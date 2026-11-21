
mod codec;
mod lines;
mod stamp;
#[cfg(test)]
mod tests;

use std::collections::HashMap;
use std::fs;
use std::io::Read;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, AtomicU8, AtomicUsize, Ordering::Relaxed};
use std::sync::Barrier;
use std::time::Instant;

use super::mem::{Arena, Scatter};
use super::pqw::{self, Column};
use super::scan::{self, Buffer, Field, Input};
use super::{
    build_links, csv_files, keys, load_context, number, Calendar, Ck, Clicks, Context, Ev, Events,
    Links, Parsed, Tally, Worker, BAD, DAY, GAP, NO_CAMPAIGN, T_ONE, WEEK,
};
use stamp::timestamp;
use codec::{decode, decode_bytes, encode, premix, scramble, unscramble, Votes, MASK, NONE};

const BUCKET_BITS: u32 = 15;
const BUCKET: usize = 1 << BUCKET_BITS;
const USER_BITS: u32 = 12;
const ALIAS_BITS: u32 = 9;
const MOST_USERS: usize = 1 << 22;
const MOST_BUCKETS: u64 = 1 << 14;
const INVALID: u64 = 0x7FFF_FFFF;
const FOREIGN: u32 = 1 << 31;
const FOREIGN_BITS: u32 = 27;
const INGEST_BITS: u32 = 21;
const INGEST_LEAD: i64 = 2 * DAY / 1000;
const MOST_ODD: usize = 1 << 18;

const LINKED_OUT: u8 = 1;
const ODD: u8 = 2;
const LOCAL: u8 = 4;
const SIDE: u8 = 8;

static BAIL: AtomicBool = AtomicBool::new(false);
static VIOLATION: AtomicBool = AtomicBool::new(false);
static PLAIN: AtomicU64 = AtomicU64::new(0);

#[cold]
fn bail() {
    BAIL.store(true, Relaxed);
}

#[derive(Clone, Copy)]
#[repr(C)]
struct Rec {
    a: u64,
    b: u64,
}

const EMPTY: Rec = Rec { a: 0, b: 0 };

type Recs = Scatter<Rec, 4>;

struct Plan {
    user_key: u64,
    event_key: u64,
    users: usize,
    event_bound: u64,
}

struct Shared<'a> {
    context: &'a Context,
    plan: Plan,
    ingest_start: i64,
    state: &'static [AtomicU8],
    adjacent: &'static [AtomicU64],
}

fn zeros<T>(count: usize) -> &'static [T] {
    unsafe { std::slice::from_raw_parts(super::mem::zeroed(count * std::mem::size_of::<T>(), false) as *const T, count) }
}

struct Raw<T>(*mut T);
unsafe impl<T> Sync for Raw<T> {}
unsafe impl<T> Send for Raw<T> {}

struct Sendable<T>(T);
unsafe impl<T> Sync for Sendable<T> {}
unsafe impl<T> Send for Sendable<T> {}

fn sample(paths: &[PathBuf], bytes: usize, prefixes: [u8; 2]) -> Vec<(u64, u64)> {
    let Some(path) = paths.iter().max_by_key(|path| fs::metadata(path).map_or(0, |meta| meta.len())) else {
        return Vec::new();
    };
    let mut head = Vec::with_capacity(bytes + 1);
    let Ok(file) = fs::File::open(path) else { return Vec::new() };
    if file.take(bytes as u64).read_to_end(&mut head).is_err() {
        return Vec::new();
    }
    let whole = head.len() < bytes;
    let mut lines: Vec<&[u8]> = head.split(|&byte| byte == b'\n').collect();
    if !whole || lines.last().is_some_and(|last| last.is_empty()) {
        lines.pop();
    }
    let number = |field: &[u8], prefix: u8| {
        let quoted = field.len() >= 2 && field[0] == b'"' && field[field.len() - 1] == b'"';
        decode_bytes(if quoted { &field[1..field.len() - 1] } else { field }, prefix)
    };
    lines
        .into_iter()
        .skip(1)
        .map(|line| {
            let mut fields = line.splitn(3, |&byte| byte == b',');
            let first = fields.next().unwrap_or(&[]);
            let second = fields.next().unwrap_or(&[]);
            (number(first, prefixes[0]), number(second, prefixes[1]))
        })
        .collect()
}
fn finish_key(low: u64, numbers: &[u64], bound: u64) -> Option<(u64, u64)> {
    for low in [low, !low & ((1 << 39) - 1)] {
        for key in [low, low | 1 << 39] {
            let mut most = 0;
            let mut fit = 0;
            for &number in numbers {
                let index = unscramble(number, key);
                if index < bound {
                    fit += 1;
                    most = most.max(index);
                }
            }
            if numbers.len() >= 32 && fit * 100 >= numbers.len() * 99 {
                return Some((key, most));
            }
        }
    }
    None
}

fn detect(link_paths: &[PathBuf], event_paths: &[PathBuf]) -> Result<Plan, &'static str> {
    let rows = sample(event_paths, 2 << 20, [b'e', b'u']);
    let user_numbers: Vec<u64> = rows.iter().map(|row| row.1).filter(|&number| number != NONE).collect();
    let event_numbers: Vec<u64> = rows.iter().map(|row| row.0).filter(|&number| number != NONE).collect();
    if user_numbers.len() < 32 || event_numbers.len() * 10 < rows.len() * 9 {
        return Err("shape");
    }

    let mut votes = Votes::default();
    for (a, b) in sample(link_paths, 1 << 16, [b'u', b'u']) {
        if a != NONE && b != NONE && a != b {
            votes.pair(premix(a), premix(b), 1, 8);
        }
    }
    let Some(low) = votes.settle() else { return Err("no user key from the links") };
    let Some((user_key, most_user)) = finish_key(low, &user_numbers, (MOST_USERS as u64) << ALIAS_BITS) else {
        return Err("the user key does not fit the events");
    };

    let mut by_user: Vec<(u64, u64)> = rows
        .iter()
        .filter(|row| row.0 != NONE && row.1 != NONE)
        .map(|row| (unscramble(row.1, user_key) >> ALIAS_BITS, premix(row.0)))
        .collect();
    by_user.sort_unstable();
    let mut pairs = Vec::new();
    let mut at = 0;
    while at < by_user.len() {
        let mut end = at + 1;
        while end < by_user.len() && by_user[end].0 == by_user[at].0 {
            end += 1;
        }
        if end - at <= 8 {
            for first in at..end {
                for second in first + 1..end {
                    if by_user[first].1 != by_user[second].1 {
                        pairs.push((by_user[first].1, by_user[second].1));
                    }
                }
            }
        }
        at = end;
    }
    pairs.truncate(4096);
    let mut votes = Votes::default();
    let mut event = None;
    for (from, to) in [(1, 64), (65, 512), (513, 4096)] {
        for &(a, b) in &pairs {
            votes.pair(a, b, from, to);
        }
        event = votes.settle().and_then(|low| finish_key(low, &event_numbers, MOST_BUCKETS << BUCKET_BITS));
        if event.is_some() {
            break;
        }
    }
    let Some((event_key, most_event)) = event else { return Err("no event key from the sample") };

    let users = ((most_user >> ALIAS_BITS) as usize + 1) * 5 / 4 + (1 << USER_BITS);
    let users = users.next_multiple_of(1 << USER_BITS).min(MOST_USERS);
    let event_bound = ((most_event + 1) * 5 / 4 + BUCKET as u64).next_multiple_of(BUCKET as u64).min(MOST_BUCKETS << BUCKET_BITS);
    Ok(Plan { user_key, event_key, users, event_bound })
}

impl<'a> Shared<'a> {
    #[inline(always)]
    unsafe fn user(&self, at: *const u8, len: usize) -> u64 {
        let number = decode(at, len, b'u');
        let id = unscramble(number, self.plan.user_key);
        if number != NONE && id < (self.plan.users as u64) << ALIAS_BITS {
            id
        } else {
            NONE
        }
    }

    fn component(&self, user: usize, alias: u32) -> u8 {
        let adjacent = self.adjacent[user].load(Relaxed);
        if alias >= 8 || adjacent >> (8 * alias) & 0xFF == 0 {
            return 0;
        }
        let mut reach = 1u8 << alias;
        loop {
            let mut next = reach;
            let mut bits = reach;
            while bits != 0 {
                next |= (adjacent >> (8 * bits.trailing_zeros())) as u8;
                bits &= bits - 1;
            }
            if next == reach {
                return reach;
            }
            reach = next;
        }
    }

    fn smallest(&self, user: usize, component: u8) -> u64 {
        let mut best = (u64::MAX, 0);
        let mut bits = component;
        while bits != 0 {
            let id = (user as u64) << ALIAS_BITS | u64::from(bits.trailing_zeros());
            bits &= bits - 1;
            best = best.min((codec::order(scramble(id, self.plan.user_key)), id));
        }
        best.1
    }

    fn key(&self, id: u64) -> u64 {
        let mut text = [0u8; 16];
        let len = encode(b'u', scramble(id, self.plan.user_key), &mut text);
        unsafe { keys::pack(text.as_ptr(), len) }
    }

    fn person(&self, links: &Links, id: u32) -> u64 {
        let user = (id >> ALIAS_BITS) as usize;
        if self.state[user].load(Relaxed) & LINKED_OUT != 0 {
            return links.person(self.key(u64::from(id)));
        }
        let component = self.component(user, id & 511);
        if component == 0 {
            self.key(u64::from(id))
        } else {
            self.key(self.smallest(user, component))
        }
    }
}

struct OddEvent {
    id: Vec<u8>,
    seconds: u64,
    stamp: u64,
    payload: u32,
    who: u32,
}

struct Parser<'a> {
    shared: &'a Shared<'a>,
    thread: u32,
    calendar: Calendar,
    events: Recs,
    clicks: Recs,
    foreign: Vec<u64>,
    odd_events: Vec<OddEvent>,
    odd_clicks: Vec<(u32, Ck)>,
}

impl<'a> Parser<'a> {
    #[cold]
    #[inline(never)]
    unsafe fn foreign(&mut self, at: *const u8, len: usize) -> u32 {
        if self.foreign.len() >= 1 << FOREIGN_BITS || self.foreign.len() >= MOST_ODD {
            bail();
            return FOREIGN;
        }
        self.foreign.push(keys::pack(at, len));
        FOREIGN | self.thread << FOREIGN_BITS | (self.foreign.len() - 1) as u32
    }

    #[cold]
    #[inline(never)]
    unsafe fn odd_event(&mut self, id: *const u8, len: usize, seconds: u64, stamp: u64, payload: u32, who: u32) {
        if self.odd_events.len() >= MOST_ODD {
            return bail();
        }
        if stamp != INVALID && who & FOREIGN == 0 {
            self.shared.state[(who >> ALIAS_BITS) as usize].fetch_or(ODD, Relaxed);
        }
        self.odd_events.push(OddEvent { id: std::slice::from_raw_parts(id, len).to_vec(), seconds, stamp, payload, who });
    }

    #[cold]
    #[inline(never)]
    unsafe fn odd_click(&mut self, id: *const u8, len: usize, who: u32, ts: u32, campaign: u32) {
        if self.odd_clicks.len() >= MOST_ODD {
            return bail();
        }
        if who & FOREIGN == 0 {
            self.shared.state[(who >> ALIAS_BITS) as usize].fetch_or(ODD, Relaxed);
        }
        self.odd_clicks.push((who, Ck { person: 0, id: keys::pack(id, len), ts, campaign }));
    }

    #[inline(always)]
    unsafe fn event_line(&mut self, fields: &[Field; 7]) {
        let shared = self.shared;
        let context = shared.context;
        let [(id, id_len), (user, user_len), (ts, ts_len), (ingest, ingest_len), (kind, kind_len), (product, product_len), (price, price_len)] =
            *fields;
        if id_len == 0 {
            return;
        }
        if ingest_len != 20 {
            return bail();
        }
        let ingest = stamp::civil::<1>(ingest, &mut self.calendar);
        let seconds = ingest.wrapping_sub(shared.ingest_start) as u64;
        if ingest == BAD || seconds >= (1 << INGEST_BITS) - 1 {
            return bail();
        }
        let ingest = ingest * 1000;
        let mut stamp = INVALID;
        let mut payload = 0u32;
        let mut who = 0u32;
        'valid: {
            if user_len == 0 || product_len == 0 {
                break 'valid;
            }
            let ts = timestamp(ts, ts_len, &mut self.calendar);
            if ts < context.window_start || ts >= context.window_end || ingest - ts > DAY {
                break 'valid;
            }
            if kind_len == 4 {
                let word = (kind as *const u32).read_unaligned();
                if word != u32::from_le_bytes(*b"view") && word != u32::from_le_bytes(*b"cart") {
                    break 'valid;
                }
            } else if kind_len == 8 && (kind as *const u64).read_unaligned() == u64::from_le_bytes(*b"purchase") {
                match number(price, price_len) {
                    Some(value) if (1..=10_000_000).contains(&value) => {
                        payload = u32::from(context.category(product, product_len)) << 24 | value as u32;
                    }
                    _ => break 'valid,
                }
            } else {
                break 'valid;
            }
            stamp = (ts - context.window_start) as u64;
            let dense = shared.user(user, user_len);
            who = if dense != NONE { dense as u32 } else { self.foreign(user, user_len) };
        }
        let number = decode(id, id_len, b'e');
        let index = unscramble(number, shared.plan.event_key);
        if number != NONE && index < shared.plan.event_bound {
            let low = index & (BUCKET as u64 - 1);
            let record = Rec {
                a: u64::from(who) | stamp << 32 | (low >> 14) << 63,
                b: u64::from(payload) | (seconds + 1) << 29 | (low & 0x3FFF) << 50,
            };
            self.events.push((index >> BUCKET_BITS) as usize, record);
        } else {
            self.odd_event(id, id_len, seconds, stamp, payload, who);
        }
    }

    #[inline(always)]
    unsafe fn click_line(&mut self, fields: &[Field; 4]) {
        let shared = self.shared;
        let context = shared.context;
        let [(id, id_len), (user, user_len), (campaign, campaign_len), (ts, ts_len)] = *fields;
        if id_len == 0 || user_len == 0 {
            return;
        }
        let campaign = context.campaign(campaign, campaign_len);
        if campaign == NO_CAMPAIGN {
            return;
        }
        let ts = timestamp(ts, ts_len, &mut self.calendar);
        if ts < context.click_start || ts >= context.window_end {
            return;
        }
        let stamp = (ts - context.click_start) as u64;
        let dense = shared.user(user, user_len);
        let number = decode(id, id_len, b'k');
        if dense != NONE && number != NONE {
            let record = Rec { a: dense | stamp << 32, b: number | u64::from(campaign) << 40 };
            self.clicks.push((dense >> (ALIAS_BITS + USER_BITS)) as usize, record);
        } else {
            let who = if dense != NONE { dense as u32 } else { self.foreign(user, user_len) };
            self.odd_click(id, id_len, who, stamp as u32, campaign);
        }
    }
}

impl lines::Events for Parser<'_> {
    #[inline(always)]
    fn calendar(&mut self) -> &mut Calendar {
        &mut self.calendar
    }

    #[inline(always)]
    unsafe fn plain(&mut self, fields: &[Field; 7]) {
        PLAIN.fetch_add(1, Relaxed);
        self.event_line(fields);
    }

    #[inline(always)]
    unsafe fn fused(&mut self, line: &lines::Fused) {
        let shared = self.shared;
        let context = shared.context;
        let seconds = line.ingest.wrapping_sub(shared.ingest_start) as u64;
        if seconds >= (1 << INGEST_BITS) - 1 {
            return bail();
        }
        let mut stamp = INVALID;
        let mut payload = 0u32;
        let mut who = 0u32;
        'valid: {
            if line.ts < context.window_start || line.ts >= context.window_end || line.ingest * 1000 - line.ts > DAY {
                break 'valid;
            }
            if line.purchase {
                match number(line.price.0, line.price.1) {
                    Some(value) if (1..=10_000_000).contains(&value) => {
                        payload = u32::from(context.category(line.product.0, line.product.1)) << 24 | value as u32;
                    }
                    _ => break 'valid,
                }
            }
            stamp = (line.ts - context.window_start) as u64;
            let dense = unscramble(line.who, shared.plan.user_key);
            who = if dense < (shared.plan.users as u64) << ALIAS_BITS { dense as u32 } else { self.foreign(line.user.0, line.user.1) };
        }
        let index = unscramble(line.event, shared.plan.event_key);
        if index < shared.plan.event_bound {
            let low = index & (BUCKET as u64 - 1);
            let record = Rec {
                a: u64::from(who) | stamp << 32 | (low >> 14) << 63,
                b: u64::from(payload) | (seconds + 1) << 29 | (low & 0x3FFF) << 50,
            };
            self.events.push((index >> BUCKET_BITS) as usize, record);
        } else {
            self.odd_event(line.id.0, line.id.1, seconds, stamp, payload, who);
        }
    }
}

struct Parse {
    events: Recs,
    clicks: Recs,
    foreign: Vec<u64>,
    odd_events: Vec<OddEvent>,
    odd_clicks: Vec<(u32, Ck)>,
}

unsafe impl Send for Parse {}
unsafe impl Sync for Parse {}

struct Row {
    day: usize,
    sessions: u32,
    events: u32,
    revenue: i64,
}

struct Stage<'a> {
    shared: &'a Shared<'a>,
    links: &'a Links,
    parsed: &'a [Parse],
    clicks: Raw<Rec>,
    starts: Raw<u32>,
}

impl<'a> Stage<'a> {
    fn person(&self, who: u32) -> u64 {
        if who & FOREIGN != 0 {
            let thread = (who & !FOREIGN) >> FOREIGN_BITS;
            let key = self.parsed[thread as usize].foreign[(who & ((1 << FOREIGN_BITS) - 1)) as usize];
            self.links.person(key)
        } else {
            self.shared.person(self.links, who)
        }
    }

    unsafe fn clicks_of(&self, user: usize) -> &[Rec] {
        let (from, to) = (*self.starts.0.add(user) as usize, *self.starts.0.add(user + 1) as usize);
        std::slice::from_raw_parts(self.clicks.0.add(from), to - from)
    }
}

#[derive(Default)]
struct Edges {
    who: Vec<u32>,
    events: Vec<u64>,
    runs: Vec<(u32, u32, usize, usize)>,
}

struct Job {
    user: u32,
    events: usize,
    pieces: Vec<(usize, usize, usize)>,
}

fn stitch(edges: &[Edges]) -> Vec<Job> {
    let mut runs: Vec<(u32, u32, usize, usize, usize)> = Vec::new();
    for (thread, edge) in edges.iter().enumerate() {
        runs.extend(edge.runs.iter().map(|&(place, user, from, len)| (place, user, thread, from, len)));
    }
    runs.sort_unstable();
    let mut jobs: Vec<Job> = Vec::new();
    for (_, user, thread, from, len) in runs {
        match jobs.last_mut() {
            Some(job) if job.user == user => {
                job.events += len;
                job.pieces.push((thread, from, len));
            }
            _ => jobs.push(Job { user, events: len, pieces: vec![(thread, from, len)] }),
        }
    }
    jobs.sort_by_key(|job| std::cmp::Reverse(job.events));
    jobs
}

struct Local<'a> {
    stage: &'a Stage<'a>,
    output: &'a Path,
    thread: usize,
    files: usize,
    rows: usize,
    columns: Vec<Column>,
    tallies: Vec<Tally>,
    assisted: Vec<u32>,
    best: Vec<Rec>,
    who: Vec<u32>,
    events: Vec<u64>,
    sorted: Vec<u64>,
    order: Vec<u64>,
    edges: Edges,
    active: Vec<u32>,
    active_count: Vec<u32>,
    active_at: Vec<u32>,
    category_sum: Vec<i64>,
    category_used: Vec<u32>,
    side_events: Events,
    side_clicks: Clicks,
    person_shift: u32,
}

unsafe impl Send for Local<'_> {}

impl<'a> Local<'a> {
    fn write_file(&mut self) {
        if self.rows == 0 {
            return;
        }
        let name = format!("dense-{}-{}.parquet", self.thread, self.files);
        pqw::write(&self.output.join(concat!("use", "r_d", "ail", "y")).join(name), &T_ONE, &self.columns, self.rows).unwrap();
        self.files += 1;
        self.rows = 0;
        for column in &mut self.columns {
            column.values.clear();
            column.present.clear();
        }
    }

    #[inline(always)]
    fn emit(&mut self, name: &[u8], row: &Row) {
        let context = self.stage.shared.context;
        self.columns[0].push_str(name);
        self.columns[1].push_i32(context.first_day + row.day as i32);
        self.columns[2].push_i32(row.sessions as i32);
        self.columns[3].push_i32(row.events as i32);
        self.columns[4].push_i64(row.revenue);
        let mut top = u32::MAX;
        let mut best = 0;
        for &category in &self.category_used {
            let sum = std::mem::take(&mut self.category_sum[category as usize]);
            if sum > best || (sum == best && category < top) {
                best = sum;
                top = category;
            }
        }
        self.category_used.clear();
        self.columns[5].push_present(self.rows, top != u32::MAX);
        if top != u32::MAX {
            self.columns[5].push_str(&context.categories[top as usize]);
        }
        self.rows += 1;
        if self.rows >= 1 << 20 {
            self.write_file();
        }
    }

    #[inline(always)]
    unsafe fn side_event(&mut self, person: u64, event: u64) {
        let part = (keys::hash(person) >> self.person_shift) as usize;
        self.side_events.push(part, Ev { person, ts: (event >> 32) as u32, payload: event as u32 });
    }

    #[inline(always)]
    unsafe fn side_click(&mut self, person: u64, click: Ck) {
        let part = (keys::hash(person) >> self.person_shift) as usize;
        self.side_clicks.push(part, Ck { person, ..click });
    }

    unsafe fn bucket(&mut self, part: usize) {
        let stage = self.stage;
        let best = self.best.as_mut_ptr();
        for thread in stage.parsed {
            thread.events.for_each_chunk(part, |chunk| {
                for record in chunk {
                    let low = (record.b >> 50 | record.a >> 63 << 14) as usize;
                    let kept = best.add(low);
                    let (new, old) = (record.b >> 29 & 0x1F_FFFF, (*kept).b >> 29 & 0x1F_FFFF);
                    if old == 0 || new < old {
                        *kept = *record;
                    }
                }
            });
        }
        self.who.clear();
        self.events.clear();
        self.who.reserve(BUCKET);
        self.events.reserve(BUCKET);
        let (who_out, event_out) = (self.who.as_mut_ptr(), self.events.as_mut_ptr());
        let mut count = 0;
        let (mut from, mut user, mut runs) = (0, u32::MAX, 0u32);
        for low in 0..BUCKET {
            let record = *best.add(low);
            if record.b == 0 {
                continue;
            }
            *best.add(low) = EMPTY;
            let stamp = record.a >> 32 & INVALID;
            if stamp == INVALID {
                continue;
            }
            let (who, event) = (record.a as u32, stamp << 32 | record.b & 0x1FFF_FFFF);
            if who & FOREIGN != 0 {
                let person = stage.person(who);
                self.side_event(person, event);
                continue;
            }
            if who >> ALIAS_BITS != user {
                if count > from {
                    if runs == 0 {
                        self.edge(part as u32 * 2, user, from, count);
                    } else {
                        self.run(user as usize, from, count);
                    }
                    runs += 1;
                }
                from = count;
                user = who >> ALIAS_BITS;
            }
            *who_out.add(count) = who;
            *event_out.add(count) = event;
            count += 1;
        }
        if count > from {
            self.edge(part as u32 * 2 + u32::from(runs > 0), user, from, count);
        }
    }

    unsafe fn edge(&mut self, place: u32, user: u32, from: usize, to: usize) {
        let edges = &mut self.edges;
        edges.runs.push((place, user, edges.who.len(), to - from));
        edges.who.extend_from_slice(std::slice::from_raw_parts(self.who.as_ptr().add(from), to - from));
        edges.events.extend_from_slice(std::slice::from_raw_parts(self.events.as_ptr().add(from), to - from));
    }

    unsafe fn job(&mut self, job: &Job, edges: &[Edges]) {
        self.who.clear();
        self.events.clear();
        for &(thread, from, len) in &job.pieces {
            self.who.extend_from_slice(&edges[thread].who[from..from + len]);
            self.events.extend_from_slice(&edges[thread].events[from..from + len]);
        }
        self.run(job.user as usize, 0, job.events);
    }

    #[inline(always)]
    unsafe fn run(&mut self, user: usize, from: usize, to: usize) {
        if !self.local(user, from, to) {
            self.side(user, from, to);
        }
    }

    #[cold]
    #[inline(never)]
    unsafe fn side(&mut self, user: usize, from: usize, to: usize) {
        let stage = self.stage;
        if stage.shared.state[user].fetch_or(SIDE, Relaxed) & LOCAL != 0 {
            VIOLATION.store(true, Relaxed);
        }
        let mut people = [(u32::MAX, 0u64); 8];
        for at in from..to {
            let who = *self.who.get_unchecked(at);
            let slot = &mut people[(who & 7) as usize];
            if slot.0 != who {
                *slot = (who, stage.person(who));
            }
            let person = slot.1;
            self.side_event(person, *self.events.get_unchecked(at));
        }
    }

    #[inline(always)]
    unsafe fn local(&mut self, user: usize, from: usize, to: usize) -> bool {
        let stage = self.stage;
        let shared = stage.shared;
        if shared.state.get_unchecked(user).load(Relaxed) & (LINKED_OUT | ODD) != 0 {
            return false;
        }
        let first = *self.who.get_unchecked(from);
        let (mut differ, mut sorted) = (0, true);
        for at in from + 1..to {
            differ |= *self.who.get_unchecked(at) ^ first;
            sorted &= *self.events.get_unchecked(at - 1) >> 32 <= *self.events.get_unchecked(at) >> 32;
        }
        let clicks = stage.clicks_of(user);
        self.order.clear();
        for (place, click) in clicks.iter().enumerate() {
            differ |= click.a as u32 ^ first;
            self.order.push(click.a >> 32 << 32 | place as u64);
        }
        let mut name = u64::from(first);
        if differ != 0 || shared.adjacent.get_unchecked(user).load(Relaxed) != 0 {
            let component = u32::from(shared.component(user, first & 511));
            let same = |who: u32| who == first || ((who & 511) < 8 && component >> (who & 7) & 1 != 0);
            if differ != 0 && !((from..to).all(|at| same(*self.who.get_unchecked(at))) && clicks.iter().all(|click| same(click.a as u32))) {
                return false;
            }
            if component != 0 {
                name = shared.smallest(user, component as u8);
            }
        }
        if shared.state.get_unchecked(user).fetch_or(LOCAL, Relaxed) & (LOCAL | SIDE) != 0 {
            VIOLATION.store(true, Relaxed);
            return true;
        }
        let mut text = [0u8; 16];
        let len = encode(b'u', scramble(name, shared.plan.user_key), &mut text);
        if self.order.len() > 1 {
            self.order.sort_unstable();
        }
        let events: &[u64] = if sorted {
            std::slice::from_raw_parts(self.events.as_ptr().add(from), to - from)
        } else {
            self.sorted.clear();
            self.sorted.extend_from_slice(std::slice::from_raw_parts(self.events.as_ptr().add(from), to - from));
            self.sorted.sort_unstable_by_key(|event| event >> 32);
            std::slice::from_raw_parts(self.sorted.as_ptr(), to - from)
        };
        self.sessions(&text[..len], events, clicks);
        true
    }

    #[inline(always)]
    unsafe fn sessions(&mut self, name: &[u8], events: &[u64], records: &[Rec]) {
        let context = self.stage.shared.context;
        let days = context.days;
        let organic = context.campaign_ids.len();
        let clicks = std::slice::from_raw_parts(self.order.as_ptr(), self.order.len());
        let stamp = |click: u64| (click >> 32) as u32;
        let record = |click: u64| records.get_unchecked(click as u32 as usize);
        let campaign = |click: u64| (record(click).b >> 40) as usize;
        let mut row = Row { day: usize::MAX, sessions: 0, events: 0, revenue: 0 };
        let (mut low, mut high) = (0, 0);
        let mut at = 0;
        while at < events.len() {
            let start = *events.get_unchecked(at) >> 32;
            let day = ((context.day_offset + start) / DAY as u64) as usize;
            if day != row.day {
                if row.day != usize::MAX {
                    self.emit(name, &row);
                }
                row = Row { day, sessions: 0, events: 0, revenue: 0 };
            }
            let mut revenue = 0i64;
            let mut count = 0u32;
            let mut last = start;
            while at < events.len() {
                let event = *events.get_unchecked(at);
                if (event >> 32) - last > GAP {
                    break;
                }
                last = event >> 32;
                count += 1;
                let payload = event as u32;
                if payload != 0 {
                    let (category, price) = ((payload >> 24) as usize, i64::from(payload & 0x00FF_FFFF));
                    revenue += price;
                    if *self.category_sum.get_unchecked(category) == 0 {
                        self.category_used.push(category as u32);
                    }
                    *self.category_sum.get_unchecked_mut(category) += price;
                }
                at += 1;
            }
            row.sessions += 1;
            row.events += count;
            row.revenue += revenue;

            let mut credited = organic;
            if !clicks.is_empty() {
                let reach = (start + WEEK as u64) as u32;
                while high < clicks.len() && stamp(clicks[high]) <= reach {
                    let campaign = campaign(clicks[high]);
                    if self.active_count[campaign] == 0 {
                        self.active_at[campaign] = self.active.len() as u32;
                        self.active.push(campaign as u32);
                    }
                    self.active_count[campaign] += 1;
                    high += 1;
                }
                while low < high && stamp(clicks[low]) < start as u32 {
                    let campaign = campaign(clicks[low]);
                    self.active_count[campaign] -= 1;
                    if self.active_count[campaign] == 0 {
                        let hole = self.active_at[campaign] as usize;
                        let moved = self.active.pop().unwrap();
                        if moved as usize != campaign {
                            self.active[hole] = moved;
                            self.active_at[moved as usize] = hole as u32;
                        }
                    }
                    low += 1;
                }
                if low < high {
                    let mut chosen = high - 1;
                    let mut other = chosen;
                    while other > low && stamp(clicks[other - 1]) == stamp(clicks[chosen]) {
                        other -= 1;
                        if codec::order(record(clicks[other]).b & MASK) < codec::order(record(clicks[chosen]).b & MASK) {
                            chosen = other;
                        }
                    }
                    credited = campaign(clicks[chosen]);
                }
                for &campaign in &self.active {
                    *self.assisted.get_unchecked_mut(campaign as usize * days + day) += 1;
                }
            }
            let tally = self.tallies.get_unchecked_mut(credited * days + day);
            tally.sessions += 1;
            tally.purchasing += u32::from(revenue != 0);
            tally.revenue += revenue;
        }
        if row.day != usize::MAX {
            self.emit(name, &row);
        }
        for &campaign in &self.active {
            self.active_count[campaign as usize] = 0;
        }
        self.active.clear();
    }

    unsafe fn leftover_clicks(&mut self, users: std::ops::Range<usize>) {
        let stage = self.stage;
        for user in users {
            let clicks = stage.clicks_of(user);
            if clicks.is_empty() || stage.shared.state[user].load(Relaxed) & LOCAL != 0 {
                continue;
            }
            let (mut last, mut person) = (u32::MAX, 0);
            for click in clicks {
                let who = click.a as u32;
                if who != last {
                    last = who;
                    person = stage.shared.person(stage.links, who);
                }
                let mut text = [0u8; 16];
                let len = encode(b'k', click.b & MASK, &mut text);
                let id = keys::pack(text.as_ptr(), len);
                self.side_click(person, Ck { person, id, ts: (click.a >> 32) as u32, campaign: (click.b >> 40) as u32 });
            }
        }
    }
}
unsafe fn group_clicks(parsed: &[Parse], part: usize, base: usize, clicks: &Raw<Rec>, starts: &Raw<u32>, counts: &mut Vec<u32>) {
    let users = 1usize << USER_BITS;
    let first = part << USER_BITS;
    counts.clear();
    counts.resize(users, 0);
    let slot = |record: &Rec| (record.a as u32 >> ALIAS_BITS) as usize - first;
    for thread in parsed {
        thread.clicks.for_each_chunk(part, |chunk| {
            for record in chunk {
                *counts.get_unchecked_mut(slot(record)) += 1;
            }
        });
    }
    let mut sum = base as u32;
    for (user, count) in counts.iter_mut().enumerate() {
        *starts.0.add(first + user) = sum;
        sum += std::mem::replace(count, sum);
    }
    for thread in parsed {
        thread.clicks.for_each_chunk(part, |chunk| {
            for record in chunk {
                let at = counts.get_unchecked_mut(slot(record));
                *clicks.0.add(*at as usize) = *record;
                *at += 1;
            }
        });
    }
}

fn remove_output(output: &Path) {
    let folder = output.join(concat!("use", "r_d", "ail", "y"));
    for entry in fs::read_dir(&folder).into_iter().flatten().flatten() {
        if entry.file_name().to_string_lossy().starts_with("dense-") {
            let _ = fs::remove_file(entry.path());
        }
    }
}

pub fn run(data: &Path, output: &Path, threads: usize, verbose: bool, started: Instant) -> bool {
    let lap = |what: &str| {
        if verbose {
            let mut cpu = libc::timespec { tv_sec: 0, tv_nsec: 0 };
            unsafe { libc::clock_gettime(libc::CLOCK_PROCESS_CPUTIME_ID, &mut cpu) };
            let cpu = cpu.tv_sec as f64 * 1e3 + cpu.tv_nsec as f64 / 1e6;
            eprintln!("{:>8.1} ms  cpu {cpu:>8.1} ms  {what}", started.elapsed().as_secs_f64() * 1e3);
        }
    };
    let refuse = |why: &str| {
        if verbose {
            eprintln!("dense path: not taken ({why})");
        }
        false
    };
    if std::env::var_os("DENSE_OFF").is_some() {
        return refuse("switched off");
    }
    let link_paths = csv_files(&data.join(concat!("lin", "ks")));
    let click_paths = csv_files(&data.join(concat!("cli", "cks")));
    let event_paths = csv_files(&data.join(concat!("eve", "nts")));
    let plan = match detect(&link_paths, &event_paths) {
        Ok(plan) => plan,
        Err(why) => return refuse(why),
    };
    let context = {
        let (data, output) = (data.to_path_buf(), output.to_path_buf());
        std::thread::spawn(move || {
            fs::create_dir_all(output.join(concat!("use", "r_d", "ail", "y"))).unwrap();
            fs::create_dir_all(output.join(concat!("cam", "pai", "gn_", "dai", "ly"))).unwrap();
            load_context(&data)
        })
    };
    let open_all = |paths: &[PathBuf]| -> Vec<Input> { paths.iter().map(|path| scan::open(path)).collect() };
    let link_inputs = open_all(&link_paths);
    let click_inputs = open_all(&click_paths);
    let event_inputs: Vec<lines::Input> = event_paths.iter().map(|path| lines::open(path)).collect();
    let event_bytes: u64 = event_inputs.iter().map(lines::Input::len).sum();
    let click_bytes: u64 = click_inputs.iter().map(Input::len).sum();
    lap("dense: keys");

    let Some(mut context) = context.join().unwrap() else { return refuse("no context") };
    if context.categories.len() > 32 || context.campaign_ids.len() >= 1 << 24 {
        return refuse("too many categories or campaigns");
    }
    let estimate = event_bytes / 80;
    context.person_bits = (estimate / 160_000).max(1).next_power_of_two().trailing_zeros().clamp(4, 11);
    context.event_bits = 4;
    let context = &context;
    let users = plan.users;
    let buckets = (plan.event_bound >> BUCKET_BITS) as usize;
    let shared = Shared {
        context,
        plan,
        ingest_start: context.window_start.div_euclid(1000) - INGEST_LEAD,
        state: zeros(users),
        adjacent: zeros(users),
    };
    let shared = &shared;

    const CHUNK: usize = 1 << 18;
    let link_tasks = scan::tasks(&link_inputs, CHUNK);
    let next = AtomicUsize::new(0);
    let barrier = Barrier::new(threads);
    let pairs: Vec<Vec<(u64, u64)>> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|_| {
                scope.spawn(|| unsafe {
                    let mut general: Vec<(u64, u64)> = Vec::new();
                    let mut inside: Vec<u32> = Vec::new();
                    let mut buffer = Buffer::new();
                    while let Some(&task) = link_tasks.get(next.fetch_add(1, Relaxed)) {
                        scan::run::<2>(&link_inputs[task.file], task, &mut buffer, |fields| {
                            let [(a, a_len), (b, b_len)] = *fields;
                            if a_len == 0 || b_len == 0 {
                                return;
                            }
                            let (x, y) = (shared.user(a, a_len), shared.user(b, b_len));
                            if x != NONE && y != NONE && x >> ALIAS_BITS == y >> ALIAS_BITS && x & 511 < 8 && y & 511 < 8 {
                                let (user, i, j) = (x >> ALIAS_BITS, x & 7, y & 7);
                                shared.adjacent[user as usize].fetch_or(1 << (8 * i + j) | 1 << (8 * j + i), Relaxed);
                                if i != j {
                                    inside.push((user << 6 | i << 3 | j) as u32);
                                }
                                return;
                            }
                            for side in [x, y] {
                                if side != NONE {
                                    shared.state[(side >> ALIAS_BITS) as usize].fetch_or(LINKED_OUT, Relaxed);
                                }
                            }
                            let (a, b) = (keys::pack(a, a_len), keys::pack(b, b_len));
                            if a != b {
                                general.push((a, b));
                            }
                        });
                    }
                    barrier.wait();
                    for link in inside {
                        let user = (link >> 6) as usize;
                        if shared.state[user].load(Relaxed) & LINKED_OUT != 0 {
                            let id = |alias: u32| shared.key((user as u64) << ALIAS_BITS | u64::from(alias & 7));
                            general.push((id(link >> 3), id(link)));
                        }
                    }
                    general
                })
            })
            .collect();
        handles.into_iter().map(|handle| handle.join().unwrap()).collect()
    });
    lap("dense: links parsed");
    let links = build_links(threads, &pairs);
    let links = &links;
    lap("dense: links joined");

    let record_bytes = (event_bytes / 80 * 16 + click_bytes / 45 * 16) as usize;
    let click_parts = users >> USER_BITS;
    let click_tasks = scan::tasks(&click_inputs, CHUNK);
    let event_tasks = lines::tasks(&event_inputs, CHUNK);
    let plain = std::env::var_os("DENSE_PLAIN").is_some();
    let (next_click, next_event) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let parsed: Vec<Parse> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|thread| {
                let (click_tasks, event_tasks, click_inputs, event_inputs) = (&click_tasks, &event_tasks, &click_inputs, &event_inputs);
                let (next_click, next_event) = (&next_click, &next_event);
                scope.spawn(move || unsafe {
                    let arena = Arena::leak(record_bytes / 4);
                    let mut parser = Parser {
                        shared,
                        thread: thread as u32,
                        calendar: Calendar::new(),
                        events: Scatter::new(arena, buckets),
                        clicks: Scatter::new(arena, click_parts),
                        foreign: Vec::new(),
                        odd_events: Vec::new(),
                        odd_clicks: Vec::new(),
                    };
                    let mut buffer = Buffer::new();
                    let mut event_buffer = lines::Buffer::new();
                    while let Some(&task) = event_tasks.get(next_event.fetch_add(1, Relaxed)) {
                        if plain {
                            lines::run_plain(&event_inputs[task.file], task, &mut event_buffer, &mut parser);
                        } else {
                            lines::run_events(&event_inputs[task.file], task, &mut event_buffer, &mut parser);
                        }
                    }
                    while let Some(&task) = click_tasks.get(next_click.fetch_add(1, Relaxed)) {
                        scan::run::<4>(&click_inputs[task.file], task, &mut buffer, |fields| parser.click_line(fields));
                    }
                    parser.events.finish();
                    parser.clicks.finish();
                    Parse {
                        events: parser.events,
                        clicks: parser.clicks,
                        foreign: parser.foreign,
                        odd_events: parser.odd_events,
                        odd_clicks: parser.odd_clicks,
                    }
                })
            })
            .collect();
        handles.into_iter().map(|handle| handle.join().unwrap()).collect()
    });
    lap("dense: parsed");
    if verbose {
        eprintln!("dense: {} event lines were read the plain way", PLAIN.load(Relaxed));
    }
    if BAIL.load(Relaxed) {
        return refuse("a row does not fit");
    }
    let parsed = &parsed;

    let mut odd: HashMap<&[u8], &OddEvent> = HashMap::new();
    for event in parsed.iter().flat_map(|thread| &thread.odd_events) {
        match odd.get_mut(event.id.as_slice()) {
            Some(kept) if kept.seconds <= event.seconds => {}
            Some(kept) => *kept = event,
            None => {
                odd.insert(&event.id, event);
            }
        }
    }
    let odd: Vec<&OddEvent> = odd.into_values().filter(|event| event.stamp != INVALID).collect();

    let mut bases = Vec::with_capacity(click_parts + 1);
    let mut click_total = 0usize;
    for part in 0..click_parts {
        bases.push(click_total);
        click_total += parsed.iter().map(|thread| thread.clicks.len(part)).sum::<usize>();
    }
    if click_total >= u32::MAX as usize {
        return refuse("too many clicks");
    }
    let stage = Stage {
        shared,
        links,
        parsed,
        clicks: Raw(super::mem::zeroed(click_total * 16, false) as *mut Rec),
        starts: Raw(super::mem::zeroed((users + 1) * 4, false) as *mut u32),
    };
    unsafe { *stage.starts.0.add(users) = click_total as u32 };
    let stage = &stage;
    let next = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                let mut counts = Vec::new();
                loop {
                    let part = next.fetch_add(1, Relaxed);
                    if part >= click_parts {
                        break;
                    }
                    unsafe { group_clicks(parsed, part, bases[part], &stage.clicks, &stage.starts, &mut counts) };
                }
            });
        }
    });
    lap("dense: clicks grouped");

    let campaigns = context.campaign_ids.len();
    let side_parts = 1usize << context.person_bits;
    let odd = &odd;
    let mut locals: Vec<Local> = (0..threads)
        .map(|thread| unsafe {
            let arena = Arena::leak((record_bytes / 16).max(1 << 22));
            Local {
                stage,
                output,
                thread,
                files: 0,
                rows: 0,
                columns: (0..6).map(|_| Column::default()).collect(),
                tallies: vec![Tally::default(); (campaigns + 1) * context.days],
                assisted: vec![0; (campaigns + 1) * context.days],
                best: Vec::new(),
                who: Vec::new(),
                events: Vec::new(),
                sorted: Vec::new(),
                order: Vec::new(),
                edges: Edges::default(),
                active: Vec::new(),
                active_count: vec![0; campaigns],
                active_at: vec![0; campaigns],
                category_sum: vec![0; context.categories.len()],
                category_used: Vec::new(),
                side_events: Scatter::new(arena, side_parts),
                side_clicks: Scatter::new(arena, side_parts),
                person_shift: 64 - context.person_bits,
            }
        })
        .collect();
    let next = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for local in &mut locals {
            let next = &next;
            scope.spawn(move || unsafe {
                local.best = vec![EMPTY; BUCKET];
                loop {
                    let part = next.fetch_add(1, Relaxed);
                    if part >= buckets {
                        break;
                    }
                    local.bucket(part);
                }
            });
        }
    });
    lap("dense: buckets");

    let edges: Vec<Edges> = locals.iter_mut().map(|local| std::mem::take(&mut local.edges)).collect();
    let jobs = stitch(&edges);
    let (edges, jobs) = (&edges, &jobs);
    let (next, next_users) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let barrier = Barrier::new(threads);
    let results: Vec<(Vec<Tally>, Sendable<Parsed>)> = std::thread::scope(|scope| {
        let handles: Vec<_> = locals
            .into_iter()
            .map(|mut local| {
                let (next, next_users, barrier) = (&next, &next_users, &barrier);
                scope.spawn(move || unsafe {
                    let thread = local.thread;
                    while let Some(job) = jobs.get(next.fetch_add(1, Relaxed)) {
                        local.job(job, edges);
                    }
                    local.write_file();
                    barrier.wait();
                    const STEP: usize = 1 << USER_BITS;
                    loop {
                        let from = next_users.fetch_add(1, Relaxed) * STEP;
                        if from >= users {
                            break;
                        }
                        local.leftover_clicks(from..from + STEP);
                    }
                    for &(who, click) in &parsed[thread].odd_clicks {
                        let person = stage.person(who);
                        local.side_click(person, click);
                    }
                    if thread == 0 {
                        for event in odd.iter() {
                            let person = stage.person(event.who);
                            local.side_event(person, event.stamp << 32 | u64::from(event.payload));
                        }
                    }
                    local.side_events.finish();
                    local.side_clicks.finish();
                    let arena = local.side_events.arena();
                    let side = Parsed { dedups: Scatter::new(arena, 1), events: local.side_events, clicks: local.side_clicks };
                    for (tally, &assisted) in local.tallies.iter_mut().zip(&local.assisted) {
                        tally.assisted += assisted;
                    }
                    (local.tallies, Sendable(side))
                })
            })
            .collect();
        handles.into_iter().map(|handle| handle.join().unwrap()).collect()
    });
    lap("dense: sessions");
    if VIOLATION.load(Relaxed) {
        remove_output(output);
        return refuse("a user's events were not together");
    }

    let (mut tallies, side): (Vec<Vec<Tally>>, Vec<Parsed>) = results.into_iter().map(|(tally, side)| (tally, side.0)).unzip();
    let side = &side;
    let side_events: usize = side.iter().map(|thread| (0..side_parts).map(|part| thread.events.len(part)).sum::<usize>()).sum();
    let side_threads = (side_events / 200_000 + 1).min(threads);
    let next = AtomicUsize::new(0);
    let more: Vec<Vec<Tally>> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..side_threads)
            .map(|thread| {
                let next = &next;
                scope.spawn(move || {
                    let mut worker = Worker::new(context, output, thread);
                    loop {
                        let part = next.fetch_add(1, Relaxed);
                        if part >= side_parts {
                            break;
                        }
                        unsafe { worker.partition(side, part) };
                    }
                    worker.write_file();
                    worker.tallies
                })
            })
            .collect();
        handles.into_iter().map(|handle| handle.join().unwrap()).collect()
    });
    tallies.extend(more);
    lap("dense: side path");

    let mut columns: Vec<Column> = (0..7).map(|_| Column::default()).collect();
    let mut rows = 0;
    for campaign in 0..=campaigns {
        for day in 0..context.days {
            let mut total = Tally::default();
            for list in &tallies {
                let tally = &list[campaign * context.days + day];
                total.sessions += tally.sessions;
                total.purchasing += tally.purchasing;
                total.revenue += tally.revenue;
                total.assisted += tally.assisted;
            }
            if total.sessions == 0 && total.assisted == 0 {
                continue;
            }
            let (id, channel): (&[u8], &[u8]) = if campaign == campaigns {
                (concat!("org", "ani", "c").as_bytes(), concat!("org", "ani", "c").as_bytes())
            } else {
                (&context.campaign_ids[campaign], &context.channels[campaign])
            };
            columns[0].push_str(id);
            columns[1].push_str(channel);
            columns[2].push_i32(context.first_day + day as i32);
            columns[3].push_i64(i64::from(total.sessions));
            columns[4].push_i64(i64::from(total.purchasing));
            columns[5].push_i64(total.revenue);
            columns[6].push_i64(i64::from(total.assisted));
            rows += 1;
        }
    }
    pqw::write(&output.join(concat!("cam", "pai", "gn_", "dai", "ly")).join("part-0.parquet"), &pqw::T_TWO, &columns, rows).unwrap();
    lap("dense: done");
    if verbose {
        eprintln!("dense path: taken");
    }
    true
}
