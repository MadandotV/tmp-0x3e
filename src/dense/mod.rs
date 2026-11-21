
mod codec;
mod lines;
mod rows;
mod sink;
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
use super::pool;
use super::pqw::{self, Column, Mode};
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
    frame: sink::Frame,
    state: &'static [AtomicU8],
    adjacent: &'static [AtomicU64],
}

fn zeros<T>(count: usize) -> &'static [T] {
    unsafe { std::slice::from_raw_parts(super::mem::shared(count * std::mem::size_of::<T>()) as *const T, count) }
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

    let users = ((most_user >> ALIAS_BITS) as usize + 1) * 5 / 4 + (1 << 12);
    let users = users.next_multiple_of(1 << 12).min(MOST_USERS);
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
    unsafe fn plain(&mut self, fields: &[Field; 7]) {
        PLAIN.fetch_add(1, Relaxed);
        self.event_line(fields);
    }

    #[inline(always)]
    unsafe fn rows(&mut self, rows: &rows::Rows, count: usize) {
        use std::arch::x86_64::*;
        let frame = &self.shared.frame;
        let mut records = [std::mem::MaybeUninit::<Rec>::uninit(); rows::BATCH];
        let mut buckets = [std::mem::MaybeUninit::<u64>::uninit(); rows::BATCH];
        let (records, buckets) = (records.as_mut_ptr() as *mut Rec, buckets.as_mut_ptr() as *mut u64);
        let (mut left, mut bought) = (0u64, 0u64);
        let whole = count & !3;
        let mut at = 0;
        while at < whole {
            let some = frame.four(rows.ids.as_ptr().add(at), rows.times.as_ptr().add(at), records.add(at), buckets.add(at));
            left |= u64::from(some) << at;
            bought |= (_mm256_movemask_pd(_mm256_loadu_pd(rows.lines.as_ptr().add(at) as *const f64)) as u64) << at;
            at += 4;
        }
        let mut priced = bought & !left;
        while priced != 0 {
            let at = priced.trailing_zeros() as usize;
            priced &= priced - 1;
            self.price(*rows.lines.get_unchecked(at), *rows.tails.get_unchecked(at), &mut *records.add(at));
        }
        for at in 0..whole {
            self.events.push(*buckets.add(at) as usize, *records.add(at));
        }
        while left != 0 {
            PLAIN.fetch_add(1, Relaxed);
            self.again(*rows.lines.get_unchecked(left.trailing_zeros() as usize));
            left &= left - 1;
        }
        for at in whole..count {
            self.again(*rows.lines.get_unchecked(at));
        }
    }
}

impl lines::Clicks for Parser<'_> {
    #[inline(always)]
    unsafe fn plain_click(&mut self, fields: &[Field; 4]) {
        self.click_line(fields);
    }

    #[inline(always)]
    unsafe fn clicks(&mut self, rows: &[rows::Click]) {
        let shared = self.shared;
        let context = shared.context;
        let user_key = shared.plan.user_key;
        let user_bound = (shared.plan.users as u64) << ALIAS_BITS;
        let (campaigns, known) = (context.campaign_by_number.as_ptr(), context.campaign_by_number.len() as u64);
        for row in rows {
            let dense = unscramble(row.who, user_key);
            if (row.campaign >= known) | (dense >= user_bound) {
                self.click_again(row.line);
                continue;
            }
            let campaign = *campaigns.add(row.campaign as usize);
            if (campaign == NO_CAMPAIGN) | (row.ts < context.click_start) | (row.ts >= context.window_end) {
                continue;
            }
            let stamp = (row.ts - context.click_start) as u64;
            let record = Rec { a: dense | stamp << 32, b: row.id | u64::from(campaign) << 40 };
            self.clicks.push((dense >> (ALIAS_BITS + USER_BITS)) as usize, record);
        }
    }
}

impl Parser<'_> {
    #[cold]
    #[inline(never)]
    unsafe fn click_again(&mut self, line: *const u8) {
        if let (_, Some(fields)) = lines::split_click(line) {
            self.click_line(&fields);
        }
    }

    #[inline(never)]
    unsafe fn price(&self, line: u64, tail: u32, record: &mut Rec) {
        if !sink::stands(record) {
            return;
        }
        let line = (line & !rows::PURCHASE) as *const u8;
        let part = |shift: u32| (tail >> shift & 0xFF) as usize;
        let payload = match number(line.add(part(16)), part(24)) {
            Some(value) if (1..=10_000_000).contains(&value) => Some(u32::from(self.shared.context.category(line.add(part(0)), part(8))) << 24 | value as u32),
            _ => None,
        };
        sink::pay(record, payload);
    }

    #[cold]
    #[inline(never)]
    unsafe fn again(&mut self, line: u64) {
        if let (_, Some(fields)) = lines::split((line & !rows::PURCHASE) as *const u8) {
            self.event_line(&fields);
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
    categories: Vec<u8>,
    credited: Vec<u32>,
    bought: Vec<[i64; 2]>,
    table: Table,
    best: Vec<Rec>,
    mark: u64,
    who: Vec<u32>,
    events: Vec<u64>,
    sorted: Vec<u64>,
    assists: Vec<u32>,
    before: Vec<DayCounts>,
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

const FILE_ROWS: usize = 1 << 16;
const NO_CATEGORY: u8 = 255;

#[derive(Clone, Copy)]
#[repr(align(32))]
struct DayCounts([u16; 16]);

const PROFILE: bool = option_env!("NB_PROF").is_some();
const STEPS: [&str; 15] =
    ["dedup", "pack", "sessions", "days", "users", "credit", "purchases", "names", "rows", "file", "u:edge", "u:unsorted", "u:claim", "u:side", "u:clicks"];
static CYCLES: [AtomicU64; 15] = [const { AtomicU64::new(0) }; 15];
static COUNTS: [AtomicU64; 15] = [const { AtomicU64::new(0) }; 15];

thread_local! {
    static STEP: std::cell::Cell<[(u64, u64); 15]> = const { std::cell::Cell::new([(0, 0); 15]) };
}

#[inline(always)]
fn step(clock: &mut u64, which: usize) {
    if PROFILE {
        let now = unsafe { std::arch::x86_64::_rdtsc() };
        STEP.with(|cell| {
            let mut steps = cell.get();
            steps[which].0 += now - *clock;
            steps[which].1 += 1;
            cell.set(steps);
        });
        *clock = unsafe { std::arch::x86_64::_rdtsc() };
    }
}

fn steps_done() {
    if PROFILE {
        for (which, (cycles, count)) in STEP.get().into_iter().enumerate() {
            CYCLES[which].fetch_add(cycles, Relaxed);
            COUNTS[which].fetch_add(count, Relaxed);
        }
    }
}

const TOP: u32 = 1 << 31;
const LOW: u32 = TOP - 1;
const LOW_50: u64 = (1 << 50) - 1;
const MARKS: u64 = (1 << 14) - 2;
const UNUSED: Rec = Rec { a: 0, b: u64::MAX };

#[inline(never)]
unsafe fn keep_earliest(chunk: &[Rec], best: *mut Rec, mark: u64) {
    for record in chunk {
        let low = (record.b >> 50 | record.a >> 63 << 14) as usize;
        let kept = best.add(low);
        let new = Rec { a: record.a, b: record.b & LOW_50 | mark };
        *kept = if new.b < (*kept).b { new } else { *kept };
    }
}

static FRONT: [[u8; 16]; 16] = {
    let mut table = [[0x80u8; 16]; 16];
    let mut mask = 0;
    while mask < 16 {
        let (mut lane, mut out) = (0, 0);
        while lane < 4 {
            if mask >> lane & 1 != 0 {
                let mut byte = 0;
                while byte < 4 {
                    table[mask][out * 4 + byte] = (lane * 4 + byte) as u8;
                    byte += 1;
                }
                out += 1;
            }
            lane += 1;
        }
        mask += 1;
    }
    table
};

#[inline(never)]
unsafe fn pack(best: *const Rec, marked: u64, who: *mut u32, ts: *mut u32, slots: *mut u32, buys: *mut u8) -> (usize, bool) {
    use std::arch::x86_64::*;
    std::ptr::write_bytes(buys, 0, BUCKET / 8 + 8);
    let halves = _mm256_setr_epi32(0, 4, 2, 6, 1, 5, 3, 7);
    let mark = _mm_set1_epi32(marked as i32);
    let invalid = _mm_set1_epi32(INVALID as i32);
    let payload = _mm_set1_epi32(0x1FFF_FFFF);
    let mut slot = _mm_setr_epi32(0, 1, 2, 3);
    let four = _mm_set1_epi32(4);
    let (mut count, mut foreign) = (0usize, 0);
    for group in 0..BUCKET / 4 {
        let (even, odd) = (_mm256_loadu_si256(best.add(4 * group) as *const __m256i), _mm256_loadu_si256(best.add(4 * group + 2) as *const __m256i));
        let firsts = _mm256_permutevar8x32_epi32(_mm256_unpacklo_epi64(even, odd), halves);
        let seconds = _mm256_permutevar8x32_epi32(_mm256_unpackhi_epi64(even, odd), halves);
        let users = _mm256_castsi256_si128(firsts);
        let stamps = _mm_and_si128(_mm256_extracti128_si256(firsts, 1), invalid);
        let marks = _mm_srli_epi32(_mm256_extracti128_si256(seconds, 1), 18);
        let valid = _mm_movemask_ps(_mm_castsi128_ps(_mm_andnot_si128(_mm_cmpeq_epi32(stamps, invalid), _mm_cmpeq_epi32(marks, mark)))) as usize;
        let other = _mm_movemask_ps(_mm_castsi128_ps(users)) as usize;
        let keep = valid & !other;
        foreign |= valid & other;
        let front = _mm_loadu_si128(FRONT.as_ptr().add(keep) as *const __m128i);
        _mm_storeu_si128(who.add(count) as *mut __m128i, _mm_shuffle_epi8(users, front));
        _mm_storeu_si128(ts.add(count) as *mut __m128i, _mm_shuffle_epi8(stamps, front));
        _mm_storeu_si128(slots.add(count) as *mut __m128i, _mm_shuffle_epi8(slot, front));
        slot = _mm_add_epi32(slot, four);
        let free = _mm_movemask_ps(_mm_castsi128_ps(_mm_cmpeq_epi32(_mm_and_si128(_mm256_castsi256_si128(seconds), payload), _mm_setzero_si128()))) as usize;
        let mut bought = keep & !free;
        while bought != 0 {
            let at = count + (keep & ((bought & bought.wrapping_neg()) - 1)).count_ones() as usize;
            *buys.add(at >> 3) |= 1 << (at & 7);
            bought &= bought - 1;
        }
        count += keep.count_ones() as usize;
    }
    (count, foreign != 0)
}

#[inline(always)]
unsafe fn front8(lanes: std::arch::x86_64::__m256i, mask: u32) -> std::arch::x86_64::__m256i {
    use std::arch::x86_64::*;
    let places = _pext_u64(0x0706_0504_0302_0100, _pdep_u64(u64::from(mask), 0x0101_0101_0101_0101) * 255);
    _mm256_permutevar8x32_epi32(lanes, _mm256_cvtepu8_epi32(_mm_cvtsi64_si128(places as i64)))
}

#[inline(never)]
unsafe fn sessions_of(who: *mut u32, ts: *mut u32, count: usize, buys: *const u8, first: *mut u32, start: *mut u32, bought: *mut u64) -> (usize, usize, bool) {
    use std::arch::x86_64::*;
    *who.sub(1) = u32::MAX;
    *ts.sub(1) = 0;
    let gap = _mm256_set1_epi32(GAP as i32);
    let top = _mm256_set1_epi32(TOP as i32);
    let eight = _mm256_set1_epi32(8);
    let mut number = _mm256_setr_epi32(0, 1, 2, 3, 4, 5, 6, 7);
    let (mut sessions, mut purchases, mut back) = (0usize, 0usize, 0u32);
    let mut at = 0;
    while at < count {
        let left = count - at;
        let real = if left >= 8 { 255 } else { (1u32 << left) - 1 };
        let users = _mm256_loadu_si256(who.add(at) as *const __m256i);
        let stamps = _mm256_loadu_si256(ts.add(at) as *const __m256i);
        let same = _mm256_cmpeq_epi32(_mm256_srli_epi32(_mm256_xor_si256(users, _mm256_loadu_si256(who.add(at).sub(1) as *const __m256i)), ALIAS_BITS as i32), _mm256_setzero_si256());
        let since = _mm256_sub_epi32(stamps, _mm256_loadu_si256(ts.add(at).sub(1) as *const __m256i));
        let near = _mm256_cmpeq_epi32(_mm256_min_epu32(since, gap), since);
        let continues = _mm256_movemask_ps(_mm256_castsi256_ps(_mm256_and_si256(same, near))) as u32;
        let starts = !continues & real;
        back |= _mm256_movemask_ps(_mm256_castsi256_ps(_mm256_and_si256(same, since))) as u32 & real;
        _mm256_storeu_si256(first.add(sessions) as *mut __m256i, front8(_mm256_or_si256(number, _mm256_andnot_si256(same, top)), starts));
        _mm256_storeu_si256(start.add(sessions) as *mut __m256i, front8(stamps, starts));
        number = _mm256_add_epi32(number, eight);
        let mut buying = u32::from(*buys.add(at >> 3));
        while buying != 0 {
            let lane = buying.trailing_zeros();
            let session = sessions + (starts & ((2 << lane) - 1)).count_ones() as usize - 1;
            *bought.add(purchases) = (session as u64) << 32 | (at as u64 + u64::from(lane));
            purchases += 1;
            buying &= buying - 1;
        }
        sessions += starts.count_ones() as usize;
        at += 8;
    }
    (sessions, purchases, back != 0)
}

#[inline(always)]
unsafe fn aliases(who: *const u32, from: usize, to: usize) -> u32 {
    use std::arch::x86_64::*;
    static REAL: [u32; 16] = [u32::MAX, u32::MAX, u32::MAX, u32::MAX, u32::MAX, u32::MAX, u32::MAX, u32::MAX, 0, 0, 0, 0, 0, 0, 0, 0];
    let (low, most, one) = (_mm256_set1_epi32(511), _mm256_set1_epi32(8), _mm256_set1_epi32(1));
    let mut all = _mm256_setzero_si256();
    let mut at = from;
    while at < to {
        let real = _mm256_loadu_si256(REAL.as_ptr().add(8 - (to - at).min(8)) as *const __m256i);
        let alias = _mm256_min_epu32(_mm256_and_si256(_mm256_loadu_si256(who.add(at) as *const __m256i), low), most);
        all = _mm256_or_si256(all, _mm256_and_si256(_mm256_sllv_epi32(one, alias), real));
        at += 8;
    }
    let half = _mm_or_si128(_mm256_castsi256_si128(all), _mm256_extracti128_si256(all, 1));
    let pair = _mm_or_si128(half, _mm_unpackhi_epi64(half, half));
    (_mm_cvtsi128_si32(pair) | _mm_extract_epi32(pair, 1)) as u32
}

#[allow(clippy::too_many_arguments)]
unsafe fn gather(best: *const Rec, who: *const u32, ts: *const u32, slots: *const u32, from: usize, to: usize, ids: &mut Vec<u32>, events: &mut Vec<u64>) {
    ids.extend_from_slice(std::slice::from_raw_parts(who.add(from), to - from));
    events.extend((from..to).map(|at| u64::from(*ts.add(at)) << 32 | (*best.add(*slots.add(at) as usize)).b & 0x1FFF_FFFF));
}

#[derive(Default)]
struct Table {
    who: Vec<u32>,
    ts: Vec<u32>,
    slots: Vec<u32>,
    buys: Vec<u8>,
    first: Vec<u32>,
    start: Vec<u32>,
    day: Vec<u32>,
    campaign: Vec<u32>,
    row: Vec<u32>,
    bought: Vec<u64>,
    row_session: Vec<u32>,
    row_event: Vec<u32>,
    row_revenue: Vec<i64>,
    row_category: Vec<u8>,
    run_session: Vec<u32>,
    run_row: Vec<u32>,
    run_name: Vec<u64>,
}

impl Table {
    fn new() -> Table {
        let size = BUCKET + 16;
        Table {
            who: vec![0; size],
            ts: vec![0; size],
            slots: vec![0; size],
            buys: vec![0; BUCKET / 8 + 8],
            first: vec![0; size],
            start: vec![0; size],
            day: vec![0; size],
            campaign: vec![0; size],
            row: vec![0; size],

            bought: vec![0; size],
            row_session: vec![0; size],
            row_event: vec![0; size],
            row_revenue: vec![0; size],
            row_category: vec![0; size],
            run_session: vec![0; size],
            run_row: vec![0; size],
            run_name: vec![0; size],
        }
    }
}

impl<'a> Local<'a> {
    fn write_file(&mut self) {
        if self.rows == 0 {
            return;
        }
        let column = &mut self.columns[5];
        column.present.clear();
        column.present.resize(self.rows.div_ceil(8), 0);
        column.values.clear();
        for (row, &category) in self.categories.iter().enumerate() {
            if category != NO_CATEGORY {
                column.present[row / 8] |= 1 << (row % 8);
                column.values.push(category);
            }
        }
        let name = format!("dense-{}-{}.parquet", self.thread, self.files);
        pqw::write(&self.output.join(concat!("use", "r_d", "ail", "y")).join(name), &T_ONE, &self.columns, self.rows).unwrap();
        self.files += 1;
        self.rows = 0;
        for column in &mut self.columns {
            column.values.clear();
        }
        self.categories.clear();
        self.columns[0].dictionary.clear();
        self.columns[0].dictionary_len = 0;
    }

    #[inline(always)]
    fn name(&mut self, id: u64) -> usize {
        let mut text = [0u8; 16];
        let len = encode(b'u', scramble(id, self.stage.shared.plan.user_key), &mut text);
        let column = &mut self.columns[0];
        column.dictionary.extend_from_slice(&(len as u32).to_le_bytes());
        column.dictionary.extend_from_slice(&text[..len]);
        column.dictionary_len += 1;
        column.dictionary_len - 1
    }

    #[inline(always)]
    fn emit(&mut self, row: &Row) {
        self.columns[1].values.push(row.day as u8);
        self.columns[2].values.push(row.sessions as u8);
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
        self.categories.push(top as u8);
        self.rows += 1;
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
        let mut clock = if PROFILE { std::arch::x86_64::_rdtsc() } else { 0 };
        self.mark -= 1;
        if self.mark == 0 {
            self.best.fill(UNUSED);
            self.mark = MARKS;
        }
        let (mark, marked) = (self.mark << 50, self.mark);
        for thread in stage.parsed {
            thread.events.for_each_chunk(part, |chunk| keep_earliest(chunk, best, mark));
        }
        step(&mut clock, 0);
        let context = stage.shared.context;
        let days = context.days as u32;
        let organic = context.campaign_ids.len() as u32;
        let unfinished = organic + 1;
        let mut table = std::mem::take(&mut self.table);
        let t = &mut table;
        let (first, start, day_of, campaign_of, row_of) =
            (t.first.as_mut_ptr(), t.start.as_mut_ptr(), t.day.as_mut_ptr(), t.campaign.as_mut_ptr(), t.row.as_mut_ptr());
        let (who, ts, slots) = (t.who.as_mut_ptr().add(8), t.ts.as_mut_ptr().add(8), t.slots.as_mut_ptr().add(8));
        let bought = t.bought.as_mut_ptr();
        let (row_session, row_event, row_revenue, row_category) =
            (t.row_session.as_mut_ptr(), t.row_event.as_mut_ptr(), t.row_revenue.as_mut_ptr(), t.row_category.as_mut_ptr());
        let (run_session, run_row, run_name) = (t.run_session.as_mut_ptr(), t.run_row.as_mut_ptr(), t.run_name.as_mut_ptr());

        let (count, foreign) = pack(best, marked, who, ts, slots, t.buys.as_mut_ptr());
        if foreign {
            self.foreign_events(marked);
        }
        step(&mut clock, 1);
        if count == 0 {
            self.table = table;
            return;
        }
        let (sessions, purchases, back) = sessions_of(who, ts, count, t.buys.as_ptr(), first, start, bought);
        *first.add(sessions) = count as u32 | TOP;

        step(&mut clock, 2);
        let (mut rows, mut runs) = (0usize, 0usize);
        let mut last_day = u32::MAX;
        for session in 0..sessions {
            let head = *first.add(session);
            let day = ((context.day_offset + u64::from(*start.add(session))) / DAY as u64) as u32;
            *day_of.add(session) = day;
            *campaign_of.add(session) = organic;
            *run_session.add(runs) = session as u32;
            *run_row.add(runs) = rows as u32;
            runs += (head >> 31) as usize;
            *row_session.add(rows) = session as u32;
            *row_event.add(rows) = head & LOW;
            rows += (head >> 31 | u32::from(day != last_day)) as usize;
            *row_of.add(session) = rows as u32 - 1;
            last_day = day;
        }
        *run_session.add(runs) = sessions as u32;
        *run_row.add(runs) = rows as u32;
        *row_session.add(rows) = sessions as u32;
        *row_event.add(rows) = count as u32;
        std::ptr::write_bytes(row_revenue, 0, rows);
        std::ptr::write_bytes(row_category, NO_CATEGORY, rows);

        step(&mut clock, 3);
        for run in 0..runs {
            let (from, to) = (*run_session.add(run) as usize, *run_session.add(run + 1) as usize);
            let (a, e) = ((*first.add(from) & LOW) as usize, (*first.add(to) & LOW) as usize);
            let events = e - a;
            let id = *who.add(a);
            let user = id >> ALIAS_BITS;
            let unsorted = back && (a + 1..e).any(|at| *ts.add(at) < *ts.add(at - 1));
            let mut name = NONE;
            let mut inner = if PROFILE { std::arch::x86_64::_rdtsc() } else { 0 };
            if run == 0 || run + 1 == runs {
                let edges = &mut self.edges;
                edges.runs.push((part as u32 * 2 + u32::from(run > 0), user, edges.who.len(), events));
                gather(best, who, ts, slots, a, e, &mut edges.who, &mut edges.events);
                step(&mut inner, 10);
            } else if unsorted {
                self.who.clear();
                self.events.clear();
                gather(best, who, ts, slots, a, e, &mut self.who, &mut self.events);
                self.run(user as usize, 0, events);
                step(&mut inner, 11);
            } else {
                name = self.claim(user as usize, id, aliases(who, a, e));
                step(&mut inner, 12);
                if name == NONE {
                    self.who.clear();
                    self.events.clear();
                    gather(best, who, ts, slots, a, e, &mut self.who, &mut self.events);
                    self.side(user as usize, 0, events);
                    step(&mut inner, 13);
                } else if *stage.starts.0.add(user as usize) != *stage.starts.0.add(user as usize + 1) {
                    self.credit(user as usize, t, from, to);
                    step(&mut inner, 14);
                }
            }
            *run_name.add(run) = name;
            if name == NONE {
                for session in from..to {
                    *campaign_of.add(session) = unfinished;
                }
            }
        }

        step(&mut clock, 4);
        self.flush_assists();
        let credited = self.credited.as_mut_ptr();
        for session in 0..sessions {
            *credited.add((*campaign_of.add(session) * days + *day_of.add(session)) as usize) += 1;
        }

        step(&mut clock, 5);
        let bought_by = self.bought.as_mut_ptr();
        let mut sums = [0i64; 32];
        let mut sum_row = [u32::MAX; 32];
        let (mut last_session, mut last_row, mut top) = (u32::MAX, u32::MAX, 0i64);
        for at in 0..purchases {
            let payload = (*best.add(*slots.add(*bought.add(at) as u32 as usize) as usize)).b as u32 & 0x1FFF_FFFF;
            let (category, price) = ((payload >> 24) as usize, i64::from(payload & 0x00FF_FFFF));
            let session = (*bought.add(at) >> 32) as u32;
            let cell = bought_by.add((*campaign_of.add(session as usize) * days + *day_of.add(session as usize)) as usize);
            (*cell)[0] += i64::from(session != last_session);
            (*cell)[1] += price;
            last_session = session;
            let row = *row_of.add(session as usize);
            let sum = if sum_row[category] == row { sums[category] } else { 0 } + price;
            sums[category] = sum;
            sum_row[category] = row;
            if row != last_row {
                top = 0;
            }
            last_row = row;
            top = top.max(sum << 5 | (31 - category as i64));
            *row_revenue.add(row as usize) += price;
            *row_category.add(row as usize) = 31 - (top & 31) as u8;
        }

        step(&mut clock, 6);
        for run in 0..runs {
            let name = *run_name.add(run);
            if name != NONE {
                let place = self.name(name);
                self.columns[0].push_run((*run_row.add(run + 1) - *run_row.add(run)) as usize, place);
            }
        }
        step(&mut clock, 7);
        let had = self.rows;
        self.columns[1].values.reserve(rows);
        self.columns[2].values.reserve(rows);
        self.columns[3].values.reserve(rows * 4);
        self.columns[4].values.reserve(rows * 8);
        self.categories.reserve(rows);
        let (day_out, sessions_out, events_out, revenue_out, category_out) = (
            self.columns[1].values.as_mut_ptr().add(had),
            self.columns[2].values.as_mut_ptr().add(had),
            self.columns[3].values.as_mut_ptr().add(had * 4) as *mut u32,
            self.columns[4].values.as_mut_ptr().add(had * 8) as *mut i64,
            self.categories.as_mut_ptr().add(had),
        );
        let mut kept = 0;
        for row in 0..rows {
            let session = *row_session.add(row) as usize;
            *day_out.add(kept) = *day_of.add(session) as u8;
            *sessions_out.add(kept) = (*row_session.add(row + 1) - session as u32) as u8;
            events_out.add(kept).write_unaligned(*row_event.add(row + 1) - *row_event.add(row));
            revenue_out.add(kept).write_unaligned(*row_revenue.add(row));
            *category_out.add(kept) = *row_category.add(row);
            kept += usize::from(*campaign_of.add(session) != unfinished);
        }
        let rows = had + kept;
        self.columns[1].values.set_len(rows);
        self.columns[2].values.set_len(rows);
        self.columns[3].values.set_len(rows * 4);
        self.columns[4].values.set_len(rows * 8);
        self.categories.set_len(rows);
        self.rows = rows;
        self.table = table;
        step(&mut clock, 8);
        if self.rows >= FILE_ROWS {
            self.write_file();
        }
        step(&mut clock, 9);
    }

    #[cold]
    #[inline(never)]
    unsafe fn foreign_events(&mut self, marked: u64) {
        for low in 0..BUCKET {
            let record = self.best[low];
            let stamp = record.a >> 32 & INVALID;
            if record.b >> 50 == marked && stamp != INVALID && record.a as u32 & FOREIGN != 0 {
                let person = self.stage.person(record.a as u32);
                self.side_event(person, stamp << 32 | record.b & 0x1FFF_FFFF);
            }
        }
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

    #[inline(never)]
    unsafe fn run(&mut self, user: usize, from: usize, to: usize) {
        let mut used = 0;
        for at in from..to {
            used |= 1 << (*self.who.get_unchecked(at) & 511).min(8);
        }
        let name = self.claim(user, *self.who.get_unchecked(from), used);
        if name == NONE {
            return self.side(user, from, to);
        }
        let mut sorted = true;
        for at in from + 1..to {
            sorted &= *self.events.get_unchecked(at - 1) >> 32 <= *self.events.get_unchecked(at) >> 32;
        }
        let events: &[u64] = if sorted {
            std::slice::from_raw_parts(self.events.as_ptr().add(from), to - from)
        } else {
            self.sorted.clear();
            self.sorted.extend_from_slice(std::slice::from_raw_parts(self.events.as_ptr().add(from), to - from));
            self.sorted.sort_unstable_by_key(|event| event >> 32);
            std::slice::from_raw_parts(self.sorted.as_ptr(), to - from)
        };
        let place = self.name(name);
        let had = self.rows;
        self.sessions(events, self.stage.clicks_of(user));
        self.columns[0].push_run(self.rows - had, place);
        if self.rows >= FILE_ROWS {
            self.write_file();
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
    unsafe fn claim(&mut self, user: usize, first: u32, used: u32) -> u64 {
        let stage = self.stage;
        let shared = stage.shared;
        if shared.state.get_unchecked(user).load(Relaxed) & (LINKED_OUT | ODD) != 0 {
            return NONE;
        }
        let mut used = used & 511;
        for click in stage.clicks_of(user) {
            used |= 1 << (click.a as u32 & 511).min(8);
        }
        let mut name = u64::from(first);
        if used & (used - 1) != 0 || shared.adjacent.get_unchecked(user).load(Relaxed) != 0 || used >> 8 != 0 {
            name = self.person(user, first, used);
            if name == NONE {
                return NONE;
            }
        }
        if shared.state.get_unchecked(user).fetch_or(LOCAL, Relaxed) & (LOCAL | SIDE) != 0 {
            VIOLATION.store(true, Relaxed);
        }
        name
    }

    #[inline(never)]
    unsafe fn person(&mut self, user: usize, first: u32, used: u32) -> u64 {
        let shared = self.stage.shared;
        if used >> 8 != 0 {
            return NONE;
        }
        let component = u32::from(shared.component(user, first & 511));
        if used & !component != 0 && used & (used - 1) != 0 {
            return NONE;
        }
        if component != 0 {
            shared.smallest(user, component as u8)
        } else {
            u64::from(first)
        }
    }

    #[inline(always)]
    unsafe fn credit(&mut self, user: usize, table: &mut Table, from: usize, to: usize) {
        use std::arch::x86_64::*;
        let records = self.stage.clicks_of(user);
        if records.len() > 16 {
            return self.credit_many(records, table, from, to);
        }
        #[repr(align(32))]
        struct Lanes([u32; 16]);
        let (mut stamps, mut campaigns, mut earlier) = (Lanes([0; 16]), Lanes([0; 16]), Lanes([0; 16]));
        for (place, click) in records.iter().enumerate() {
            stamps.0[place] = (click.a >> 32) as u32;
            campaigns.0[place] = (click.b >> 40) as u32;
        }
        let load = |lanes: &Lanes, half: usize| _mm256_load_si256(lanes.0.as_ptr().add(8 * half) as *const __m256i);
        let bits = |low: __m256i, high: __m256i| (_mm256_movemask_ps(_mm256_castsi256_ps(low)) | _mm256_movemask_ps(_mm256_castsi256_ps(high)) << 8) as u32;
        let (stamps_low, stamps_high) = (load(&stamps, 0), load(&stamps, 1));
        let (campaigns_low, campaigns_high) = (load(&campaigns, 0), load(&campaigns, 1));
        for place in 0..records.len() {
            let one = _mm256_set1_epi32(campaigns.0[place] as i32);
            earlier.0[place] = bits(_mm256_cmpeq_epi32(campaigns_low, one), _mm256_cmpeq_epi32(campaigns_high, one)) & ((1 << place) - 1);
        }
        let (earlier_low, earlier_high) = (load(&earlier, 0), load(&earlier, 1));
        let days = _mm256_set1_epi32(self.stage.shared.context.days as i32);
        let (cells_low, cells_high) = (_mm256_mullo_epi32(campaigns_low, days), _mm256_mullo_epi32(campaigns_high, days));
        let valid = (1u32 << records.len()) - 1;
        let week = _mm256_set1_epi32(WEEK as i32);
        let mut listed = self.assists.len();
        if listed + 16 * (to - from) + 16 > self.assists.capacity() {
            self.flush_assists();
            self.assists.reserve(16 * (to - from) + 16);
            listed = 0;
        }
        let list = self.assists.as_mut_ptr();
        for session in from..to {
            let start = _mm256_set1_epi32(*table.start.get_unchecked(session) as i32);
            let day = _mm256_set1_epi32(*table.day.get_unchecked(session) as i32);
            let (after_low, after_high) = (_mm256_sub_epi32(stamps_low, start), _mm256_sub_epi32(stamps_high, start));
            let inside = bits(
                _mm256_cmpeq_epi32(_mm256_min_epu32(after_low, week), after_low),
                _mm256_cmpeq_epi32(_mm256_min_epu32(after_high, week), after_high),
            ) & valid;
            let latest = campaigns.0[(31 - (inside | 1).leading_zeros()) as usize & 15];
            let credited = table.campaign.get_unchecked_mut(session);
            *credited = if inside != 0 { latest } else { *credited };
            let lowest = _mm256_set1_epi32((inside & inside.wrapping_neg()) as i32);
            let counted = inside & bits(_mm256_cmpgt_epi32(lowest, earlier_low), _mm256_cmpgt_epi32(lowest, earlier_high));
            for (half, cells) in [cells_low, cells_high].into_iter().enumerate() {
                let mask = u64::from(counted >> (8 * half) & 255);
                let places = _pext_u64(0x0706_0504_0302_0100, _pdep_u64(mask, 0x0101_0101_0101_0101) * 255);
                let packed = _mm256_permutevar8x32_epi32(_mm256_add_epi32(cells, day), _mm256_cvtepu8_epi32(_mm_cvtsi64_si128(places as i64)));
                _mm256_storeu_si256(list.add(listed) as *mut __m256i, packed);
                listed += mask.count_ones() as usize;
            }
        }
        self.assists.set_len(listed);
    }

    #[inline(never)]
    fn flush_assists(&mut self) {
        for &cell in &self.assists {
            unsafe { *self.assisted.get_unchecked_mut(cell as usize) += 1 };
        }
        self.assists.clear();
    }

    #[inline(never)]
    unsafe fn credit_many(&mut self, clicks: &[Rec], table: &mut Table, from: usize, to: usize) {
        use std::arch::x86_64::*;
        let days = self.stage.shared.context.days;
        if days > 16 {
            return self.credit_slow(clicks, table, from, to);
        }
        static ONE_DAY: [DayCounts; 16] = {
            let mut table = [DayCounts([0; 16]); 16];
            let mut day = 0;
            while day < 16 {
                table[day].0[day] = 1;
                day += 1;
            }
            table
        };
        let stamp = |click: &Rec| (click.a >> 32) as u32;
        let campaign = |click: &Rec| (click.b >> 40) as usize;
        let count = to - from;
        let starts = table.start.as_ptr().add(from);
        self.before.clear();
        self.before.reserve(count + 1);
        let before = self.before.as_mut_ptr() as *mut __m256i;
        let mut sum = _mm256_setzero_si256();
        _mm256_store_si256(before, sum);
        let mut high = 0;
        for session in 0..count {
            let start = *starts.add(session);
            sum = _mm256_add_epi16(sum, _mm256_load_si256(ONE_DAY.as_ptr().add(*table.day.get_unchecked(from + session) as usize) as *const __m256i));
            _mm256_store_si256(before.add(session + 1), sum);
            while high < clicks.len() && stamp(clicks.get_unchecked(high)) <= start + WEEK as u32 {
                high += 1;
            }
            if high > 0 && stamp(clicks.get_unchecked(high - 1)) >= start {
                *table.campaign.get_unchecked_mut(from + session) = campaign(clicks.get_unchecked(high - 1)) as u32;
            }
        }
        let reached = self.active_count.as_mut_ptr();
        let assisted = self.assisted.as_mut_ptr();
        let (mut low, mut high) = (0, 0);
        for click in clicks {
            let at = stamp(click);
            while high < count && *starts.add(high) <= at {
                high += 1;
            }
            while low < high && *starts.add(low) + (WEEK as u32) < at {
                low += 1;
            }
            let reach = reached.add(campaign(click));
            let first = low.max(*reach as usize);
            *reach = high as u32;
            let more = _mm256_sub_epi16(_mm256_load_si256(before.add(high)), _mm256_load_si256(before.add(first)));
            let cells = assisted.add(campaign(click) * days) as *mut __m256i;
            _mm256_storeu_si256(cells, _mm256_add_epi32(_mm256_loadu_si256(cells), _mm256_cvtepu16_epi32(_mm256_castsi256_si128(more))));
            let cells = cells.add(1);
            _mm256_storeu_si256(cells, _mm256_add_epi32(_mm256_loadu_si256(cells), _mm256_cvtepu16_epi32(_mm256_extracti128_si256(more, 1))));
        }
        for click in clicks {
            *reached.add(campaign(click)) = 0;
        }
    }

    #[inline(never)]
    unsafe fn credit_slow(&mut self, clicks: &[Rec], table: &mut Table, from: usize, to: usize) {
        let context = self.stage.shared.context;
        let days = context.days;
        let stamp = |click: &Rec| (click.a >> 32) as u32;
        let campaign = |click: &Rec| (click.b >> 40) as usize;
        let (mut low, mut high) = (0, 0);
        for session in from..to {
            let start = u64::from(*table.start.get_unchecked(session));
            let day = *table.day.get_unchecked(session) as usize;
            let reach = (start + WEEK as u64) as u32;
            while high < clicks.len() && stamp(&clicks[high]) <= reach {
                let campaign = campaign(&clicks[high]);
                if self.active_count[campaign] == 0 {
                    self.active_at[campaign] = self.active.len() as u32;
                    self.active.push(campaign as u32);
                }
                self.active_count[campaign] += 1;
                high += 1;
            }
            while low < high && stamp(&clicks[low]) < start as u32 {
                let campaign = campaign(&clicks[low]);
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
                *table.campaign.get_unchecked_mut(session) = campaign(&clicks[high - 1]) as u32;
            }
            for &campaign in &self.active {
                *self.assisted.get_unchecked_mut(campaign as usize * days + day) += 1;
            }
        }
        for &campaign in &self.active {
            self.active_count[campaign as usize] = 0;
        }
        self.active.clear();
    }

    #[inline(always)]
    unsafe fn sessions(&mut self, events: &[u64], records: &[Rec]) {
        let context = self.stage.shared.context;
        let days = context.days;
        let organic = context.campaign_ids.len();
        let clicks = records;
        let stamp = |click: Rec| (click.a >> 32) as u32;
        let campaign = |click: Rec| (click.b >> 40) as usize;
        let mut row = Row { day: usize::MAX, sessions: 0, events: 0, revenue: 0 };
        let (mut low, mut high) = (0, 0);
        let mut at = 0;
        while at < events.len() {
            let start = *events.get_unchecked(at) >> 32;
            let day = ((context.day_offset + start) / DAY as u64) as usize;
            if day != row.day {
                if row.day != usize::MAX {
                    self.emit(&row);
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
                    credited = campaign(clicks[high - 1]);
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
            self.emit(&row);
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
unsafe fn group_clicks(
    parsed: &[Parse],
    part: usize,
    base: usize,
    clicks: &Raw<Rec>,
    starts: &Raw<u32>,
    counts: &mut Vec<u32>,
    keys: &mut Vec<u64>,
    copy: &mut Vec<Rec>,
    large: &std::sync::Mutex<Vec<(usize, usize)>>,
) {
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
    let mut from = base;
    for &to in counts.iter() {
        let to = to as usize;
        if to - from > MANY_CLICKS {
            large.lock().unwrap().push((from, to));
        } else if to - from > 1 {
            sort_clicks(std::slice::from_raw_parts_mut(clicks.0.add(from), to - from), keys, copy);
        }
        from = to;
    }
}

const MANY_CLICKS: usize = 4096;

fn sort_clicks(clicks: &mut [Rec], keys: &mut Vec<u64>, copy: &mut Vec<Rec>) {
    let before = |x: &Rec, y: &Rec| {
        let (at_x, at_y) = (x.a >> 32, y.a >> 32);
        at_x < at_y || (at_x == at_y && codec::order(x.b & MASK) > codec::order(y.b & MASK))
    };
    let insertion = |clicks: &mut [Rec]| {
        for at in 1..clicks.len() {
            let click = clicks[at];
            let mut hole = at;
            while hole > 0 && before(&click, &clicks[hole - 1]) {
                clicks[hole] = clicks[hole - 1];
                hole -= 1;
            }
            clicks[hole] = click;
        }
    };
    if clicks.len() <= 32 {
        use std::arch::x86_64::*;
        #[repr(align(32))]
        struct Lanes([u32; 32]);
        let mut stamps = Lanes([i32::MAX as u32; 32]);
        let mut copy = [EMPTY; 32];
        for (place, click) in clicks.iter().enumerate() {
            stamps.0[place] = (click.a >> 32) as u32;
            copy[place] = *click;
        }
        let groups = clicks.len().div_ceil(8);
        let mut ties = false;
        unsafe {
            let lanes = stamps.0.as_ptr() as *const __m256i;
            for place in 0..clicks.len() {
                let one = _mm256_set1_epi32(stamps.0[place] as i32);
                let (mut earlier, mut same) = (0u32, 0u32);
                for group in 0..groups {
                    let stamps = _mm256_load_si256(lanes.add(group));
                    earlier += (_mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpgt_epi32(one, stamps))) as u32).count_ones();
                    same |= (_mm256_movemask_ps(_mm256_castsi256_ps(_mm256_cmpeq_epi32(one, stamps))) as u32) << (8 * group);
                }
                same &= (1 << place) - 1;
                ties |= same != 0 && copy[same.trailing_zeros() as usize].b != copy[place].b;
                *clicks.get_unchecked_mut((earlier + same.count_ones()) as usize) = copy[place];
            }
        }
        if ties {
            insertion(clicks);
        }
        return;
    }
    keys.clear();
    keys.extend(clicks.iter().enumerate().map(|(place, click)| click.a >> 32 << 32 | place as u64));
    keys.sort_unstable();
    copy.clear();
    copy.extend(keys.iter().map(|&key| clicks[key as u32 as usize]));
    clicks.copy_from_slice(copy);
    let mut from = 0;
    while from < clicks.len() {
        let mut to = from + 1;
        while to < clicks.len() && clicks[to].a >> 32 == clicks[from].a >> 32 {
            to += 1;
        }
        if to - from > 1 {
            insertion(&mut clicks[from..to]);
        }
        from = to;
    }
}

fn row_columns(context: &Context) -> Vec<Column> {
    let mut columns: Vec<Column> = (0..6).map(|_| Column::default()).collect();
    columns[0].mode = Mode::Runs;
    for (column, values) in [(1, context.days), (2, 256), (5, context.categories.len())] {
        columns[column].mode = Mode::Bytes;
        columns[column].dictionary_len = values;
    }
    for day in 0..context.days {
        columns[1].dictionary.extend_from_slice(&(context.first_day + day as i32).to_le_bytes());
    }
    for sessions in 0..256i32 {
        columns[2].dictionary.extend_from_slice(&sessions.to_le_bytes());
    }
    for category in &context.categories {
        columns[5].dictionary.extend_from_slice(&(category.len() as u32).to_le_bytes());
        columns[5].dictionary.extend_from_slice(category);
    }
    columns
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
    let first_tick = pool::now_ticks();
    let lap = |what: &str| {
        if verbose {
            let mut cpu = libc::timespec { tv_sec: 0, tv_nsec: 0 };
            unsafe { libc::clock_gettime(libc::CLOCK_PROCESS_CPUTIME_ID, &mut cpu) };
            let cpu = cpu.tv_sec as f64 * 1e3 + cpu.tv_nsec as f64 / 1e6;
            let ticks = (pool::now_ticks() - first_tick).max(1);
            let alone = started.elapsed().as_secs_f64() * 1e3 * ticks.saturating_sub(pool::staged_ticks()) as f64 / ticks as f64;
            let mut usage: libc::rusage = unsafe { std::mem::zeroed() };
            unsafe { libc::getrusage(libc::RUSAGE_SELF, &mut usage) };
            let system = usage.ru_stime.tv_sec as f64 * 1e3 + usage.ru_stime.tv_usec as f64 / 1e3;
            eprintln!(
                "{:>8.1} ms  cpu {cpu:>8.1} ms  {what}  (sys {system:.0} ms, {} faults, {} MB peak, {}% idle, {alone:.1} ms alone)",
                started.elapsed().as_secs_f64() * 1e3,
                usage.ru_minflt,
                usage.ru_maxrss >> 10,
                pool::idle()
            );
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
    enum Ready {
        Plan(Result<Plan, &'static str>),
        Context(Option<Context>),
        Input(Input),
        Events(lines::Input),
    }
    let (links_end, clicks_end) = (2 + link_paths.len(), 2 + link_paths.len() + click_paths.len());
    let mut ready = pool::fill(threads, clicks_end + event_paths.len(), |task| match task {
        0 => Ready::Plan(detect(&link_paths, &event_paths)),
        1 => {
            fs::create_dir_all(output.join(concat!("use", "r_d", "ail", "y"))).unwrap();
            fs::create_dir_all(output.join(concat!("cam", "pai", "gn_", "dai", "ly"))).unwrap();
            Ready::Context(load_context(data))
        }
        _ if task < links_end => Ready::Input(scan::open(&link_paths[task - 2])),
        _ if task < clicks_end => Ready::Input(scan::open(&click_paths[task - links_end])),
        _ => Ready::Events(lines::open(&event_paths[task - clicks_end])),
    })
    .into_iter();
    let (Some(Ready::Plan(plan)), Some(Ready::Context(context))) = (ready.next(), ready.next()) else { unreachable!() };
    let mut link_inputs = Vec::new();
    let mut click_inputs = Vec::new();
    let mut event_inputs = Vec::new();
    for (task, ready) in ready.enumerate() {
        match ready {
            Ready::Input(input) if task + 2 < links_end => link_inputs.push(input),
            Ready::Input(input) => click_inputs.push(input),
            Ready::Events(input) => event_inputs.push(input),
            _ => unreachable!(),
        }
    }
    let plan = match plan {
        Ok(plan) => plan,
        Err(why) => return refuse(why),
    };
    let click_lines = &click_inputs;
    let event_bytes: u64 = event_inputs.iter().map(lines::Input::len).sum();
    let click_bytes: u64 = click_lines.iter().map(lines::Input::len).sum();
    lap("dense: keys");

    let Some(mut context) = context else { return refuse("no context") };
    if context.categories.len() > 32 || context.campaign_ids.len() >= 1 << 24 || context.days > 255 {
        return refuse("too many categories or campaigns");
    }
    let estimate = event_bytes / 80;
    context.person_bits = (estimate / 160_000).max(1).next_power_of_two().trailing_zeros().clamp(4, 11);
    context.event_bits = 4;
    let context = &context;
    let users = plan.users;
    let buckets = (plan.event_bound >> BUCKET_BITS) as usize;
    let ingest_start = context.window_start.div_euclid(1000) - INGEST_LEAD;
    let shared = Shared {
        context,
        frame: sink::Frame {
            user_key: plan.user_key,
            event_key: plan.event_key,
            user_bound: (plan.users as u64) << ALIAS_BITS,
            event_bound: plan.event_bound,
            ingest_start,
            window_start: context.window_start,
            window_end: context.window_end,
            spare: buckets as u64,
        },
        plan,
        ingest_start,
        state: zeros(users),
        adjacent: zeros(users),
    };
    let shared = &shared;

    let chunk = super::source::chunk();
    let link_tasks = scan::tasks(&link_inputs, chunk.min(1 << 18));
    let next = AtomicUsize::new(0);
    let barrier = Barrier::new(threads);
    let pairs: Vec<Vec<(u64, u64)>> = {
        {
            {
                pool::map(threads, |_| unsafe {
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
            }
        }
    };
    lap("dense: links parsed");
    let links = build_links(threads, &pairs);
    let links = &links;
    lap("dense: links joined");

    let record_bytes = (event_bytes / 80 * 16 + click_bytes / 45 * 16) as usize;
    let click_parts = users >> USER_BITS;
    let click_tasks = lines::tasks(click_lines, chunk);
    let event_tasks = lines::tasks(&event_inputs, chunk);
    let plain = std::env::var_os("DENSE_PLAIN").is_some();
    let (next_click, next_event) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let parsed: Vec<Parse> = {
        {
            {
                let (click_tasks, event_tasks, event_inputs) = (&click_tasks, &event_tasks, &event_inputs);
                let (next_click, next_event) = (&next_click, &next_event);
                pool::map(threads, move |thread| unsafe {
                    let arena = Arena::leak(record_bytes / 4);
                    let mut parser = Parser {
                        shared,
                        thread: thread as u32,
                        calendar: Calendar::new(),
                        events: Scatter::new(arena, buckets + 1),
                        clicks: Scatter::new(arena, click_parts),
                        foreign: Vec::new(),
                        odd_events: Vec::new(),
                        odd_clicks: Vec::new(),
                    };
                    let mut event_buffer = lines::Buffer::new();
                    let mut batch = lines::Batch::new();
                    while let Some(&task) = event_tasks.get(next_event.fetch_add(1, Relaxed)) {
                        if plain {
                            lines::run_plain(&event_inputs[task.file], task, &mut event_buffer, &mut parser);
                        } else {
                            lines::run_events(&event_inputs[task.file], task, &mut event_buffer, &mut batch, &mut parser);
                        }
                    }
                    while let Some(&task) = click_tasks.get(next_click.fetch_add(1, Relaxed)) {
                        if plain {
                            lines::run_plain_clicks(&click_lines[task.file], task, &mut event_buffer, &mut parser);
                        } else {
                            lines::run_clicks(&click_lines[task.file], task, &mut event_buffer, &mut batch, &mut parser);
                        }
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
            }
        }
    };
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
        clicks: Raw(super::mem::shared(click_total * 16) as *mut Rec),
        starts: Raw(super::mem::shared((users + 1) * 4) as *mut u32),
    };
    unsafe { *stage.starts.0.add(users) = click_total as u32 };
    let stage = &stage;
    let (next, next_large) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let large = std::sync::Mutex::new(Vec::new());
    let barrier = Barrier::new(threads);
    {
        {
            pool::run(threads, |_| {
                let (mut counts, mut keys, mut copy) = (Vec::new(), Vec::new(), Vec::new());
                loop {
                    let part = next.fetch_add(1, Relaxed);
                    if part >= click_parts {
                        break;
                    }
                    unsafe { group_clicks(parsed, part, bases[part], &stage.clicks, &stage.starts, &mut counts, &mut keys, &mut copy, &large) };
                }
                barrier.wait();
                loop {
                    let Some(&(from, to)) = large.lock().unwrap().get(next_large.fetch_add(1, Relaxed)) else { break };
                    sort_clicks(unsafe { std::slice::from_raw_parts_mut(stage.clicks.0.add(from), to - from) }, &mut keys, &mut copy);
                }
            });
        }
       }
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
                columns: row_columns(context),
                tallies: vec![Tally::default(); (campaigns + 1) * context.days],
                assisted: vec![0; (campaigns + 1) * context.days + 16],
                categories: Vec::new(),
                credited: vec![0; (campaigns + 2) * context.days],
                bought: vec![[0; 2]; (campaigns + 2) * context.days],
                table: Table::default(),
                best: Vec::new(),
                mark: MARKS + 1,
                who: Vec::new(),
                events: Vec::new(),
                sorted: Vec::new(),
                assists: Vec::with_capacity(1 << 12),
                before: Vec::new(),
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
    {
        {
            let next = &next;
            pool::each(&mut locals, move |_, local| unsafe {
                local.best = vec![UNUSED; BUCKET];
                local.table = Table::new();
                loop {
                    let part = next.fetch_add(1, Relaxed);
                    if part >= buckets {
                        break;
                    }
                    local.bucket(part);
                }
                steps_done();
            });
        }
    }
    lap("dense: buckets");
    if PROFILE && verbose {
        for (name, cycles) in STEPS.iter().zip(&CYCLES) {
            eprintln!("{name:>12} {:>7.1} M cycles", cycles.load(Relaxed) as f64 / 1e6);
        }
        for (name, count) in STEPS.iter().zip(&COUNTS).skip(10) {
            eprintln!("{name:>12} {:>7.1} K cycles", count.load(Relaxed) as f64 / 1e3);
        }
    }

    let edges: Vec<Edges> = locals.iter_mut().map(|local| std::mem::take(&mut local.edges)).collect();
    let jobs = stitch(&edges);
    let (edges, jobs) = (&edges, &jobs);
    let (next, next_users) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let barrier = Barrier::new(threads);
    let results: Vec<(Vec<Tally>, Sendable<Parsed>)> = {
        {
            {
                let (next, next_users, barrier) = (&next, &next_users, &barrier);
                pool::consume(locals, move |_, mut local: Local| unsafe {
                    let thread = local.thread;
                    while let Some(job) = jobs.get(next.fetch_add(1, Relaxed)) {
                        local.job(job, edges);
                    }
                    local.write_file();
                    barrier.wait();
                    const STEP: usize = 1 << 12;
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
                    for (cell, tally) in local.tallies.iter_mut().enumerate() {
                        tally.assisted += local.assisted[cell];
                        tally.sessions += local.credited[cell];
                        tally.purchasing += local.bought[cell][0] as u32;
                        tally.revenue += local.bought[cell][1];
                    }
                    (local.tallies, Sendable(side))
                })
            }
        }
    };
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
    let more: Vec<Vec<Tally>> = {
        {
            {
                let next = &next;
                pool::map(side_threads, move |thread| {
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
            }
        }
    };
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
