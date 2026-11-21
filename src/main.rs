
mod mem;
mod scan;

use std::arch::x86_64::*;
use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicI64, AtomicU64, AtomicUsize, Ordering::Relaxed};
use std::sync::Barrier;
use std::time::Instant;

use mem::{Arena, Scatter};
use scan::{Buffer, Field, Input};
use nb7x::keys;
use nb7x::pqw::{self, Column, Kind, Mode, Spec};
use nb7x::slow;

const DAY: i64 = 86_400_000;
const WEEK: i64 = 7 * DAY;
const GAP: u64 = 1_800_000;
const BAD: i64 = i64::MIN;
const NO_CAMPAIGN: u32 = u32::MAX;
const NO_CATEGORY: u8 = u8::MAX;
const TOMBSTONE: u32 = u32::MAX;
const INGEST_LEAD: i64 = 4 * DAY;
const INGEST_BITS: u32 = 22;
const REF_BITS: u32 = 64 - INGEST_BITS;
const NO_REF: u64 = (1 << REF_BITS) - 1;
const INDEX_BITS: u32 = 26;
const PART_BITS: u32 = 12;

static BAIL: AtomicBool = AtomicBool::new(false);

#[cold]
fn bail() {
    BAIL.store(true, Relaxed);
}


#[derive(Clone, Copy)]
#[repr(C)]
struct Dedup {
    eid: u64,
    meta: u64,
}

#[derive(Clone, Copy)]
#[repr(C)]
struct Ev {
    person: u32,
    ts: u32,
    payload: u32,
}

#[derive(Clone, Copy)]
#[repr(C)]
struct Ck {
    id: u64,
    person: u32,
    ts: u32,
    campaign: u32,
}

type Dedups = Scatter<Dedup, 4>;
type Events = Scatter<Ev, 16>;
type Clicks = Scatter<Ck, 8>;


#[derive(Clone, Copy)]
#[repr(C, align(32))]
struct Date {
    head: u64,
    tail: u64,
    midnight: i64,
}

struct Calendar {
    dates: [Date; 64],
}

fn days_from_civil(year: i64, month: i64, day: i64) -> i64 {
    let year = if month <= 2 { year - 1 } else { year };
    let era = year.div_euclid(400);
    let year_of_era = year - era * 400;
    let day_of_year = (153 * ((month + 9) % 12) + 2) / 5 + day - 1;
    era * 146_097 + year_of_era * 365 + year_of_era / 4 - year_of_era / 100 + day_of_year - 719_468
}

const DAY_DIGITS: u64 = 0x000F_0300_0000_0000;

impl Calendar {
    fn new() -> Self {
        let mut dates = [Date { head: 0, tail: 0, midnight: 0 }; 64];
        dates[0].tail = 1;
        Calendar { dates }
    }

    #[cold]
    #[inline(never)]
    unsafe fn load(&mut self, at: *const u8) -> i64 {
        let bytes = std::slice::from_raw_parts(at, 11);
        let digit = |at: usize| bytes[at].is_ascii_digit().then(|| i64::from(bytes[at] - b'0'));
        let (Some(y1), Some(y2), Some(y3), Some(y4), Some(m1), Some(m2), Some(d1), Some(d2)) =
            (digit(0), digit(1), digit(2), digit(3), digit(5), digit(6), digit(8), digit(9))
        else {
            return BAD;
        };
        let (year, month, day) = (y1 * 1000 + y2 * 100 + y3 * 10 + y4, m1 * 10 + m2, d1 * 10 + d2);
        if bytes[4] != b'-' || bytes[7] != b'-' || bytes[10] != b'T' || !(1..=12).contains(&month) {
            return BAD;
        }
        let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
        let days_in_month = match month {
            4 | 6 | 9 | 11 => 30,
            2 => 28 + i64::from(leap),
            _ => 31,
        };
        if day < 1 || day > days_in_month {
            return BAD;
        }
        let head = (at as *const u64).read_unaligned();
        let tail = (at.add(3) as *const u64).read_unaligned();
        let midnight = days_from_civil(year, month, day) * 86_400;
        self.dates[_pext_u64(tail, DAY_DIGITS) as usize] = Date { head, tail, midnight };
        midnight
    }
}

#[inline(always)]
unsafe fn civil(at: *const u8, calendar: &mut Calendar) -> i64 {
    let head = (at as *const u64).read_unaligned();
    let tail = (at.add(3) as *const u64).read_unaligned();
    let date = calendar.dates.get_unchecked(_pext_u64(tail, DAY_DIGITS) as usize);
    let mut midnight = date.midnight;
    if head != date.head || tail != date.tail {
        midnight = calendar.load(at);
        if midnight == BAD {
            return BAD;
        }
    }
    let time = (at.add(11) as *const u64).read_unaligned() ^ u64::from_le_bytes(*b"00:00:00");
    let parts = (time.wrapping_mul(10).wrapping_add(time >> 8)) & 0x00FF_0000_FF00_00FF;
    if (time.wrapping_add(0x7676_7F76_767F_7676) | time) & 0x8080_8080_8080_8080
        | parts.wrapping_add(0x0044_0000_4400_0068) & 0x0080_0000_8000_0080
        != 0
    {
        return BAD;
    }
    midnight + (parts.wrapping_mul(3600 << 40 | 60 << 16) >> 40) as i64 + (parts >> 48) as i64
}

static RIGHT_ALIGN: [[u8; 16]; 17] = {
    let mut table = [[0x80u8; 16]; 17];
    let mut len = 0;
    while len <= 16 {
        let mut at = 0;
        while at < len {
            table[len][16 - len + at] = at as u8;
            at += 1;
        }
        len += 1;
    }
    table
};

#[inline(always)]
unsafe fn timestamp(at: *const u8, len: usize, calendar: &mut Calendar) -> i64 {
    if len == 20 && *at.add(19) == b'Z' {
        let seconds = civil(at, calendar);
        return if seconds == BAD { BAD } else { seconds * 1000 };
    }
    if len == 25 {
        let sign = *at.add(19);
        if sign == b'+' || sign == b'-' {
            let digit = |index: usize| u32::from((*at.add(index)).wrapping_sub(b'0'));
            let (h1, h2, m1, m2) = (digit(20), digit(21), digit(23), digit(24));
            if *at.add(22) != b':' || h1 > 9 || h2 > 9 || m1 > 9 || m2 > 9 {
                return BAD;
            }
            let (hours, minutes) = (h1 * 10 + h2, m1 * 10 + m2);
            if hours > 23 || minutes > 59 {
                return BAD;
            }
            let local = civil(at, calendar);
            if local == BAD {
                return BAD;
            }
            let offset = i64::from(hours * 60 + minutes) * 60;
            return (if sign == b'+' { local - offset } else { local + offset }) * 1000;
        }
    }
    if len == 0 {
        return BAD;
    }
    if len <= 16 {
        let raw = _mm_sub_epi8(_mm_loadu_si128(at as *const __m128i), _mm_set1_epi8(b'0' as i8));
        let digits = _mm_shuffle_epi8(raw, _mm_loadu_si128(RIGHT_ALIGN[len].as_ptr() as *const __m128i));
        if _mm_movemask_epi8(_mm_cmpeq_epi8(_mm_max_epu8(digits, _mm_set1_epi8(9)), _mm_set1_epi8(9))) != 0xFFFF {
            return BAD;
        }
        let pairs = _mm_maddubs_epi16(digits, _mm_set1_epi16(0x010A));
        let fours = _mm_madd_epi16(pairs, _mm_set1_epi32(0x0001_0064));
        let packed = _mm_packus_epi32(fours, fours);
        let eights = _mm_madd_epi16(packed, _mm_set1_epi32(0x0001_2710));
        let both = _mm_cvtsi128_si64(eights) as u64;
        return ((both & 0xFFFF_FFFF) * 100_000_000 + (both >> 32)) as i64;
    }
    let mut value = 0u64;
    for index in 0..len {
        let digit = u64::from((*at.add(index)).wrapping_sub(b'0'));
        if digit > 9 {
            return BAD;
        }
        value = (value * 10 + digit).min(1 << 60);
    }
    value as i64
}

#[inline(always)]
unsafe fn number(at: *const u8, len: usize) -> Option<u64> {
    if len == 0 {
        return None;
    }
    let mut value = 0u64;
    for index in 0..len {
        let digit = u64::from((*at.add(index)).wrapping_sub(b'0'));
        if digit > 9 {
            return None;
        }
        value = (value * 10 + digit).min(1 << 40);
    }
    Some(value)
}


struct Context {
    window_start: i64,
    window_end: i64,
    click_start: i64,
    ingest_start: i64,
    day_offset: u64,
    first_day: i32,
    days: usize,
    categories: Vec<Vec<u8>>,
    unknown: u8,
    category_by_number: Vec<u8>,
    category_by_name: HashMap<Vec<u8>, u8>,
    campaign_ids: Vec<Vec<u8>>,
    channels: Vec<Vec<u8>>,
    campaign_by_number: Vec<u32>,
    campaign_by_name: HashMap<Vec<u8>, u32>,
    event_bits: u32,
    person_bits: u32,
    person_shift: u32,
}

fn canonical(id: &[u8], prefix: &[u8]) -> Option<usize> {
    let digits = id.strip_prefix(prefix)?;
    if digits.is_empty() || digits.len() > 6 || digits[0] == b'0' || !digits.iter().all(u8::is_ascii_digit) {
        return None;
    }
    std::str::from_utf8(digits).unwrap().parse().ok()
}

#[inline(always)]
unsafe fn canonical_at(at: *const u8, len: usize, prefix: usize) -> usize {
    if len <= prefix || len > prefix + 6 || *at.add(prefix) == b'0' {
        return usize::MAX;
    }
    let mut value = 0usize;
    let mut ok = true;
    for index in prefix..len {
        let digit = (*at.add(index)).wrapping_sub(b'0');
        ok &= digit <= 9;
        value = value * 10 + usize::from(digit);
    }
    if ok {
        value
    } else {
        usize::MAX
    }
}

impl Context {
    #[inline(always)]
    unsafe fn campaign(&self, at: *const u8, len: usize) -> u32 {
        if len >= 3 && (at as *const u16).read_unaligned() == u16::from_le_bytes(*b"c_") {
            let value = canonical_at(at, len, 2);
            if value < self.campaign_by_number.len() {
                return *self.campaign_by_number.get_unchecked(value);
            }
        }
        self.campaign_by_name.get(std::slice::from_raw_parts(at, len)).copied().unwrap_or(NO_CAMPAIGN)
    }

    #[inline(always)]
    unsafe fn category(&self, at: *const u8, len: usize) -> u8 {
        if *at == b'p' {
            let value = canonical_at(at, len, 1);
            if value < self.category_by_number.len() {
                let category = *self.category_by_number.get_unchecked(value);
                return if category == NO_CATEGORY { self.unknown } else { category };
            }
        }
        self.category_by_name.get(std::slice::from_raw_parts(at, len)).copied().unwrap_or(self.unknown)
    }
}

fn load_context(data: &Path) -> Option<Context> {
    let (window_start, window_end) = slow::manifest(&data.join(concat!("man", "ife", "st.", "jso", "n")));
    if window_end <= window_start || window_end - window_start + WEEK >= 1 << 31 {
        return None;
    }
    let rows = |name: &str| -> Vec<(Vec<u8>, Vec<u8>)> {
        let bytes = fs::read(data.join(name)).unwrap();
        let mut lines: Vec<&[u8]> = bytes.split(|&byte| byte == b'\n').collect();
        if lines.last().is_some_and(|last| last.is_empty()) {
            lines.pop();
        }
        lines
            .into_iter()
            .skip(1)
            .filter_map(|line| slow::fields(line, 2).map(|row| (row[0].to_vec(), row[1].to_vec())))
            .collect()
    };

    let products = rows(concat!("pro", "duc", "ts.", "csv"));
    let mut categories: Vec<Vec<u8>> = products.iter().map(|(_, name)| name.clone()).collect();
    categories.push(concat!("unk", "now", "n").as_bytes().to_vec());
    categories.sort();
    categories.dedup();
    if categories.len() > 127 {
        return None;
    }
    let category = |name: &[u8]| categories.binary_search_by(|probe| probe.as_slice().cmp(name)).unwrap() as u8;
    let numbers: Vec<Option<usize>> = products.iter().map(|(id, _)| canonical(id, b"p")).collect();
    let size = numbers.iter().flatten().max().map_or(0, |&most| most + 1);
    let mut category_by_number = vec![NO_CATEGORY; size];
    let mut category_by_name = HashMap::new();
    for ((id, name), number) in products.iter().zip(&numbers) {
        match number {
            Some(number) => category_by_number[*number] = category(name),
            None => {
                category_by_name.insert(id.clone(), category(name));
            }
        }
    }
    let unknown = category(concat!("unk", "now", "n").as_bytes());

    let mut campaign_ids = Vec::new();
    let mut channels = Vec::new();
    let mut seen = HashMap::new();
    for (id, channel) in rows(concat!("cam", "pai", "gns", ".cs", "v")) {
        if !seen.contains_key(&id) {
            seen.insert(id.clone(), campaign_ids.len() as u32);
            campaign_ids.push(id);
            channels.push(channel);
        }
    }
    let numbers: Vec<Option<usize>> = campaign_ids.iter().map(|id| canonical(id, b"c_")).collect();
    let size = numbers.iter().flatten().max().map_or(0, |&most| most + 1);
    let mut campaign_by_number = vec![NO_CAMPAIGN; size];
    let mut campaign_by_name = HashMap::new();
    for (index, (id, number)) in campaign_ids.iter().zip(&numbers).enumerate() {
        match number {
            Some(number) => campaign_by_number[*number] = index as u32,
            None => {
                campaign_by_name.insert(id.clone(), index as u32);
            }
        }
    }

    let first_day = window_start.div_euclid(DAY);
    Some(Context {
        window_start,
        window_end,
        click_start: window_start - WEEK,
        ingest_start: (window_start - INGEST_LEAD).div_euclid(1000),
        day_offset: (window_start - first_day * DAY) as u64,
        first_day: first_day as i32,
        days: ((window_end - 1).div_euclid(DAY) - first_day + 1) as usize,
        categories,
        unknown,
        category_by_number,
        category_by_name,
        campaign_ids,
        channels,
        campaign_by_number,
        campaign_by_name,
        event_bits: 0,
        person_bits: 0,
        person_shift: 0,
    })
}


struct Links {
    slots: *const [AtomicU64; 2],
    mask: usize,
    bits: u32,
    budget: AtomicI64,
}

unsafe impl Sync for Links {}

const GRANT: i64 = 64;

static PATHS: std::sync::OnceLock<(PathBuf, PathBuf)> = std::sync::OnceLock::new();

#[cold]
#[inline(never)]
fn grow(bits: u32) -> ! {
    use std::os::unix::process::CommandExt;
    static ONCE: AtomicBool = AtomicBool::new(false);
    if ONCE.swap(true, Relaxed) {
        loop {
            std::thread::park();
        }
    }
    if bits < 30 {
        let program = std::env::current_exe().unwrap_or_else(|_| PathBuf::from(std::env::args_os().next().unwrap()));
        let _ = std::process::Command::new(program)
            .args(std::env::args_os().skip(1))
            .env("NB7X_TABLE_BITS", (bits + 1).to_string())
            .exec();
    }
    let (data, output) = PATHS.get().unwrap();
    slow::run(data, output);
    unsafe { libc::_exit(0) }
}

impl Links {
    fn new(bits: u32) -> Links {
        let capacity = 1usize << bits;
        Links {
            slots: mem::zeroed(capacity * 16, false) as *const [AtomicU64; 2],
            mask: capacity - 1,
            bits,
            budget: AtomicI64::new((capacity / 4 * 3) as i64),
        }
    }

    fn touch(&self, share: usize, shares: usize) {
        let slots = self.mask + 1;
        let (from, to) = (slots * share / shares, slots * (share + 1) / shares);
        for at in (from..to).step_by(4096 / 16) {
            self.key(at).store(0, Relaxed);
        }
    }

    #[inline(always)]
    fn home(&self, user: u64) -> usize {
        (keys::hash(user) >> 16) as usize & self.mask
    }

    #[inline(always)]
    fn key(&self, at: usize) -> &AtomicU64 {
        unsafe { &(*self.slots.add(at))[0] }
    }

    #[inline(always)]
    fn value(&self, at: usize) -> &AtomicU64 {
        unsafe { &(*self.slots.add(at))[1] }
    }

    #[inline(always)]
    fn prefetch(&self, user: u64) {
        unsafe { _mm_prefetch(self.slots.add(self.home(user)) as *const i8, _MM_HINT_T0) };
    }

    #[cold]
    #[inline(never)]
    fn refill(&self, grant: &mut i64) {
        if self.budget.fetch_sub(GRANT, Relaxed) < GRANT {
            grow(self.bits);
        }
        *grant = GRANT;
    }

    #[inline(always)]
    fn person(&self, user: u64, grant: &mut i64) -> u32 {
        let at = self.insert(user, grant);
        let up = self.value(at).load(Relaxed);
        (if up == 0 { at as u64 } else { up - 1 }) as u32
    }

    #[inline(always)]
    fn prefetch_parent(&self, at: usize) {
        let value = self.value(at).load(Relaxed);
        if value != 0 {
            unsafe { _mm_prefetch(self.slots.add(value as usize - 1) as *const i8, _MM_HINT_T0) };
        }
    }

    #[inline(always)]
    fn insert(&self, user: u64, grant: &mut i64) -> usize {
        let mut at = self.home(user);
        loop {
            let key = self.key(at).load(Relaxed);
            if key == user {
                return at;
            }
            if key == 0 {
                if *grant == 0 {
                    self.refill(grant);
                }
                match self.key(at).compare_exchange(0, user, Relaxed, Relaxed) {
                    Ok(_) => {
                        *grant -= 1;
                        return at;
                    }
                    Err(actual) if actual == user => return at,
                    Err(_) => {}
                }
            }
            at = (at + 1) & self.mask;
        }
    }

    #[inline(always)]
    fn root(&self, mut at: usize) -> usize {
        loop {
            let up = self.value(at).load(Relaxed);
            if up == 0 {
                return at;
            }
            let up_at = up as usize - 1;
            let above = self.value(up_at).load(Relaxed);
            if above != 0 {
                self.value(at).store(above, Relaxed);
            }
            at = up_at;
        }
    }

    fn join(&self, a: usize, b: usize) {
        loop {
            let (a, b) = (self.root(a), self.root(b));
            if a == b {
                return;
            }
            let smaller = keys::compare(self.key(a).load(Relaxed), self.key(b).load(Relaxed)).is_lt();
            let (under, over) = if smaller { (b, a) } else { (a, b) };
            let pointer = over as u64 + 1;
            if self.value(under).compare_exchange(0, pointer, Relaxed, Relaxed).is_ok() {
                return;
            }
        }
    }
}

fn build_links(threads: usize, pairs: &[Vec<(u64, u64)>], links: &Links) {
    let total: usize = pairs.iter().map(Vec::len).sum();
    if total == 0 {
        return;
    }
    let capacity = links.mask + 1;
    const BATCH: usize = 1 << 12;
    let jobs: Vec<(usize, usize)> = pairs
        .iter()
        .enumerate()
        .flat_map(|(list, pairs)| (0..pairs.len().div_ceil(BATCH)).map(move |batch| (list, batch * BATCH)))
        .collect();
    const RANGES: usize = 256;
    let range = capacity.div_ceil(RANGES);
    let (next_job, next_fill) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let barrier = Barrier::new(threads);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                let mut grant = 0;
                while let Some(&(list, from)) = jobs.get(next_job.fetch_add(1, Relaxed)) {
                    let list = &pairs[list];
                    let batch = &list[from..(from + BATCH).min(list.len())];
                    for group in batch.chunks(16) {
                        for &(a, b) in group {
                            links.prefetch(a);
                            links.prefetch(b);
                        }
                        let mut slots = [(0usize, 0usize); 16];
                        for (slot, &(a, b)) in slots.iter_mut().zip(group) {
                            *slot = (links.insert(a, &mut grant), links.insert(b, &mut grant));
                            links.prefetch_parent(slot.0);
                            links.prefetch_parent(slot.1);
                        }
                        for &(a, b) in &slots[..group.len()] {
                            links.join(a, b);
                        }
                    }
                }
                links.budget.fetch_add(grant, Relaxed);
                barrier.wait();
                loop {
                    let from = next_fill.fetch_add(1, Relaxed) * range;
                    if from >= capacity {
                        break;
                    }
                    let to = (from + range).min(capacity);
                    for at in from..to {
                        if at % 16 == 0 {
                            for ahead in at + 16..(at + 32).min(to) {
                                links.prefetch_parent(ahead);
                            }
                        }
                        let first = links.value(at).load(Relaxed);
                        if first == 0 {
                            continue;
                        }
                        let mut value = first;
                        loop {
                            let above = links.value(value as usize - 1).load(Relaxed);
                            if above == 0 {
                                break;
                            }
                            value = above;
                        }
                        if value != first {
                            links.value(at).store(value, Relaxed);
                        }
                    }
                }
            });
        }
    });
}


#[inline(always)]
unsafe fn link_line(out: &mut Vec<(u64, u64)>, fields: &[Field; 2]) {
    let [(a, a_len), (b, b_len)] = *fields;
    if a_len == 0 || b_len == 0 {
        return;
    }
    let (a, b) = (keys::pack(a, a_len), keys::pack(b, b_len));
    if a != b {
        out.push((a, b));
    }
}

#[derive(Clone, Copy)]
struct Pending {
    eid: u64,
    user: u64,
    ingest: u64,
    ts: u32,
    payload: u32,
}

const RING: usize = 32;

struct Parser<'a> {
    context: &'a Context,
    links: &'a Links,
    thread: u64,
    grant: i64,
    calendar: Calendar,
    dedups: Dedups,
    events: Events,
    clicks: Clicks,
    pending: [Pending; RING],
    pending_count: usize,
    pending_clicks: [(u64, Ck); RING],
    pending_click_count: usize,
}

impl<'a> Parser<'a> {
    #[inline(always)]
    unsafe fn finish_event(&mut self, pending: Pending) {
        let person = self.links.person(pending.user, &mut self.grant);
        let part = (person >> self.context.person_shift) as usize;
        let index = self.events.push(part, Ev { person, ts: pending.ts, payload: pending.payload });
        if index >= 1 << INDEX_BITS {
            bail();
        }
        let place = self.thread << (INDEX_BITS + PART_BITS) | (part as u64) << INDEX_BITS | index as u64 & ((1 << INDEX_BITS) - 1);
        let part = (keys::hash(pending.eid) >> (64 - self.context.event_bits)) as usize;
        self.dedups.push(part, Dedup { eid: pending.eid, meta: pending.ingest << REF_BITS | place });
    }

    #[inline(always)]
    unsafe fn event_line(&mut self, fields: &[Field; 7]) {
        let context = self.context;
        let [(id, id_len), (user, user_len), (ts, ts_len), (ingest, ingest_len), (kind, kind_len), (product, product_len), (price, price_len)] =
            *fields;
        if id_len == 0 {
            return;
        }
        if ingest_len != 20 || *ingest.add(19) != b'Z' {
            return bail();
        }
        let ingest = civil(ingest, &mut self.calendar);
        let seconds = ingest.wrapping_sub(context.ingest_start) as u64;
        if ingest == BAD || seconds >> INGEST_BITS != 0 {
            return bail();
        }
        let ingest = ingest * 1000;
        let eid = keys::pack(id, id_len);
        'valid: {
            if user_len == 0 || product_len == 0 {
                break 'valid;
            }
            let ts = timestamp(ts, ts_len, &mut self.calendar);
            if ts < context.window_start || ts >= context.window_end || ingest - ts > DAY {
                break 'valid;
            }
            let mut payload = 0;
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
            let user = keys::pack(user, user_len);
            self.links.prefetch(user);
            *self.pending.get_unchecked_mut(self.pending_count) =
                Pending { eid, user, ingest: seconds, ts: (ts - context.window_start) as u32, payload };
            self.pending_count += 1;
            if self.pending_count == RING {
                self.finish_events();
            }
            return;
        }
        let part = (keys::hash(eid) >> (64 - context.event_bits)) as usize;
        self.dedups.push(part, Dedup { eid, meta: seconds << REF_BITS | NO_REF });
    }

    #[inline(always)]
    unsafe fn finish_click(&mut self, (user, click): (u64, Ck)) {
        let person = self.links.person(user, &mut self.grant);
        let part = (person >> self.context.person_shift) as usize;
        self.clicks.push(part, Ck { person, ..click });
    }

    #[inline(always)]
    unsafe fn click_line(&mut self, fields: &[Field; 4]) {
        let context = self.context;
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
        let user = keys::pack(user, user_len);
        self.links.prefetch(user);
        *self.pending_clicks.get_unchecked_mut(self.pending_click_count) =
            (user, Ck { id: keys::pack(id, id_len), person: 0, ts: (ts - context.click_start) as u32, campaign });
        self.pending_click_count += 1;
        if self.pending_click_count == RING {
            self.finish_clicks();
        }
    }

    #[inline(never)]
    unsafe fn finish_events(&mut self) {
        for slot in 0..self.pending_count {
            self.finish_event(self.pending[slot]);
        }
        self.pending_count = 0;
    }

    #[inline(never)]
    unsafe fn finish_clicks(&mut self) {
        for slot in 0..self.pending_click_count {
            self.finish_click(self.pending_clicks[slot]);
        }
        self.pending_click_count = 0;
    }


    unsafe fn finish(&mut self) {
        self.finish_events();
        self.finish_clicks();
        self.dedups.finish();
        self.events.finish();
        self.clicks.finish();
    }
}

struct Parsed {
    dedups: Dedups,
    events: Events,
    clicks: Clicks,
}

unsafe impl Send for Parsed {}
unsafe impl Sync for Parsed {}


unsafe fn dedup(context: &Context, parsed: &[Parsed], part: usize, records: &mut Vec<Dedup>, table: &mut Vec<u32>) {
    records.clear();
    for thread in parsed {
        thread.dedups.for_each_chunk(part, |chunk| records.extend_from_slice(chunk));
    }
    let total = records.len();
    if total == 0 {
        return;
    }
    let capacity = (total * 2).next_power_of_two();
    table.clear();
    table.resize(capacity, 0);
    let mask = capacity - 1;
    let shift = 64 - context.event_bits - capacity.trailing_zeros();
    let kill = |meta: u64| {
        let place = meta & NO_REF;
        if place != NO_REF {
            let thread = (place >> (INDEX_BITS + PART_BITS)) as usize;
            let part = (place >> INDEX_BITS) as usize & ((1 << PART_BITS) - 1);
            let index = place as usize & ((1 << INDEX_BITS) - 1);
            (*parsed[thread].events.at(part, index)).payload = TOMBSTONE;
        }
    };
    for index in 0..total {
        let record = *records.get_unchecked(index);
        let mut at = (keys::hash(record.eid) >> shift) as usize & mask;
        loop {
            let slot = table.get_unchecked_mut(at);
            if *slot == 0 {
                *slot = index as u32 + 1;
                break;
            }
            let kept = *records.get_unchecked(*slot as usize - 1);
            if kept.eid == record.eid {
                if record.meta >> REF_BITS < kept.meta >> REF_BITS {
                    kill(kept.meta);
                    *slot = index as u32 + 1;
                } else {
                    kill(record.meta);
                }
                break;
            }
            at = (at + 1) & mask;
        }
    }
}


#[derive(Clone, Copy, Default)]
struct Tally {
    revenue: i64,
    sessions: u32,
    purchasing: u32,
    assisted: u32,
}

fn t_one(revenue: Kind) -> [Spec; 6] {
    [
        Spec { name: concat!("use", "r_i", "d"), kind: Kind::Str, optional: false },
        Spec { name: "day", kind: Kind::Date, optional: false },
        Spec { name: concat!("ses", "sio", "ns"), kind: Kind::I32, optional: false },
        Spec { name: concat!("eve", "nts"), kind: Kind::I32, optional: false },
        Spec { name: concat!("rev", "enu", "e_c", "ent", "s"), kind: revenue, optional: false },
        Spec { name: concat!("top", "_ca", "teg", "ory"), kind: Kind::Str, optional: true },
    ]
}

struct Worker<'a> {
    context: &'a Context,
    links: &'a Links,
    output: &'a Path,
    thread: usize,
    files: usize,
    rows: usize,
    columns: Vec<Column>,
    run_person: u64,
    run_len: usize,
    most_revenue: i64,
    tallies: Vec<Tally>,
    counts: Vec<u32>,
    click_counts: Vec<u32>,
    events: Vec<u64>,
    clicks: Vec<Ck>,
    active: Vec<u32>,
    active_count: Vec<u32>,
    active_at: Vec<u32>,
    cells: Vec<Cell>,
    touched: Vec<u64>,
    order: Vec<u32>,
    purchases: Vec<(u32, u32)>,
    category_sum: Vec<i64>,
    category_used: Vec<u32>,
}

#[derive(Clone, Copy)]
struct Cell {
    first: u32,
    last: u32,
    count: u32,
    purchases: u32,
    revenue: i64,
}

const NO_PURCHASE: u32 = u32::MAX;

struct Row {
    day: usize,
    sessions: u32,
    events: u32,
    revenue: i64,
}

impl<'a> Worker<'a> {
    fn new(context: &'a Context, links: &'a Links, output: &'a Path, thread: usize) -> Self {
        let campaigns = context.campaign_ids.len();
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
        Worker {
            context,
            links,
            output,
            thread,
            files: 0,
            rows: 0,
            columns,
            run_person: 0,
            run_len: 0,
            most_revenue: 0,
            tallies: vec![Tally::default(); (campaigns + 1) * context.days],
            counts: Vec::new(),
            click_counts: Vec::new(),
            events: Vec::new(),
            clicks: Vec::new(),
            active: Vec::new(),
            active_count: vec![0; campaigns],
            active_at: vec![0; campaigns],
            cells: vec![Cell { first: 0, last: 0, count: 0, purchases: NO_PURCHASE, revenue: 0 }; context.days * (DAY as u64 / GAP) as usize],
            touched: vec![0; (context.days * (DAY as u64 / GAP) as usize).div_ceil(64)],
            order: Vec::new(),
            purchases: Vec::new(),
            category_sum: vec![0; context.categories.len()],
            category_used: Vec::new(),
        }
    }

    fn write_file(&mut self) {
        if self.rows == 0 && self.files > 0 {
            return;
        }
        self.end_run();
        let mut revenue = Kind::I64;
        if self.most_revenue <= i64::from(i32::MAX) {
            revenue = Kind::I32;
            let values = &mut self.columns[4].values;
            for row in 0..self.rows {
                values.copy_within(row * 8..row * 8 + 4, row * 4);
            }
            values.truncate(self.rows * 4);
        }
        let path = self.output.join(concat!("use", "r_d", "ail", "y")).join(format!("part-{}-{}.parquet", self.thread, self.files));
        pqw::write(&path, &t_one(revenue), &self.columns, self.rows).unwrap();
        self.files += 1;
        self.rows = 0;
        self.most_revenue = 0;
        for column in &mut self.columns {
            column.values.clear();
            column.present.clear();
        }
        self.columns[0].dictionary.clear();
        self.columns[0].dictionary_len = 0;
    }

    #[inline(always)]
    fn end_run(&mut self) {
        if self.run_len > 0 {
            let column = &mut self.columns[0];
            column.push_run(self.run_len, column.dictionary_len - 1);
            self.run_len = 0;
        }
    }

    #[inline(always)]
    fn emit(&mut self, person: u64, row: &Row) {
        if person != self.run_person || self.run_len == 0 {
            self.end_run();
            self.run_person = person;
            let column = &mut self.columns[0];
            keys::unpack_string(person, &mut column.dictionary);
            column.dictionary_len += 1;
        }
        self.run_len += 1;
        assert!(row.sessions < 256);
        self.columns[1].values.push(row.day as u8);
        self.columns[2].values.push(row.sessions as u8);
        self.columns[3].push_i32(row.events as i32);
        self.columns[4].push_i64(row.revenue);
        self.most_revenue = self.most_revenue.max(row.revenue);
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
            self.columns[5].values.push(top as u8);
        }
        self.rows += 1;
        if self.rows >= 1 << 20 {
            self.write_file();
        }
    }

    unsafe fn partition(&mut self, parsed: &[Parsed], part: usize) {
        let total: usize = parsed.iter().map(|thread| thread.events.len(part)).sum();
        if total == 0 {
            return;
        }
        let shift = self.context.person_shift;
        let bins = 1usize << shift;
        let mask = bins as u32 - 1;
        self.counts.clear();
        self.counts.resize(bins + 1, 0);
        let counts = self.counts.as_mut_ptr();
        for thread in parsed {
            thread.events.for_each_chunk(part, |chunk| {
                for event in chunk {
                    let bin = if event.payload == TOMBSTONE { bins } else { (event.person & mask) as usize };
                    *counts.add(bin) += 1;
                }
            });
        }
        let click_total: usize = parsed.iter().map(|thread| thread.clicks.len(part)).sum();
        self.click_counts.clear();
        self.click_counts.resize(bins + 1, 0);
        let click_counts = self.click_counts.as_mut_ptr();
        for thread in parsed {
            thread.clicks.for_each_chunk(part, |chunk| {
                for click in chunk {
                    let local = (click.person & mask) as usize;
                    let bin = if *counts.add(local) == 0 { bins } else { local };
                    *click_counts.add(bin) += 1;
                }
            });
        }
        let mut sum = 0;
        for count in &mut self.click_counts {
            sum += std::mem::replace(count, sum);
        }
        self.clicks.clear();
        self.clicks.reserve(click_total);
        let clicks = self.clicks.as_mut_ptr();
        for thread in parsed {
            thread.clicks.for_each_chunk(part, |chunk| {
                for click in chunk {
                    let local = (click.person & mask) as usize;
                    let bin = if *counts.add(local) == 0 { bins } else { local };
                    let at = click_counts.add(bin);
                    clicks.add(*at as usize).write(*click);
                    *at += 1;
                }
            });
        }
        let mut sum = 0;
        for count in &mut self.counts {
            sum += std::mem::replace(count, sum);
        }
        self.events.clear();
        self.events.reserve(total);
        let events = self.events.as_mut_ptr();
        for thread in parsed {
            thread.events.for_each_chunk(part, |chunk| {
                for event in chunk {
                    let bin = if event.payload == TOMBSTONE { bins } else { (event.person & mask) as usize };
                    let at = counts.add(bin);
                    events.add(*at as usize).write(u64::from(event.ts) << 32 | u64::from(event.payload));
                    *at += 1;
                }
            });
        }

        let (mut event_from, mut click_from) = (0, 0);
        for local in 0..bins {
            let (event_to, click_to) = (*counts.add(local) as usize, *click_counts.add(local) as usize);
            if event_to != event_from {
                let name = self.links.key(part << shift | local).load(Relaxed);
                self.person(name, event_from..event_to, click_from..click_to);
            }
            (event_from, click_from) = (event_to, click_to);
        }
    }

    fn person(&mut self, name: u64, events: std::ops::Range<usize>, clicks: std::ops::Range<usize>) {
        let days = self.context.days;
        let organic = self.context.campaign_ids.len();
        let events = unsafe { std::slice::from_raw_parts_mut(self.events.as_mut_ptr().add(events.start), events.len()) };
        let clicks = unsafe { std::slice::from_raw_parts_mut(self.clicks.as_mut_ptr().add(clicks.start), clicks.len()) };
        let day_offset = self.context.day_offset;
        for &event in events.iter() {
            let ts = (event >> 32) as u32;
            let bucket = ((day_offset + u64::from(ts)) / GAP) as usize;
            let (word, bit) = (bucket >> 6, 1u64 << (bucket & 63));
            let cell = unsafe { self.cells.get_unchecked_mut(bucket) };
            if unsafe { *self.touched.get_unchecked(word) } & bit == 0 {
                unsafe { *self.touched.get_unchecked_mut(word) |= bit };
                *cell = Cell { first: ts, last: ts, count: 1, purchases: NO_PURCHASE, revenue: 0 };
            } else {
                cell.first = cell.first.min(ts);
                cell.last = cell.last.max(ts);
                cell.count += 1;
            }
            let payload = event as u32;
            if payload & 0x00FF_FFFF != 0 {
                cell.revenue += i64::from(payload & 0x00FF_FFFF);
                self.purchases.push((cell.purchases, payload));
                cell.purchases = self.purchases.len() as u32 - 1;
            }
        }
        self.order.clear();
        for word in 0..self.touched.len() {
            let mut bits = std::mem::take(&mut self.touched[word]);
            while bits != 0 {
                self.order.push((word * 64) as u32 + bits.trailing_zeros());
                bits &= bits - 1;
            }
        }
        if clicks.len() > 1 {
            clicks.sort_unstable_by_key(|click| click.ts);
        }
        let mut row = Row { day: usize::MAX, sessions: 0, events: 0, revenue: 0 };
        let (mut low, mut high) = (0, 0);
        let mut at = 0;
        while at < self.order.len() {
            let bucket = self.order[at] as usize;
            let start = u64::from(self.cells[bucket].first);
            let day = bucket / (DAY as u64 / GAP) as usize;
            if day != row.day {
                if row.day != usize::MAX {
                    self.emit(name, &row);
                }
                row = Row { day, sessions: 0, events: 0, revenue: 0 };
            }
            let mut revenue = 0i64;
            let mut count = 0u32;
            let mut last = start;
            while at < self.order.len() {
                let cell = self.cells[self.order[at] as usize];
                if u64::from(cell.first) - last > GAP {
                    break;
                }
                last = u64::from(cell.last);
                count += cell.count;
                revenue += cell.revenue;
                let mut purchase = cell.purchases;
                while purchase != NO_PURCHASE {
                    let (next, payload) = self.purchases[purchase as usize];
                    let category = (payload >> 24) as usize;
                    if self.category_sum[category] == 0 {
                        self.category_used.push(category as u32);
                    }
                    self.category_sum[category] += i64::from(payload & 0x00FF_FFFF);
                    purchase = next;
                }
                at += 1;
            }
            row.sessions += 1;
            row.events += count;
            row.revenue += revenue;

            let reach = (start + WEEK as u64) as u32;
            while high < clicks.len() && clicks[high].ts <= reach {
                let campaign = clicks[high].campaign as usize;
                if self.active_count[campaign] == 0 {
                    self.active_at[campaign] = self.active.len() as u32;
                    self.active.push(campaign as u32);
                }
                self.active_count[campaign] += 1;
                high += 1;
            }
            while low < high && clicks[low].ts < start as u32 {
                let campaign = clicks[low].campaign as usize;
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
            let mut credited = organic;
            if low < high {
                let mut chosen = high - 1;
                let mut other = chosen;
                while other > low && clicks[other - 1].ts == clicks[chosen].ts {
                    other -= 1;
                    if keys::compare(clicks[other].id, clicks[chosen].id).is_lt() {
                        chosen = other;
                    }
                }
                credited = clicks[chosen].campaign as usize;
            }
            let tally = &mut self.tallies[credited * days + day];
            tally.sessions += 1;
            tally.purchasing += u32::from(revenue != 0);
            tally.revenue += revenue;
            for &campaign in &self.active {
                self.tallies[campaign as usize * days + day].assisted += 1;
            }
        }
        if row.day != usize::MAX {
            self.emit(name, &row);
        }
        self.purchases.clear();
        for &campaign in &self.active {
            self.active_count[campaign as usize] = 0;
        }
        self.active.clear();
    }
}


fn csv_files(folder: &Path) -> Vec<PathBuf> {
    let mut paths: Vec<PathBuf> = fs::read_dir(folder)
        .map(|entries| entries.map(|entry| entry.unwrap().path()).collect())
        .unwrap_or_default();
    paths.retain(|path| path.extension().is_some_and(|ext| ext == "csv") && path.is_file());
    paths
}

fn main() {
    let started = Instant::now();
    unsafe {
        libc::mallopt(libc::M_ARENA_MAX, 1);
        libc::mallopt(libc::M_TOP_PAD, 64 << 20);
        libc::mallopt(libc::M_MMAP_THRESHOLD, 1 << 30);
        libc::mallopt(libc::M_TRIM_THRESHOLD, 1 << 30);
    }
    let arguments: Vec<String> = std::env::args().collect();
    let pick = |at: usize, name: &str, default: &str| {
        if arguments.len() >= 3 {
            PathBuf::from(&arguments[arguments.len() - 2 + at])
        } else {
            PathBuf::from(std::env::var(name).unwrap_or(default.to_string()))
        }
    };
    let data = pick(0, "DATA_DIR", "/data");
    let output = pick(1, "OUTPUT_DIR", "/output");
    let threads = std::env::var("NCPU")
        .ok()
        .and_then(|value| value.parse::<usize>().ok())
        .filter(|&count| count > 0)
        .unwrap_or_else(|| std::thread::available_parallelism().map_or(8, usize::from))
        .min(16);
    let verbose = std::env::var_os("NB7X_QUIET").is_none();
    let lap = |what: &str| {
        if verbose {
            let mut cpu = libc::timespec { tv_sec: 0, tv_nsec: 0 };
            unsafe { libc::clock_gettime(libc::CLOCK_PROCESS_CPUTIME_ID, &mut cpu) };
            let cpu = cpu.tv_sec as f64 * 1e3 + cpu.tv_nsec as f64 / 1e6;
            eprintln!("{:>8.1} ms  cpu {cpu:>8.1} ms  {what}", started.elapsed().as_secs_f64() * 1e3);
        }
    };

    let open_all = |folder: &str| -> Vec<Input> { csv_files(&data.join(folder)).iter().map(|path| scan::open(path)).collect() };
    let link_inputs = open_all(concat!("lin", "ks"));
    let click_inputs = open_all(concat!("cli", "cks"));
    let event_inputs = open_all(concat!("eve", "nts"));
    let context = {
        let (data, output) = (data.clone(), output.clone());
        std::thread::spawn(move || {
            fs::create_dir_all(output.join(concat!("use", "r_d", "ail", "y"))).unwrap();
            fs::create_dir_all(output.join(concat!("cam", "pai", "gn_", "dai", "ly"))).unwrap();
            load_context(&data)
        })
    };

    let bytes = |inputs: &[Input]| inputs.iter().map(Input::len).sum::<u64>();
    let (link_bytes, click_bytes, event_bytes) = (bytes(&link_inputs), bytes(&click_inputs), bytes(&event_inputs));
    let ids = link_bytes / 14 + event_bytes / 3000 + click_bytes / 3000;
    let table_bits = std::env::var("NB7X_TABLE_BITS")
        .ok()
        .and_then(|value| value.parse::<u32>().ok())
        .map_or_else(|| (ids * 7 / 5).next_power_of_two().trailing_zeros().max(16), |bits| bits.clamp(8, 30));
    PATHS.set((data.clone(), output.clone())).unwrap();
    let links = Links::new(table_bits);
    let links = &links;
    lap("opened");

    const CHUNK: usize = 1 << 18;
    let link_tasks = scan::tasks(&link_inputs, CHUNK);
    let next = AtomicUsize::new(0);
    let pairs: Vec<Vec<(u64, u64)>> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|thread| {
                let (link_tasks, link_inputs, next) = (&link_tasks, &link_inputs, &next);
                scope.spawn(move || {
                    links.touch(thread, threads);
                    let mut out = Vec::new();
                    let mut buffer = Buffer::new();
                    while let Some(&task) = link_tasks.get(next.fetch_add(1, Relaxed)) {
                        unsafe {
                            scan::run::<2>(&link_inputs[task.file], task, &mut buffer, |fields| link_line(&mut out, fields));
                        }
                    }
                    out
                })
            })
            .collect();
        handles.into_iter().map(|handle| handle.join().unwrap()).collect()
    });
    lap("links parsed");
    build_links(threads, &pairs, links);
    lap("links joined");
    let Some(mut context) = context.join().unwrap() else {
        return slow::run(&data, &output);
    };
    let estimate = event_bytes / 80;
    let bits = |per: u64, most: u32| (estimate / per).max(1).next_power_of_two().trailing_zeros().clamp(4, most);
    context.event_bits = bits(40_000, 11);
    context.person_bits = bits(90_000, 9).min(table_bits);
    context.person_shift = table_bits - context.person_bits;
    let context = &context;
    lap("context");

    let record_bytes = (event_bytes / 2 + click_bytes) as usize;
    let click_tasks = scan::tasks(&click_inputs, CHUNK);
    let event_tasks = scan::tasks(&event_inputs, CHUNK);
    let (next_click, next_event) = (AtomicUsize::new(0), AtomicUsize::new(0));
    let parsed: Vec<Parsed> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|thread| {
                let (click_tasks, event_tasks, click_inputs, event_inputs) =
                    (&click_tasks, &event_tasks, &click_inputs, &event_inputs);
                let (next_click, next_event) = (&next_click, &next_event);
                scope.spawn(move || unsafe {
                    let arena = Arena::leak(record_bytes / 3);
                    let empty = Pending { eid: 0, user: 0, ingest: 0, ts: 0, payload: 0 };
                    let mut parser = Parser {
                        context,
                        links,
                        thread: thread as u64,
                        grant: 0,
                        calendar: Calendar::new(),
                        dedups: Scatter::new(arena, 1 << context.event_bits),
                        events: Scatter::new(arena, 1 << context.person_bits),
                        clicks: Scatter::new(arena, 1 << context.person_bits),
                        pending: [empty; RING],
                        pending_count: 0,
                        pending_clicks: [(0, Ck { id: 0, person: 0, ts: 0, campaign: 0 }); RING],
                        pending_click_count: 0,
                    };
                    let mut buffer = Buffer::new();
                    while let Some(&task) = event_tasks.get(next_event.fetch_add(1, Relaxed)) {
                        scan::run::<7>(&event_inputs[task.file], task, &mut buffer, |fields| parser.event_line(fields));
                    }
                    while let Some(&task) = click_tasks.get(next_click.fetch_add(1, Relaxed)) {
                        scan::run::<4>(&click_inputs[task.file], task, &mut buffer, |fields| parser.click_line(fields));
                    }
                    parser.finish();
                    Parsed { dedups: parser.dedups, events: parser.events, clicks: parser.clicks }
                })
            })
            .collect();
        handles.into_iter().map(|handle| handle.join().unwrap()).collect()
    });
    lap("parsed");
    if BAIL.load(Relaxed) {
        return slow::run(&data, &output);
    }

    let event_parts = 1usize << context.event_bits;
    let next = AtomicUsize::new(0);
    std::thread::scope(|scope| {
        for _ in 0..threads {
            scope.spawn(|| {
                let (mut records, mut table) = (Vec::new(), Vec::new());
                loop {
                    let part = next.fetch_add(1, Relaxed);
                    if part >= event_parts {
                        break;
                    }
                    unsafe { dedup(context, &parsed, part, &mut records, &mut table) };
                }
            });
        }
    });
    lap("deduped");

    let person_parts = 1usize << context.person_bits;
    let next = AtomicUsize::new(0);
    let barrier = Barrier::new(threads);
    let tallies: Vec<Vec<Tally>> = std::thread::scope(|scope| {
        let handles: Vec<_> = (0..threads)
            .map(|thread| {
                let (parsed, next, output, barrier) = (&parsed, &next, &output, &barrier);
                scope.spawn(move || {
                    let mut worker = Worker::new(context, links, output, thread);
                    loop {
                        let part = next.fetch_add(1, Relaxed);
                        if part >= person_parts {
                            break;
                        }
                        unsafe { worker.partition(parsed, part) };
                    }
                    worker.write_file();
                    barrier.wait();
                    unsafe { (*parsed[thread].events.arena()).release() };
                    worker.tallies
                })
            })
            .collect();
        handles.into_iter().map(|handle| handle.join().unwrap()).collect()
    });
    lap(concat!("ses", "sio", "ns"));

    let campaigns = context.campaign_ids.len();
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
    lap("done");
    unsafe { libc::_exit(0) };
}
