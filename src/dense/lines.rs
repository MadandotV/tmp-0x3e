

use std::arch::x86_64::*;
use std::fs;
use std::path::Path;

use super::super::{Calendar, BAD};
use super::codec::decode2;
use super::stamp::{civil, timestamp};

pub struct Input {
    file: fs::File,
    len: usize,
}

impl Input {
    pub fn len(&self) -> u64 {
        self.len as u64
    }
}

pub fn open(path: &Path) -> Input {
    let file = fs::File::open(path).unwrap();
    let len = file.metadata().unwrap().len() as usize;
    Input { file, len }
}

#[derive(Clone, Copy)]
pub struct Task {
    pub file: usize,
    from: usize,
    to: usize,
}

pub fn tasks(inputs: &[Input], chunk: usize) -> Vec<Task> {
    let mut out = Vec::new();
    for (file, input) in inputs.iter().enumerate() {
        let mut from = 0;
        while from < input.len {
            let to = (from + chunk).min(input.len);
            out.push(Task { file, from, to });
            from = to;
        }
    }
    out.sort_by_key(|task| std::cmp::Reverse(task.to - task.from));
    out
}

const OVERHANG: usize = 4096;
const PAD: usize = 256;

pub struct Buffer {
    bytes: Vec<u8>,
}

impl Buffer {
    pub fn new() -> Self {
        Buffer { bytes: Vec::new() }
    }

    unsafe fn fill(&mut self, input: &Input, task: Task) -> (usize, usize) {
        use std::os::fd::AsRawFd;
        let fd = input.file.as_raw_fd();
        let origin = task.from.saturating_sub(1);
        let mut want = (task.to + OVERHANG).min(input.len) - origin;
        let mut have = 0;
        loop {
            if self.bytes.len() < want + PAD {
                self.bytes.resize(want + PAD, 0);
            }
            while have < want {
                let got = libc::pread(
                    fd,
                    self.bytes.as_mut_ptr().add(have) as *mut libc::c_void,
                    want - have,
                    (origin + have) as libc::off_t,
                );
                assert!(got > 0, "read failed");
                have += got as usize;
            }
            let mut start = 0;
            if task.from > 0 {
                while start < have && self.bytes[start] != b'\n' {
                    start += 1;
                }
                start += 1;
                if start >= task.to - origin {
                    return (0, 0);
                }
            }
            let mut end = task.to - origin;
            if task.to < input.len {
                end -= 1;
                while end < have && self.bytes[end] != b'\n' {
                    end += 1;
                }
                if end == have && origin + have < input.len {
                    want = (want * 2).min(input.len - origin);
                    continue;
                }
                end = (end + 1).min(have);
            }
            if start >= end {
                return (0, 0);
            }
            if self.bytes[end - 1] != b'\n' {
                self.bytes[end] = b'\n';
                end += 1;
            }
            return (start, end);
        }
    }
}

pub type Field = (*const u8, usize);

#[inline(always)]
unsafe fn masks(at: *const u8) -> (u64, u64, u64) {
    let low = _mm256_loadu_si256(at as *const __m256i);
    let high = _mm256_loadu_si256(at.add(32) as *const __m256i);
    let mask = |needle: u8| {
        let needle = _mm256_set1_epi8(needle as i8);
        u64::from(_mm256_movemask_epi8(_mm256_cmpeq_epi8(low, needle)) as u32)
            | u64::from(_mm256_movemask_epi8(_mm256_cmpeq_epi8(high, needle)) as u32) << 32
    };
    (mask(b','), mask(b'\n'), mask(b'"'))
}

#[inline(always)]
unsafe fn take<const K: usize>(at: *const u8, last: bool, out: &mut [Field]) -> usize {
    let (commas, newlines, quotes) = masks(at);
    let separators = commas | newlines;
    let end = _pdep_u64(1 << (K - 1), separators);
    let upto = end | end.wrapping_sub(1);
    let within = quotes & upto;
    let opening = within & (separators << 1 | 1);
    let closing = within & (separators >> 1);
    let opens = _pext_u64(quotes >> 1, separators) << 1 | quotes & 1;
    let closes = _pext_u64(quotes << 1, separators);
    let fields = (1u64 << K) - 1;
    let wrong = (within & !opening & !closing)
        | (opening & closing)
        | ((opens ^ closes) & fields)
        | ((newlines & upto) ^ if last { end } else { 0 });
    if end == 0 || wrong != 0 {
        return 0;
    }
    let mut rest = separators;
    let mut from = 0usize;
    for index in 0..K {
        let to = rest.trailing_zeros() as usize;
        rest &= rest - 1;
        let strip = (opens >> index) as usize & 1;
        *out.get_unchecked_mut(index) = (at.add(from + strip), to - from - 2 * strip);
        from = to + 1;
    }
    from
}

#[cold]
#[inline(never)]
unsafe fn slow_line<const N: usize>(at: *const u8, out: &mut [Field; N]) -> (usize, bool) {
    let mut len = 0;
    while *at.add(len) != b'\n' {
        len += 1;
    }
    let line = std::slice::from_raw_parts(at, len);
    let mut count = 0;
    let mut ok = len > 0;
    for field in line.split(|&byte| byte == b',') {
        let quotes = field.iter().filter(|&&byte| byte == b'"').count();
        let wrapped = quotes == 2 && field.len() >= 2 && field[0] == b'"' && field[field.len() - 1] == b'"';
        if count < N {
            out[count] = if wrapped { (field.as_ptr().add(1), field.len() - 2) } else { (field.as_ptr(), field.len()) };
        }
        ok &= quotes == 0 || wrapped;
        count += 1;
    }
    (len + 1, ok && count == N)
}

#[inline(always)]
pub unsafe fn split(at: *const u8) -> (usize, Option<[Field; 7]>) {
    let mut fields: [Field; 7] = [(std::ptr::null(), 0); 7];
    let first = take::<3>(at, false, &mut fields[..3]);
    let second = take::<4>(at.add(first), true, &mut fields[3..]);
    if first != 0 && second != 0 {
        return (first + second, Some(fields));
    }
    let (len, ok) = slow_line(at, &mut fields);
    (len, ok.then_some(fields))
}

pub struct Fused {
    pub id: Field,
    pub user: Field,
    pub event: u64,
    pub who: u64,
    pub ts: i64,
    pub ingest: i64,
    pub purchase: bool,
    pub product: Field,
    pub price: Field,
}

#[inline(always)]
pub unsafe fn fused(at: *const u8, calendar: &mut Calendar) -> Option<(usize, Fused)> {
    let (commas, _, quotes) = masks(at);
    let c0 = commas.trailing_zeros() as usize;
    let after = commas & commas.wrapping_sub(1);
    let c1 = after.trailing_zeros() as usize;
    let third = after & after.wrapping_sub(1);
    let c2 = third.trailing_zeros() as usize;
    let open = quotes & 1 | (_pext_u64(quotes >> 1, commas) & 3) << 1;
    let close = _pext_u64(quotes << 1, commas) & 7;
    let wrapped = |field: u32| (open >> field) as usize & 1;
    let mut odd = (open ^ close) | u64::from(third == 0);
    let id: Field = (at.add(wrapped(0)), c0.wrapping_sub(2 * wrapped(0)));
    let user: Field = (at.add(c0 + 1 + wrapped(1)), c1.wrapping_sub(c0 + 1 + 2 * wrapped(1)));
    let (ids, event, who) = decode2::<b'e', b'u'>(id.0, id.1, user.0, user.1);
    let ts_len = c2.wrapping_sub(c1 + 1 + 2 * wrapped(2));
    let ts = timestamp(at.add(c1 + 1 + wrapped(2)), if ts_len > 64 { 0 } else { ts_len }, calendar);

    let tail = at.add(c2 + 1);
    let (commas, newlines, quotes) = masks(tail);
    let end = newlines.trailing_zeros() as usize;
    let line_end = newlines & newlines.wrapping_neg();
    let below = line_end.wrapping_sub(1);
    let inside = commas & below;
    let k0 = inside.trailing_zeros() as usize;
    let last_two = inside & inside.wrapping_sub(1);
    let k1 = last_two.trailing_zeros() as usize;
    let last = last_two & last_two.wrapping_sub(1);
    let k2 = last.trailing_zeros() as usize;
    let ends = inside | line_end;
    let open = quotes & 1 | (_pext_u64(quotes >> 1, ends) & 7) << 1;
    let close = _pext_u64(quotes << 1, ends) & 15;
    let wrapped = |field: u32| (open >> field) as usize & 1;
    let ingest_len = k0.wrapping_sub(2 * wrapped(0));
    let ingest = civil::<1>(tail.add(wrapped(0)), calendar);
    let kind_len = k1.wrapping_sub(k0 + 1 + 2 * wrapped(1));
    let kind = tail.add(k0 + 1 + wrapped(1));
    let purchase = (kind_len == 8) & ((kind as *const u64).read_unaligned() == u64::from_le_bytes(*b"purchase"));
    let word = (kind as *const u32).read_unaligned();
    let browse = (kind_len == 4) & ((word == u32::from_le_bytes(*b"view")) | (word == u32::from_le_bytes(*b"cart")));
    let product_len = k2.wrapping_sub(k1 + 1 + 2 * wrapped(2));
    let price_len = end.wrapping_sub(k2 + 1 + 2 * wrapped(3));
    let their_quotes = quotes & below & !(last_two & last_two.wrapping_neg()).wrapping_sub(1);
    odd |= (open ^ close)
        | u64::from((last == 0) | (last & last.wrapping_sub(1) != 0))
        | u64::from(newlines == 0)
        | u64::from(their_quotes.count_ones() as usize != 2 * (wrapped(2) + wrapped(3)))
        | u64::from(ingest_len != 20)
        | u64::from(product_len == 0)
        | (product_len | price_len) as u64 >> 63
        | u64::from(!ids | (ingest == BAD) | (ts == BAD) | !(purchase | browse));
    if odd != 0 {
        return None;
    }
    let product: Field = (tail.add(k1 + 1 + wrapped(2)), product_len);
    let price: Field = (tail.add(k2 + 1 + wrapped(3)), price_len);
    Some((c2 + 1 + end + 1, Fused { id, user, event, who, ts, ingest, purchase, product, price }))
}
pub trait Events {
    fn calendar(&mut self) -> &mut Calendar;
    unsafe fn fused(&mut self, line: &Fused);
    unsafe fn plain(&mut self, fields: &[Field; 7]);
}

pub unsafe fn run_plain(input: &Input, task: Task, buffer: &mut Buffer, sink: &mut impl Events) {
    let (mut from, to) = buffer.fill(input, task);
    let base = buffer.bytes.as_ptr();
    if task.from == 0 {
        while from < to && *base.add(from) != b'\n' {
            from += 1;
        }
        from += 1;
    }
    while from < to {
        let (len, fields) = split(base.add(from));
        if let Some(fields) = fields {
            sink.plain(&fields);
        }
        from += len;
    }
}

#[inline(always)]
pub unsafe fn run_events(input: &Input, task: Task, buffer: &mut Buffer, sink: &mut impl Events) {
    let (mut from, to) = buffer.fill(input, task);
    let base = buffer.bytes.as_ptr();
    if task.from == 0 {
        while from < to && *base.add(from) != b'\n' {
            from += 1;
        }
        from += 1;
    }
    while from < to {
        let at = base.add(from);
        if let Some((len, line)) = fused(at, sink.calendar()) {
            sink.fused(&line);
            from += len;
        } else {
            from += other(at, sink);
        }
    }
}

#[cold]
#[inline(never)]
unsafe fn other(at: *const u8, sink: &mut impl Events) -> usize {
    let (len, fields) = split(at);
    if let Some(fields) = fields {
        sink.plain(&fields);
    }
    len
}
