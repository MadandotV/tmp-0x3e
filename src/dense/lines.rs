

use std::arch::x86_64::*;

use super::rows::{self, Click, Days, Rows, NO_CLICK};

pub use super::super::source::{open, Source as Input};

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
const LEAD: usize = 64;

pub struct Buffer {
    bytes: Vec<u8>,
    base: *const u8,
    held: (usize, usize),
}

impl Buffer {
    pub fn new() -> Self {
        Buffer { bytes: Vec::new(), base: std::ptr::null(), held: (0, 0) }
    }

    unsafe fn fill(&mut self, input: &Input, task: Task) -> (usize, usize) {
        use std::os::fd::AsRawFd;
        super::super::source::release(self.held.0, self.held.1);
        self.held = (0, 0);
        if let Some((base, start, end)) = input.window(task.from, task.to) {
            self.base = base;
            self.held = (base as usize + start, base as usize + end);
            return (start, end);
        }
        let fd = input.file.as_ref().unwrap().as_raw_fd();
        let origin = task.from.saturating_sub(1);
        let mut want = (task.to + OVERHANG).min(input.len) - origin;
        let mut have = 0;
        loop {
            if self.bytes.len() < LEAD + want + PAD {
                self.bytes.resize(LEAD + want + PAD, 0);
            }
            let bytes = std::slice::from_raw_parts_mut(self.bytes.as_mut_ptr().add(LEAD), want + PAD);
            self.base = bytes.as_ptr();
            while have < want {
                let got = libc::pread(fd, bytes.as_mut_ptr().add(have) as *mut libc::c_void, want - have, (origin + have) as libc::off_t);
                assert!(got > 0, "read failed");
                have += got as usize;
            }
            let mut start = 0;
            if task.from > 0 {
                while start < have && bytes[start] != b'\n' {
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
                while end < have && bytes[end] != b'\n' {
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
            if bytes[end - 1] != b'\n' {
                bytes[end] = b'\n';
                end += 1;
            }
            return (start, end);
        }
    }

    fn base(&self) -> *const u8 {
        self.base
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

pub trait Events {
    unsafe fn rows(&mut self, rows: &Rows, count: usize);
    unsafe fn plain(&mut self, fields: &[Field; 7]);
}

pub unsafe fn run_plain(input: &Input, task: Task, buffer: &mut Buffer, sink: &mut impl Events) {
    let (mut from, to) = buffer.fill(input, task);
    let base = buffer.base();
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

#[repr(C, align(64))]
pub struct Batch {
    rows: Rows,
    clicks: [Click; rows::BATCH],
    pub days: Days,
}

impl Batch {
    pub fn new() -> Box<Self> {
        Box::new(Batch { rows: Rows::new(), clicks: [NO_CLICK; rows::BATCH], days: Days::new() })
    }
}

#[inline(always)]
pub unsafe fn split_click(at: *const u8) -> (usize, Option<[Field; 4]>) {
    let mut fields: [Field; 4] = [(std::ptr::null(), 0); 4];
    let len = take::<4>(at, true, &mut fields);
    if len != 0 {
        return (len, Some(fields));
    }
    let (len, ok) = slow_line(at, &mut fields);
    (len, ok.then_some(fields))
}

pub trait Clicks {
    unsafe fn clicks(&mut self, rows: &[Click]);
    unsafe fn plain_click(&mut self, fields: &[Field; 4]);
}

pub unsafe fn run_plain_clicks(input: &Input, task: Task, buffer: &mut Buffer, sink: &mut impl Clicks) {
    let (mut from, to) = buffer.fill(input, task);
    let base = buffer.base();
    if task.from == 0 {
        while from < to && *base.add(from) != b'\n' {
            from += 1;
        }
        from += 1;
    }
    while from < to {
        let (len, fields) = split_click(base.add(from));
        if let Some(fields) = fields {
            sink.plain_click(&fields);
        }
        from += len;
    }
}

#[inline(never)]
pub unsafe fn run_clicks(input: &Input, task: Task, buffer: &mut Buffer, batch: &mut Batch, sink: &mut impl Clicks) {
    let (mut from, to) = buffer.fill(input, task);
    let base = buffer.base();
    if task.from == 0 {
        while from < to && *base.add(from) != b'\n' {
            from += 1;
        }
        from += 1;
    }
    let first = batch.clicks.as_mut_ptr();
    let last = first.add(rows::BATCH);
    let days: *mut Days = &mut batch.days;
    let mut row = first;
    let (mut at, end) = (base.add(from), base.add(to));
    while at < end {
        let len = rows::read_click(at, days, row);
        if len != 0 {
            at = at.add(len);
            row = row.add(1);
            if row == last {
                hand_on_clicks(first, row, sink);
                row = first;
            }
        } else {
            at = at.add(other_click(at, days, sink));
        }
    }
    hand_on_clicks(first, row, sink);
}

#[inline(never)]
unsafe fn hand_on_clicks(first: *const Click, end: *const Click, sink: &mut impl Clicks) {
    sink.clicks(std::slice::from_raw_parts(first, end.offset_from(first) as usize));
}

#[cold]
#[inline(never)]
unsafe fn other_click(at: *const u8, days: *mut Days, sink: &mut impl Clicks) -> usize {
    let (len, fields) = split_click(at);
    if let Some(fields) = fields {
        if fields[3].1 >= 10 {
            (*days).learn(fields[3].0);
        }
        sink.plain_click(&fields);
    }
    len
}

#[inline(never)]
pub unsafe fn run_events(input: &Input, task: Task, buffer: &mut Buffer, batch: &mut Batch, sink: &mut impl Events) {
    let (mut from, to) = buffer.fill(input, task);
    let base = buffer.base();
    if task.from == 0 {
        while from < to && *base.add(from) != b'\n' {
            from += 1;
        }
        from += 1;
    }
    let rows: *mut Rows = &mut batch.rows;
    let days: *mut Days = &mut batch.days;
    let mut row = 0;
    let (mut at, end) = (base.add(from), base.add(to));
    while at < end {
        let len = rows::read(at, days, rows, row);
        if len != 0 {
            at = at.add(len);
            row += 1;
            if row == rows::BATCH {
                hand_on(rows, row, sink);
                row = 0;
            }
        } else {
            at = at.add(other(at, days, sink));
        }
    }
    hand_on(rows, row, sink);
}

#[inline(never)]
unsafe fn hand_on(rows: *const Rows, count: usize, sink: &mut impl Events) {
    sink.rows(&*rows, count);
}

#[cold]
#[inline(never)]
unsafe fn other(at: *const u8, days: *mut Days, sink: &mut impl Events) -> usize {
    let (len, fields) = split(at);
    if let Some(fields) = fields {
        for field in [fields[2], fields[3]] {
            if field.1 >= 10 {
                (*days).learn(field.0);
            }
        }
        sink.plain(&fields);
    }
    len
}
