
use std::arch::x86_64::*;

use super::super::days_from_civil;

#[repr(C, align(64))]
pub struct Rows {
    pub ids: [[u64; 2]; BATCH],
    pub times: [[i64; 2]; BATCH],
    pub lines: [u64; BATCH],
    pub tails: [u32; BATCH],
}

pub const PURCHASE: u64 = 1 << 63;
pub const BATCH: usize = 64;

impl Rows {
    pub fn new() -> Self {
        Rows { ids: [[0; 2]; BATCH], times: [[0; 2]; BATCH], lines: [0; BATCH], tails: [0; BATCH] }
    }
}

#[repr(C, align(32))]
#[derive(Clone, Copy)]
struct Day {
    text: [u8; 16],
    ms: i64,
    seconds: i64,
}

pub struct Days([Day; 128]);

const PLACE: u32 = 0x0F03_0001;

impl Days {
    pub fn new() -> Self {
        Days([Day { text: [b','; 16], ms: 0, seconds: 0 }; 128])
    }

    #[cold]
    #[inline(never)]
    pub unsafe fn learn(&mut self, at: *const u8) {
        let text = std::slice::from_raw_parts(at, 10);
        let digit = |index: usize| text[index].is_ascii_digit().then(|| i64::from(text[index] - b'0'));
        let (Some(y1), Some(y2), Some(y3), Some(y4), Some(m1), Some(m2), Some(d1), Some(d2)) =
            (digit(0), digit(1), digit(2), digit(3), digit(5), digit(6), digit(8), digit(9))
        else {
            return;
        };
        let (year, month, day) = (y1 * 1000 + y2 * 100 + y3 * 10 + y4, m1 * 10 + m2, d1 * 10 + d2);
        if text[4] != b'-' || text[7] != b'-' || !(1..=12).contains(&month) {
            return;
        }
        let leap = year % 4 == 0 && (year % 100 != 0 || year % 400 == 0);
        let most = match month {
            4 | 6 | 9 | 11 => 30,
            2 => 28 + i64::from(leap),
            _ => 31,
        };
        if !(1..=most).contains(&day) {
            return;
        }
        let place = _pext_u32((at.add(6) as *const u32).read_unaligned(), PLACE) as usize;
        let seconds = days_from_civil(year, month, day) * 86_400;
        let mut kept = [0u8; 16];
        kept[0] = b'"';
        kept[1..11].copy_from_slice(text);
        self.0[place] = Day { text: kept, ms: seconds * 1000, seconds };
    }
}

const NOTHING: u8 = 0x80;

#[repr(C, align(64))]
#[derive(Clone, Copy)]
struct IdRow {
    pick: [u8; 16],
    want: [u8; 16],
    lead: [u8; 16],
    unused: [u8; 16],
}

const fn id_rows(prefix: u8) -> [IdRow; 64] {
    let refuse = {
        let mut want = [0u8; 16];
        want[8] = 1;
        IdRow { pick: [NOTHING; 16], want, lead: [0; 16], unused: [0; 16] }
    };
    let mut rows = [refuse; 64];
    let mut length = 2;
    while length <= 11 {
        let quoted = if length >= 10 { 1 } else { 0 };
        let digits = length - 1 - 2 * quoted;
        let first = 16 - length;
        let mut row = IdRow { pick: [NOTHING; 16], want: [0; 16], lead: [0; 16], unused: [0; 16] };
        let mut at = 0;
        while at < 8 {
            if at < 8 - digits {
                row.want[at] = b'0';
            } else {
                row.pick[at] = (first + quoted + 1 + at - (8 - digits)) as u8;
            }
            at += 1;
        }
        if digits > 1 {
            row.lead[8 - digits] = 1;
        }
        row.pick[8] = (first + quoted) as u8;
        row.want[8] = prefix;
        if quoted == 1 {
            row.pick[9] = first as u8;
            row.want[9] = b'"';
            row.pick[10] = 15;
            row.want[10] = b'"';
        }
        rows[length] = row;
        length += 1;
    }
    rows
}

static EVENT_IDS: [IdRow; 64] = id_rows(b'e');
static USER_IDS: [IdRow; 64] = id_rows(b'u');

#[repr(C, align(64))]
#[derive(Clone, Copy)]
struct TimeRow {
    pick: [u8; 32],
    base: [u8; 32],
    most: [u8; 32],
    tens: [i16; 16],
    top: [i32; 8],
    fold: [i16; 16],
    gain: [u64; 4],
    back: [i64; 4],
    sign: [u8; 32],
    dated: [u8; 32],
    place: u32,
    quoted: u32,
    unused: [u8; 56],
}

const fn set(part: &mut [u8; 32], half: usize, at: usize, value: u8) {
    part[half * 16 + at] = value;
}

const fn calendar(row: &mut TimeRow, half: usize, length: usize, quoted: usize) {
    let cut = length - 16 + quoted;
    let digits: [(usize, usize, u8); 10] =
        [(0, 11, 2), (1, 12, 9), (2, 14, 5), (3, 15, 9), (4, 17, 5), (5, 18, 9), (8, 20, 2), (9, 21, 9), (10, 23, 5), (11, 24, 9)];
    let mut index = 0;
    while index < if length == 25 { 10 } else { 6 } {
        let (to, from, most) = digits[index];
        set(&mut row.pick, half, to, (from - cut) as u8);
        set(&mut row.base, half, to, b'0');
        set(&mut row.most, half, to, most);
        index += 1;
    }
    let fixed: [(usize, usize, u8); 5] = [(6, 10, b'T'), (12, 13, b':'), (13, 16, b':'), (7, 19, b'Z'), (14, 22, b':')];
    let mut index = 0;
    while index < 5 {
        let (to, from, what) = fixed[index];
        if from >= cut && from < length {
            set(&mut row.pick, half, to, (from - cut) as u8);
            set(&mut row.base, half, to, what);
        }
        index += 1;
    }
    if length == 25 {
        set(&mut row.base, half, 7, b'+');
        set(&mut row.most, half, 7, 2);
        set(&mut row.sign, half, 7, 2);
    }
    if quoted == 1 {
        set(&mut row.pick, half, 15, 15);
        set(&mut row.base, half, 15, b'"');
    }
    let tens: [i16; 8] = [60, 1, 1, 0, 60, 1, 0, 0];
    let fold: [i16; 8] = [60, 1, 1, 0, 60, 1, 1, 0];
    let top: [i32; 4] = [1439, i32::MAX, 1439, i32::MAX];
    let mut at = 0;
    while at < 8 {
        row.tens[half * 8 + at] = tens[at];
        row.fold[half * 8 + at] = fold[at];
        at += 1;
    }
    let mut at = 0;
    while at < 4 {
        row.top[half * 4 + at] = top[at];
        at += 1;
    }
    row.gain[half * 2] = 1000;
    row.gain[half * 2 + 1] = 1;
    row.back[half * 2] = 60_000;
    row.back[half * 2 + 1] = 60;
}

const fn plain(row: &mut TimeRow, count: usize, quoted: usize) {
    let mut at = 16 - count;
    while at < 16 {
        row.pick[at] = (at - quoted) as u8;
        row.base[at] = b'0';
        row.most[at] = 9;
        at += 1;
    }
    if quoted == 1 {
        row.pick[0] = 15;
        row.base[0] = b'"';
        row.pick[1] = (14 - count) as u8;
        row.base[1] = b'"';
    }
    let mut at = 0;
    while at < 8 {
        row.tens[at] = if at % 2 == 0 { 100 } else { 1 };
        row.fold[at] = if at % 2 == 0 { 10_000 } else { 1 };
        at += 1;
    }
    let mut at = 0;
    while at < 4 {
        row.top[at] = i32::MAX;
        at += 1;
    }
    row.gain[0] = 100_000_000;
    row.back[0] = -1;
}

const fn dated(row: &mut TimeRow, half: usize, quoted: usize) {
    let mut at = 1 - quoted;
    while at <= 10 {
        row.dated[half * 16 + at] = 0xFF;
        at += 1;
    }
}

const fn time_rows() -> [TimeRow; 128] {
    let empty = TimeRow {
        pick: [NOTHING; 32],
        base: [0; 32],
        most: [0; 32],
        tens: [0; 16],
        top: [0; 8],
        fold: [0; 16],
        gain: [0; 4],
        back: [0; 4],
        sign: [0; 32],
        dated: [0; 32],
        place: 0,
        quoted: 0,
        unused: [0; 56],
    };
    let mut rows = [empty; 128];
    let mut index = 0;
    while index < 128 {
        let (raw, ingest_quoted) = (index / 2, index % 2);
        let row = &mut rows[index];
        calendar(row, 1, 20, ingest_quoted);
        dated(row, 1, ingest_quoted);
        let quoted = if raw == 15 || raw == 22 || raw == 27 { 1 } else { 0 };
        let length = raw - 2 * quoted;
        row.quoted = quoted as u32;
        if length == 20 || length == 25 {
            calendar(row, 0, length, quoted);
            dated(row, 0, quoted);
            row.place = PLACE;
        } else if length >= 1 && length <= 16 - 2 * quoted {
            plain(row, length, quoted);
        } else {
            row.base[0] = 1;
        }
        index += 1;
    }
    rows
}

#[repr(C, align(64))]
#[derive(Clone, Copy)]
struct TailRow {
    span: u64,
    opens: u64,
    quotes: [u64; 4],
    unused: [u64; 2],
}

const fn tail_rows() -> [TailRow; 4096] {
    const NEVER: u64 = u64::MAX;
    let mut rows = [TailRow { span: 0, opens: 0, quotes: [NEVER; 4], unused: [0; 2] }; 4096];
    let mut index = 0;
    while index < 4096 {
        let (product, price) = (index / 64, index % 64);
        if product >= 1 && product + 1 + price <= 63 {
            let row = &mut rows[index];
            row.span = (1 << (product + 1 + price)) - 1;
            row.opens = 1 | if price > 0 { 1 << (product + 1) } else { 0 };
            let wrapped_product = 1 | 1 << (product - 1);
            let wrapped_price = if price >= 2 { (1 | 1 << (price - 1)) << (product + 1) } else { 0 };
            row.quotes[0] = 0;
            if product >= 3 {
                row.quotes[1] = wrapped_product;
            }
            if price >= 2 {
                row.quotes[2] = wrapped_price;
            }
            if product >= 3 && price >= 2 {
                row.quotes[3] = wrapped_product | wrapped_price;
            }
        }
        index += 1;
    }
    rows
}

static TAILS: [TailRow; 4096] = tail_rows();
static TIMES: [TimeRow; 128] = time_rows();

#[repr(align(32))]
struct Wide<T>(T);

static ID_PAIRS: Wide<[u8; 32]> = Wide([36, 1, 36, 1, 36, 1, 36, 1, 0, 0, 0, 0, 0, 0, 0, 0, 36, 1, 36, 1, 36, 1, 36, 1, 0, 0, 0, 0, 0, 0, 0, 0]);
static ID_FOURS: Wide<[i16; 16]> = Wide([1296, 1, 1296, 1, 0, 0, 0, 0, 1296, 1, 1296, 1, 0, 0, 0, 0]);

#[inline(always)]
unsafe fn two(low: *const u8, high: *const u8) -> __m256i {
    _mm256_inserti128_si256::<1>(_mm256_castsi128_si256(_mm_loadu_si128(low as *const __m128i)), _mm_loadu_si128(high as *const __m128i))
}

#[inline(always)]
unsafe fn whole<T>(at: &T) -> __m256i {
    _mm256_load_si256(at as *const T as *const __m256i)
}

const VIEW: u64 = u64::from_le_bytes(*b"view,\0\0\0");
const CART: u64 = u64::from_le_bytes(*b"cart,\0\0\0");
const VIEW_QUOTED: u64 = u64::from_le_bytes(*b"\"view\",\0");
const CART_QUOTED: u64 = u64::from_le_bytes(*b"\"cart\",\0");
const BOUGHT: u64 = u64::from_le_bytes(*b"purchase");

#[inline(always)]
pub unsafe fn read(at: *const u8, days: *const Days, rows: *mut Rows, row: usize) -> usize {
    let bits = |bytes: __m256i, what: u8| u64::from(_mm256_movemask_epi8(_mm256_cmpeq_epi8(bytes, _mm256_set1_epi8(what as i8))) as u32);
    let first = _mm256_loadu_si256(at as *const __m256i);
    let second = _mm256_loadu_si256(at.add(32) as *const __m256i);
    let third = _mm256_loadu_si256(at.add(64) as *const __m256i);
    let middle = bits(second, b',');
    let head = bits(first, b',') | middle << 32;
    let commas = middle | bits(third, b',') << 32;
    let newlines = bits(second, b'\n') | bits(third, b'\n') << 32;
    let quotes = bits(second, b'"') | bits(third, b'"') << 32;

    let end = u64::from(newlines.trailing_zeros());
    let c0 = head.trailing_zeros() as usize;
    let rest = head & head.wrapping_sub(1);
    let c1 = rest.trailing_zeros() as usize;
    let rest = rest & rest.wrapping_sub(1);
    let c2 = rest.trailing_zeros() as usize;
    let before = _bzhi_u64(commas, end as u32);
    let gap = u64::from(before.leading_zeros());
    let price = end.wrapping_add(gap).wrapping_sub(64);
    let before = before.wrapping_shl(gap as u32) << 1;
    let product = u64::from(before.leading_zeros());
    let before = before.wrapping_shl(product as u32) << 1;
    let kind = u64::from(before.leading_zeros());
    let c3 = 93u64.wrapping_sub(gap).wrapping_sub(product).wrapping_sub(kind) as usize;
    let longer = c3.wrapping_sub(c2 + 21);
    if (end > 63) | (c2 > 63) | (kind > 63) | (longer & !2 != 0) {
        return 0;
    }
    let q3 = longer >> 1;

    let event = EVENT_IDS.get_unchecked(c0);
    let user = USER_IDS.get_unchecked(c1 - c0 - 1);
    let text = two(at.add(c0).sub(16), at.add(c1).sub(16));
    let moved = _mm256_xor_si256(_mm256_shuffle_epi8(text, two(event.pick.as_ptr(), user.pick.as_ptr())), two(event.want.as_ptr(), user.want.as_ptr()));
    let above = _mm256_cmpgt_epi8(moved, _mm256_set1_epi8(b'9' as i8));
    let value = _mm256_sub_epi8(moved, _mm256_add_epi8(_mm256_set1_epi8(b'0' as i8), _mm256_and_si256(above, _mm256_set1_epi8((b'a' - 10 - b'0') as i8))));
    let held = _mm256_min_epu8(_mm256_max_epu8(value, _mm256_and_si256(above, _mm256_set1_epi8(10))), _mm256_set1_epi8(35));
    let mut wrong = _mm256_blend_epi32::<0b1100_1100>(_mm256_xor_si256(held, value), moved);
    wrong = _mm256_or_si256(wrong, _mm256_subs_epu8(two(event.lead.as_ptr(), user.lead.as_ptr()), value));
    let fours = _mm256_madd_epi16(_mm256_maddubs_epi16(value, whole(&ID_PAIRS)), whole(&ID_FOURS));
    let ids = _mm256_add_epi64(_mm256_mul_epu32(fours, _mm256_set1_epi64x(1_679_616)), _mm256_srli_epi64::<32>(fours));
    wrong = _mm256_or_si256(wrong, _mm256_cmpgt_epi64(ids, _mm256_set1_epi64x(super::codec::MASK as i64)));
    _mm_storeu_si128((*rows).ids.as_mut_ptr().add(row) as *mut __m128i, _mm256_castsi256_si128(_mm256_permute4x64_epi64::<0b1000>(ids)));

    let time = TIMES.get_unchecked((c2 - c1 - 1) * 2 + q3);
    let text = two(at.add(c2).sub(16), at.add(c3).sub(16));
    let digits = _mm256_sub_epi8(_mm256_shuffle_epi8(text, whole(&time.pick)), whole(&time.base));
    wrong = _mm256_or_si256(wrong, _mm256_subs_epu8(digits, whole(&time.most)));
    let sums = _mm256_madd_epi16(_mm256_maddubs_epi16(digits, _mm256_set1_epi16(0x010A)), whole(&time.tens));
    wrong = _mm256_or_si256(wrong, _mm256_cmpgt_epi32(sums, whole(&time.top)));
    let folded = _mm256_madd_epi16(_mm256_packus_epi32(sums, sums), whole(&time.fold));
    let gained = _mm256_mul_epu32(folded, whole(&time.gain));
    let back = _mm256_mul_epi32(_mm256_srli_epi64::<32>(folded), whole(&time.back));
    let off = _mm256_cmpeq_epi64(_mm256_and_si256(digits, whole(&time.sign)), _mm256_setzero_si256());
    let mut times = _mm256_add_epi64(gained, _mm256_sub_epi64(_mm256_xor_si256(back, off), off));
    let ts_text = at.add(c1 + time.quoted as usize);
    let ts_day = (days as *const Day).add(_pext_u32((ts_text.add(7) as *const u32).read_unaligned(), time.place) as usize) as *const u8;
    let ingest_text = at.add(c2 + q3);
    let ingest_day = (days as *const Day).add(_pext_u32((ingest_text.add(7) as *const u32).read_unaligned(), PLACE) as usize) as *const u8;
    wrong = _mm256_or_si256(wrong, _mm256_and_si256(_mm256_xor_si256(two(ts_text, ingest_text), two(ts_day, ingest_day)), whole(&time.dated)));
    times = _mm256_add_epi64(times, two(ts_day.add(16), ingest_day.add(16)));
    _mm_storeu_si128((*rows).times.as_mut_ptr().add(row) as *mut __m128i, _mm256_castsi256_si128(_mm256_permute4x64_epi64::<0b1100>(times)));

    let tail = at.add(32);
    let type_at = tail.add(c3 - 31);
    let word = (type_at as *const u64).read_unaligned();
    let (five, seven) = (word & 0xFF_FFFF_FFFF, word & 0xFF_FFFF_FFFF_FFFF);
    let browse = (five == VIEW) | (five == CART) | (seven == VIEW_QUOTED) | (seven == CART_QUOTED);
    let pair = TAILS.get_unchecked((product * 64 + price) as usize);
    let theirs = quotes >> (63 - gap - product) & pair.span;
    let odd = theirs != *pair.quotes.get_unchecked(_pext_u64(theirs, pair.opens) as usize);
    if (_mm256_testz_si256(wrong, wrong) == 0) | odd {
        return 0;
    }
    let mut line = at as u64;
    if !browse {
        let quoted = u64::from(*type_at == b'"');
        let bought = (type_at.add(quoted as usize) as *const u64).read_unaligned() == BOUGHT;
        let closed = quoted == 0 || *type_at.add(9) == b'"';
        if !(bought & closed & (kind == 8 + 2 * quoted)) {
            return 0;
        }
        line |= PURCHASE;
        let (qp, qr) = (theirs & 1, theirs >> (product + 1) & 1);
        let (product_at, price_at) = (32 + 63 - gap - product + qp, 32 + 64 - gap + qr);
        *(*rows).tails.as_mut_ptr().add(row) = (product_at | (product - 2 * qp) << 8 | price_at << 16 | (price - 2 * qr) << 24) as u32;
    }
    *(*rows).lines.as_mut_ptr().add(row) = line;
    33 + end as usize
}

#[repr(C, align(64))]
#[derive(Clone, Copy)]
pub struct Click {
    pub id: u64,
    pub who: u64,
    pub ts: i64,
    unused: i64,
    pub campaign: u64,
    other: i64,
    pub line: *const u8,
    spare: u64,
}

pub const NO_CLICK: Click = Click { id: 0, who: 0, ts: 0, unused: 0, campaign: 0, other: 0, line: std::ptr::null(), spare: 0 };

#[repr(C, align(64))]
#[derive(Clone, Copy)]
struct Half {
    pick: [u8; 16],
    base: [u8; 16],
    most: [u8; 16],
    tens: [i16; 8],
    top: [i32; 4],
    fold: [i16; 8],
    gain: [u64; 2],
    back: [i64; 2],
    sign: [u8; 16],
    dated: [u8; 16],
    place: u32,
    quoted: u32,
    unused: [u8; 24],
}

const fn lower(row: &TimeRow) -> Half {
    let mut half = Half {
        pick: [0; 16],
        base: [0; 16],
        most: [0; 16],
        tens: [0; 8],
        top: [0; 4],
        fold: [0; 8],
        gain: [row.gain[0], row.gain[1]],
        back: [row.back[0], row.back[1]],
        sign: [0; 16],
        dated: [0; 16],
        place: row.place,
        quoted: row.quoted,
        unused: [0; 24],
    };
    let mut at = 0;
    while at < 16 {
        half.pick[at] = row.pick[at];
        half.base[at] = row.base[at];
        half.most[at] = row.most[at];
        half.sign[at] = row.sign[at];
        half.dated[at] = row.dated[at];
        if at < 8 {
            half.tens[at] = row.tens[at];
            half.fold[at] = row.fold[at];
        }
        if at < 4 {
            half.top[at] = row.top[at];
        }
        at += 1;
    }
    half
}

const fn ts_halves() -> [Half; 64] {
    let rows = time_rows();
    let mut halves = [lower(&rows[0]); 64];
    let mut index = 0;
    while index < 64 {
        halves[index] = lower(&rows[index * 2]);
        index += 1;
    }
    halves
}

const fn campaign_halves() -> [Half; 32] {
    let refuse = {
        let mut half = lower(&time_rows()[0]);
        half.dated = [0; 16];
        half.place = 0;
        half.quoted = 0;
        half
    };
    let mut halves = [refuse; 32];
    let mut index = 0;
    while index < 32 {
        let (raw, quoted) = (index / 2, index % 2);
        if raw >= 3 + 2 * quoted && raw <= 8 + 2 * quoted {
            let count = raw - 2 - 2 * quoted;
            let first = 16 - raw;
            let mut half = Half {
                pick: [NOTHING; 16],
                base: [0; 16],
                most: [0; 16],
                tens: [100, 1, 100, 1, 100, 1, 100, 1],
                top: [i32::MAX; 4],
                fold: [10_000, 1, 10_000, 1, 10_000, 1, 10_000, 1],
                gain: [0; 2],
                back: [-1, 0],
                sign: [0; 16],
                dated: [0; 16],
                place: 0,
                quoted: 0,
                unused: [0; 24],
            };
            let mut at = 0;
            let mut short = 1u64;
            while at < count {
                let to = 16 - count + at;
                half.pick[to] = (first + quoted + 2 + at) as u8;
                half.base[to] = if at == 0 { b'1' } else { b'0' };
                half.most[to] = if at == 0 { 8 } else { 9 };
                if at > 0 {
                    short *= 10;
                }
                at += 1;
            }
            half.pick[0] = (first + quoted) as u8;
            half.base[0] = b'c';
            half.pick[1] = (first + quoted + 1) as u8;
            half.base[1] = b'_';
            if quoted == 1 {
                half.pick[2] = first as u8;
                half.base[2] = b'"';
                half.pick[3] = 15;
                half.base[3] = b'"';
            }
            let bytes = short.to_le_bytes();
            let mut at = 0;
            while at < 8 {
                half.dated[at] = bytes[at];
                at += 1;
            }
            halves[index] = half;
        }
        index += 1;
    }
    halves
}

static CLICK_IDS: [IdRow; 64] = id_rows(b'k');
static TS_HALVES: [Half; 64] = ts_halves();
static CAMPAIGNS: [Half; 32] = campaign_halves();

#[inline(always)]
pub unsafe fn read_click(at: *const u8, days: *const Days, row: *mut Click) -> usize {
    let bits = |bytes: __m256i, what: u8| u64::from(_mm256_movemask_epi8(_mm256_cmpeq_epi8(bytes, _mm256_set1_epi8(what as i8))) as u32);
    let first = _mm256_loadu_si256(at as *const __m256i);
    let second = _mm256_loadu_si256(at.add(32) as *const __m256i);
    let newlines = bits(first, b'\n') | bits(second, b'\n') << 32;
    let end = newlines.trailing_zeros() as usize;
    let commas = _bzhi_u64(bits(first, b',') | bits(second, b',') << 32, end as u32);
    let c0 = commas.trailing_zeros() as usize;
    let rest = commas & commas.wrapping_sub(1);
    let c1 = rest.trailing_zeros() as usize;
    let rest = rest & rest.wrapping_sub(1);
    let c2 = rest.trailing_zeros() as usize;
    if (end > 63) | (c2 > 63) | (rest & rest.wrapping_sub(1) != 0) {
        return 0;
    }
    let q2 = usize::from(*at.add(c1 + 1) == b'"');

    let click = CLICK_IDS.get_unchecked(c0);
    let user = USER_IDS.get_unchecked(c1 - c0 - 1);
    let text = two(at.add(c0).sub(16), at.add(c1).sub(16));
    let moved = _mm256_xor_si256(_mm256_shuffle_epi8(text, two(click.pick.as_ptr(), user.pick.as_ptr())), two(click.want.as_ptr(), user.want.as_ptr()));
    let above = _mm256_cmpgt_epi8(moved, _mm256_set1_epi8(b'9' as i8));
    let value = _mm256_sub_epi8(moved, _mm256_add_epi8(_mm256_set1_epi8(b'0' as i8), _mm256_and_si256(above, _mm256_set1_epi8((b'a' - 10 - b'0') as i8))));
    let held = _mm256_min_epu8(_mm256_max_epu8(value, _mm256_and_si256(above, _mm256_set1_epi8(10))), _mm256_set1_epi8(35));
    let mut wrong = _mm256_blend_epi32::<0b1100_1100>(_mm256_xor_si256(held, value), moved);
    wrong = _mm256_or_si256(wrong, _mm256_subs_epu8(two(click.lead.as_ptr(), user.lead.as_ptr()), value));
    let fours = _mm256_madd_epi16(_mm256_maddubs_epi16(value, whole(&ID_PAIRS)), whole(&ID_FOURS));
    let ids = _mm256_add_epi64(_mm256_mul_epu32(fours, _mm256_set1_epi64x(1_679_616)), _mm256_srli_epi64::<32>(fours));
    wrong = _mm256_or_si256(wrong, _mm256_cmpgt_epi64(ids, _mm256_set1_epi64x(super::codec::MASK as i64)));
    _mm_storeu_si128(row as *mut __m128i, _mm256_castsi256_si128(_mm256_permute4x64_epi64::<0b1000>(ids)));

    let time = TS_HALVES.get_unchecked(end - c2 - 1);
    let campaign = CAMPAIGNS.get_unchecked((c2 - c1 - 1).min(15) * 2 + q2);
    let text = two(at.add(end).sub(16), at.add(c2).sub(16));
    let digits = _mm256_sub_epi8(_mm256_shuffle_epi8(text, two(time.pick.as_ptr(), campaign.pick.as_ptr())), two(time.base.as_ptr(), campaign.base.as_ptr()));
    wrong = _mm256_or_si256(wrong, _mm256_subs_epu8(digits, two(time.most.as_ptr(), campaign.most.as_ptr())));
    let sums = _mm256_madd_epi16(_mm256_maddubs_epi16(digits, _mm256_set1_epi16(0x010A)), two(time.tens.as_ptr() as *const u8, campaign.tens.as_ptr() as *const u8));
    wrong = _mm256_or_si256(wrong, _mm256_cmpgt_epi32(sums, two(time.top.as_ptr() as *const u8, campaign.top.as_ptr() as *const u8)));
    let folded = _mm256_madd_epi16(_mm256_packus_epi32(sums, sums), two(time.fold.as_ptr() as *const u8, campaign.fold.as_ptr() as *const u8));
    let gained = _mm256_mul_epu32(folded, two(time.gain.as_ptr() as *const u8, campaign.gain.as_ptr() as *const u8));
    let back = _mm256_mul_epi32(_mm256_srli_epi64::<32>(folded), two(time.back.as_ptr() as *const u8, campaign.back.as_ptr() as *const u8));
    let off = _mm256_cmpeq_epi64(_mm256_and_si256(digits, two(time.sign.as_ptr(), campaign.sign.as_ptr())), _mm256_setzero_si256());
    let mut times = _mm256_add_epi64(gained, _mm256_sub_epi64(_mm256_xor_si256(back, off), off));
    let ts_text = at.add(c2 + time.quoted as usize);
    let ts_day = (days as *const Day).add(_pext_u32((ts_text.add(7) as *const u32).read_unaligned(), time.place) as usize);
    let differs = _mm_and_si128(_mm_xor_si128(_mm_loadu_si128(ts_text as *const __m128i), _mm_load_si128(ts_day as *const __m128i)), _mm_load_si128(time.dated.as_ptr() as *const __m128i));
    wrong = _mm256_or_si256(wrong, _mm256_castsi128_si256(differs));
    times = _mm256_add_epi64(times, two((ts_day as *const u8).add(16), campaign.dated.as_ptr()));
    _mm256_storeu_si256((row as *mut __m256i).byte_add(16), times);
    (*row).line = at;
    if _mm256_testz_si256(wrong, wrong) == 0 {
        return 0;
    }
    end + 1
}
