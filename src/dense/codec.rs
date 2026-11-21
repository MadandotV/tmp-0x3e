
use std::arch::x86_64::*;

pub const MASK: u64 = (1 << 40) - 1;
const A: u64 = 0x9E37_79B9_7F4B;
const B: u64 = 0xD6E8_FEB8_6659;
pub const NONE: u64 = u64::MAX;

const fn inverse(odd: u64) -> u64 {
    let mut x = odd;
    let mut round = 0;
    while round < 6 {
        x = x.wrapping_mul(2u64.wrapping_sub(odd.wrapping_mul(x)));
        round += 1;
    }
    x
}

pub const A_INVERSE: u64 = inverse(A);
pub const B_INVERSE: u64 = inverse(B);

#[inline(always)]
pub fn scramble(value: u64, key: u64) -> u64 {
    let mut mixed = (value.wrapping_mul(A) ^ key) & MASK;
    mixed ^= mixed >> 17;
    mixed.wrapping_mul(B) & MASK
}

#[inline(always)]
pub fn premix(scrambled: u64) -> u64 {
    let mixed = scrambled.wrapping_mul(B_INVERSE) & MASK;
    mixed ^ mixed >> 17 ^ mixed >> 34
}

#[inline(always)]
pub fn unscramble(scrambled: u64, key: u64) -> u64 {
    (premix(scrambled) ^ key).wrapping_mul(A_INVERSE) & MASK
}

static FILL: [u64; 9] = {
    let mut table = [0u64; 9];
    let mut digits = 0;
    while digits < 8 {
        table[digits] = 0x3030_3030_3030_3030 >> (8 * digits);
        digits += 1;
    }
    table
};

#[inline(always)]
pub unsafe fn decode(at: *const u8, len: usize, prefix: u8) -> u64 {
    if len.wrapping_sub(2) > 7 || *at != prefix {
        return NONE;
    }
    let digits = len - 1;
    let raw = (at.add(1) as *const u64).read_unaligned();
    if raw as u8 == b'0' && digits > 1 {
        return NONE;
    }
    let word = raw << (8 * (8 - digits)) | *FILL.get_unchecked(digits);
    let bytes = _mm_cvtsi64_si128(word as i64);
    let above = _mm_cmpgt_epi8(bytes, _mm_set1_epi8(b'9' as i8));
    let base = _mm_add_epi8(_mm_set1_epi8(b'0' as i8), _mm_and_si128(above, _mm_set1_epi8((b'a' - 10 - b'0') as i8)));
    let value = _mm_sub_epi8(bytes, base);
    let least = _mm_and_si128(above, _mm_set1_epi8(10));
    let held = _mm_min_epu8(_mm_max_epu8(value, least), _mm_set1_epi8(35));
    if _mm_movemask_epi8(_mm_cmpeq_epi8(held, value)) & 0xFF != 0xFF {
        return NONE;
    }
    let pairs = _mm_maddubs_epi16(value, _mm_set1_epi16(0x0124));
    let fours = _mm_madd_epi16(pairs, _mm_set1_epi32(0x0001_0510));
    let both = _mm_cvtsi128_si64(fours) as u64;
    let out = (both & 0xFFFF_FFFF) * 1_679_616 + (both >> 32);
    if out > MASK {
        NONE
    } else {
        out
    }
}

pub fn decode_bytes(id: &[u8], prefix: u8) -> u64 {
    let mut padded = [0u8; 16];
    if id.len() > 9 {
        return NONE;
    }
    padded[..id.len()].copy_from_slice(id);
    unsafe { decode(padded.as_ptr(), id.len(), prefix) }
}

#[inline]
pub fn encode(prefix: u8, value: u64, out: &mut [u8; 16]) -> usize {
    const DIGITS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";
    let mut buffer = [0u8; 8];
    let mut at = 8;
    let mut rest = value;
    loop {
        at -= 1;
        buffer[at] = DIGITS[(rest % 36) as usize];
        rest /= 36;
        if rest == 0 {
            break;
        }
    }
    *out = [0; 16];
    out[0] = prefix;
    let len = 8 - at;
    out[1..1 + len].copy_from_slice(&buffer[at..]);
    len + 1
}

#[inline]
pub fn order(value: u64) -> u64 {
    const POWERS: [u64; 9] = {
        let mut table = [1u64; 9];
        let mut at = 1;
        while at < 9 {
            table[at] = table[at - 1] * 36;
            at += 1;
        }
        table
    };
    let mut digits = 1;
    while digits < 8 && value >= POWERS[digits] {
        digits += 1;
    }
    (value * POWERS[8 - digits]) << 4 | digits as u64
}

#[derive(Default)]
pub struct Votes {
    hits: Vec<(u64, u64, u64, u64)>,
}

const LOW: u64 = (1 << 39) - 1;

impl Votes {
    pub fn pair(&mut self, m1: u64, m2: u64, from: u64, to: u64) {
        let differ = m1 ^ m2;
        let mut delta = from.wrapping_mul(A) & MASK;
        for _ in from..=to {
            let carries = differ ^ delta;
            let fixed = delta ^ carries;
            if carries & 1 == 0 && (carries >> 1 ^ delta) & !fixed & LOW == 0 {
                self.hits.push((m1, m2, carries >> 1, fixed & LOW));
            }
            delta = delta.wrapping_add(A) & MASK;
        }
    }

    fn tally(&self, key: u64, known: u64) -> ([u32; 39], [u32; 39]) {
        let (mut zero, mut one) = ([0u32; 39], [0u32; 39]);
        for &(m1, m2, carries, fixed) in &self.hits {
            let (first, second) = (m1 ^ carries, m2 ^ carries);
            let apart = (first ^ second) & fixed;
            let (a, b) = (((first ^ key) & apart & known).count_ones(), ((second ^ key) & apart & known).count_ones());
            if a == b && apart != 0 {
                continue;
            }
            let chosen = if a <= b { first } else { second };
            let mut bits = fixed;
            while bits != 0 {
                let bit = bits.trailing_zeros() as usize;
                bits &= bits - 1;
                if chosen >> bit & 1 == 0 {
                    zero[bit] += 1;
                } else {
                    one[bit] += 1;
                }
            }
        }
        (zero, one)
    }

    pub fn settle(&self) -> Option<u64> {
        'anchor: for &(m1, _, carries, fixed) in self.hits.iter().take(4) {
            let (mut key, mut known) = (m1 ^ carries, fixed);
            for round in 0..6 {
                let (zero, one) = self.tally(key, known);
                (key, known) = (0, 0);
                let mut clear = true;
                for bit in 0..39 {
                    let (most, least) = (zero[bit].max(one[bit]), zero[bit].min(one[bit]));
                    key |= u64::from(one[bit] > zero[bit]) << bit;
                    known |= u64::from(most > 0) << bit;
                    clear &= most >= 2 && least * 3 <= most;
                }
                if round >= 2 && clear {
                    return Some(key);
                }
                if known == 0 {
                    continue 'anchor;
                }
            }
        }
        None
    }
}
