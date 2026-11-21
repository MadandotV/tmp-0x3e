
use std::arch::x86_64::*;

use super::super::{Calendar, BAD, RIGHT_ALIGN};

#[repr(align(16))]
struct Bytes([u8; 16]);

static FORM: [Bytes; 2] = [Bytes(*b"00T00:00:00\0\0\0\0\0"), Bytes(*b"00T00:00:00Z\0\0\0\0")];
static MOST: [Bytes; 2] = [
    Bytes([3, 9, 0, 2, 9, 0, 5, 9, 0, 5, 9, 255, 255, 255, 255, 255]),
    Bytes([3, 9, 0, 2, 9, 0, 5, 9, 0, 5, 9, 0, 255, 255, 255, 255]),
];
static TENS: Bytes = Bytes([10, 1, 0, 10, 1, 0, 10, 1, 0, 10, 1, 0, 0, 0, 0, 0]);
#[repr(align(16))]
struct Words([i16; 8]);
static SECONDS: Words = Words([0, 3600, 3600, 60, 1, 1, 0, 0]);

#[inline(always)]
pub unsafe fn civil<const Z: usize>(at: *const u8, calendar: &mut Calendar) -> i64 {
    let prefix = (at as *const u64).read_unaligned();
    if prefix != calendar.prefix && !calendar.load(prefix) {
        return BAD;
    }
    let text = _mm_loadu_si128(at.add(8) as *const __m128i);
    let digits = _mm_sub_epi8(text, _mm_load_si128(FORM[Z].0.as_ptr() as *const __m128i));
    let most = _mm_load_si128(MOST[Z].0.as_ptr() as *const __m128i);
    let fits = _mm_movemask_epi8(_mm_cmpeq_epi8(_mm_max_epu8(digits, most), most));
    let pairs = _mm_maddubs_epi16(digits, _mm_load_si128(TENS.0.as_ptr() as *const __m128i));
    let parts = _mm_madd_epi16(pairs, _mm_load_si128(SECONDS.0.as_ptr() as *const __m128i));
    let sum = _mm_add_epi32(parts, _mm_shuffle_epi32(parts, 0b0100_1110));
    let time = (_mm_cvtsi128_si32(sum) + _mm_extract_epi32(sum, 1)) as u32;
    let day = _mm_cvtsi128_si32(pairs) as u32 & 0xFFFF;
    if fits != 0xFFFF || u64::from(day.wrapping_sub(1)) >= calendar.days_in_month || time >= 86_400 {
        return BAD;
    }
    (calendar.days + i64::from(day)) * 86_400 + i64::from(time)
}

#[inline(always)]
pub unsafe fn timestamp(at: *const u8, len: usize, calendar: &mut Calendar) -> i64 {
    if len == 20 {
        let seconds = civil::<1>(at, calendar);
        if seconds != BAD {
            return seconds * 1000;
        }
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
            let local = civil::<0>(at, calendar);
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
