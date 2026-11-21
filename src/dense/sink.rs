
use std::arch::x86_64::*;

use super::super::DAY;
#[cfg(test)]
use super::codec::unscramble;
use super::codec::{A_INVERSE, B_INVERSE, MASK};
#[cfg(test)]
use super::BUCKET;
use super::{Rec, BUCKET_BITS, INGEST_BITS, INVALID};

pub struct Frame {
    pub user_key: u64,
    pub event_key: u64,
    pub user_bound: u64,
    pub event_bound: u64,
    pub ingest_start: i64,
    pub window_start: i64,
    pub window_end: i64,
    pub spare: u64,
}

impl Frame {
    #[cfg(test)]
    pub fn one(&self, event: u64, who: u64, ts: i64, ingest: i64, payload: Option<u32>) -> Option<(usize, Rec)> {
        let seconds = ingest.wrapping_sub(self.ingest_start) as u64;
        let valid = payload.is_some() && ts >= self.window_start && ts < self.window_end && ingest.wrapping_mul(1000).wrapping_sub(ts) <= DAY;
        let dense = unscramble(who, self.user_key);
        let index = unscramble(event, self.event_key);
        if seconds >= (1 << INGEST_BITS) - 1 || (valid && dense >= self.user_bound) || index >= self.event_bound {
            return None;
        }
        let stamp = if valid { (ts - self.window_start) as u64 } else { INVALID };
        let who = if valid { dense } else { 0 };
        let payload = if valid { payload.unwrap_or(0) } else { 0 };
        let low = index & (BUCKET as u64 - 1);
        let record = Rec { a: who | stamp << 32 | (low >> 14) << 63, b: u64::from(payload) | (seconds + 1) << 29 | (low & 0x3FFF) << 50 };
        Some(((index >> BUCKET_BITS) as usize, record))
    }

    #[inline(always)]
    pub unsafe fn four(&self, ids: *const [u64; 2], times: *const [i64; 2], records: *mut Rec, buckets: *mut u64) -> u32 {
        let all = |value: u64| _mm256_set1_epi64x(value as i64);
        let (first, second) = (_mm256_loadu_si256(ids as *const __m256i), _mm256_loadu_si256(ids.add(2) as *const __m256i));
        let (events, users) = (_mm256_unpacklo_epi64(first, second), _mm256_unpackhi_epi64(first, second));
        let (first, second) = (_mm256_loadu_si256(times as *const __m256i), _mm256_loadu_si256(times.add(2) as *const __m256i));
        let (ts, ingest) = (_mm256_unpacklo_epi64(first, second), _mm256_unpackhi_epi64(first, second));

        let times_low = |value: __m256i, by: u64| {
            let cross = _mm256_add_epi64(_mm256_mul_epu32(value, all(by >> 32)), _mm256_mul_epu32(_mm256_srli_epi64::<32>(value), all(by & 0xFFFF_FFFF)));
            _mm256_add_epi64(_mm256_mul_epu32(value, all(by & 0xFFFF_FFFF)), _mm256_slli_epi64::<32>(cross))
        };
        let plain = |number: __m256i, key: u64| {
            let mixed = _mm256_and_si256(times_low(number, B_INVERSE), all(MASK));
            let mixed = _mm256_xor_si256(_mm256_xor_si256(mixed, _mm256_srli_epi64::<17>(mixed)), _mm256_srli_epi64::<34>(mixed));
            _mm256_and_si256(times_low(_mm256_xor_si256(mixed, all(key)), A_INVERSE), all(MASK))
        };
        let index = plain(events, self.event_key);
        let dense = plain(users, self.user_key);
        let below = |value: __m256i, bound: i64| _mm256_andnot_si256(_mm256_cmpgt_epi64(_mm256_setzero_si256(), value), _mm256_cmpgt_epi64(_mm256_set1_epi64x(bound), value));

        let seconds = _mm256_sub_epi64(ingest, _mm256_set1_epi64x(self.ingest_start));
        let stamp = _mm256_sub_epi64(ts, _mm256_set1_epi64x(self.window_start));
        let apart = _mm256_sub_epi64(
            _mm256_add_epi64(_mm256_mul_epu32(seconds, all(1000)), _mm256_set1_epi64x(self.ingest_start.wrapping_mul(1000).wrapping_sub(self.window_start))),
            stamp,
        );
        let valid = _mm256_andnot_si256(_mm256_cmpgt_epi64(apart, _mm256_set1_epi64x(DAY)), below(stamp, self.window_end.wrapping_sub(self.window_start)));
        let fits = _mm256_and_si256(below(seconds, (1 << INGEST_BITS) - 1), _mm256_cmpgt_epi64(all(self.event_bound), index));
        let foreign = _mm256_andnot_si256(_mm256_cmpgt_epi64(all(self.user_bound), dense), valid);
        let left = _mm256_or_si256(_mm256_andnot_si256(fits, all(u64::MAX)), foreign);

        let stamp = _mm256_blendv_epi8(all(INVALID << 32), _mm256_slli_epi64::<32>(stamp), valid);
        let a = _mm256_or_si256(_mm256_or_si256(_mm256_and_si256(dense, valid), stamp), _mm256_and_si256(_mm256_slli_epi64::<49>(index), all(if BUCKET_BITS > 14 { 1 << 63 } else { 0 })));
        let b = _mm256_or_si256(_mm256_slli_epi64::<29>(_mm256_sub_epi64(seconds, all(u64::MAX))), _mm256_slli_epi64::<50>(index));
        _mm256_storeu_si256(records as *mut __m256i, _mm256_unpacklo_epi64(a, b));
        _mm256_storeu_si256(records.add(2) as *mut __m256i, _mm256_unpackhi_epi64(a, b));
        let bucket = _mm256_blendv_pd(_mm256_castsi256_pd(_mm256_srli_epi64::<{ BUCKET_BITS as i32 }>(index)), _mm256_castsi256_pd(all(self.spare)), _mm256_castsi256_pd(left));
        _mm256_storeu_pd(buckets as *mut f64, _mm256_permute4x64_pd::<0b1101_1000>(bucket));
        _mm256_movemask_pd(_mm256_permute4x64_pd::<0b1101_1000>(_mm256_castsi256_pd(left))) as u32
    }
}

#[inline(always)]
pub fn stands(record: &Rec) -> bool {
    record.a >> 32 & INVALID != INVALID
}

#[inline(always)]
pub fn pay(record: &mut Rec, payload: Option<u32>) {
    match payload {
        Some(payload) => record.b |= u64::from(payload),
        None => record.a = record.a & 1 << 63 | INVALID << 32,
    }
}
