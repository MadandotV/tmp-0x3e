
use super::super::{slow, Calendar, BAD};
use super::codec::{decode_bytes, encode, order, scramble, unscramble, MASK, NONE};
use super::stamp::timestamp;

fn random(seed: u64) -> impl FnMut() -> u64 {
    let mut state = seed;
    move || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    }
}

fn fast(text: &[u8], calendar: &mut Calendar) -> Option<i64> {
    let mut padded = text.to_vec();
    padded.extend_from_slice(&[b','; 64]);
    let value = unsafe { timestamp(padded.as_ptr(), text.len(), calendar) };
    (value != BAD).then_some(value)
}

fn slow_value(text: &[u8]) -> Option<i64> {
    slow::timestamp(text).map(|value| if text.iter().all(u8::is_ascii_digit) { value.min(1 << 60) } else { value })
}

#[test]
fn timestamps_agree_with_the_slow_reference() {
    let mut calendar = Calendar::new();
    let mut next = random(0x9E37_79B9_7F4A_7C15);
    let seeds: [&[u8]; 12] = [
        b"2026-10-03T23:58:10Z",
        b"2026-10-03T19:58:10-04:00",
        b"2028-02-29T00:00:00+12:00",
        b"2027-02-28T23:59:59Z",
        b"1791071890000",
        b"0001791071890000",
        b"00000001791071890000",
        b"0000000000001791071890000",
        b"2026-12-31T23:59:59+23:59",
        b"2026-01-01T00:00:00-00:00",
        b"86400000",
        b"",
    ];
    let alphabet = b"0123456789-:TZ+tz .\r";
    let mut valid = 0;
    for seed in seeds {
        assert_eq!(fast(seed, &mut calendar), slow_value(seed), "{:?}", String::from_utf8_lossy(seed));
        for _ in 0..200_000 {
            let mut text = seed.to_vec();
            for _ in 0..1 + next() % 3 {
                if text.is_empty() {
                    break;
                }
                let at = (next() % text.len() as u64) as usize;
                match next() % 8 {
                    0 => {
                        text.remove(at);
                    }
                    1 => text.insert(at, alphabet[(next() % alphabet.len() as u64) as usize]),
                    2 => text[at] = text[at].wrapping_add(1),
                    3 => text[at] = text[at].wrapping_sub(1),
                    _ => text[at] = alphabet[(next() % alphabet.len() as u64) as usize],
                }
            }
            let expected = slow_value(&text);
            valid += usize::from(expected.is_some());
            assert_eq!(fast(&text, &mut calendar), expected, "{:?}", String::from_utf8_lossy(&text));
        }
    }
    assert!(valid > 100_000, "only {valid} valid timestamps were tried");
}

fn simple(id: &[u8], prefix: u8) -> u64 {
    if id.len() < 2 || id.len() > 9 || id[0] != prefix || (id[1] == b'0' && id.len() > 2) {
        return NONE;
    }
    let mut value = 0u64;
    for &byte in &id[1..] {
        let digit = match byte {
            b'0'..=b'9' => byte - b'0',
            b'a'..=b'z' => byte - b'a' + 10,
            _ => return NONE,
        };
        value = value * 36 + u64::from(digit);
    }
    if value > MASK {
        NONE
    } else {
        value
    }
}

#[test]
fn ids_round_trip_and_odd_ones_are_refused() {
    let mut next = random(0x1234_5678_9ABC_DEF1);
    for round in 0..2_000_000u64 {
        let value = match round % 4 {
            0 => next() & MASK,
            1 => next() % 36u64.pow(1 + (round % 8) as u32) & MASK,
            2 => round,
            _ => MASK - round,
        };
        let key = next();
        assert_eq!(unscramble(scramble(value, key), key), value);
        let mut text = [0u8; 16];
        let len = encode(b'e', value, &mut text);
        assert_eq!(decode_bytes(&text[..len], b'e'), value);
        assert_eq!(decode_bytes(&text[..len], b'u'), NONE);
        let mut odd = text[..len].to_vec();
        let at = (next() % len as u64) as usize;
        odd[at] = (next() % 256) as u8;
        assert_eq!(decode_bytes(&odd, b'e'), simple(&odd, b'e'), "{:?}", String::from_utf8_lossy(&odd));
        odd.insert(at, b'0');
        assert_eq!(decode_bytes(&odd, b'e'), simple(&odd, b'e'), "{:?}", String::from_utf8_lossy(&odd));
        let other = (next() & MASK) >> (round % 30);
        let mut second = [0u8; 16];
        let other_len = encode(b'e', other, &mut second);
        assert_eq!(text[..len].cmp(&second[..other_len]), order(value).cmp(&order(other)));
    }
    for id in [&b"e"[..], b"", b"e0", b"e00", b"e01", b"ezzzzzzzz", b"edzzzzzzz", b"ee0000000", b"E1", b"e1 ", b"e1234567890"] {
        assert_eq!(decode_bytes(id, b'e'), simple(id, b'e'), "{:?}", String::from_utf8_lossy(id));
    }
}
