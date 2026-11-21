
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

fn event_text(next: &mut dyn FnMut() -> u64, damage: bool) -> Vec<u8> {
    const DIGITS: &[u8; 36] = b"0123456789abcdefghijklmnopqrstuvwxyz";
    let pick = |next: &mut dyn FnMut() -> u64, count: u64| (next() % count) as usize;
    let id = |next: &mut dyn FnMut() -> u64, prefix: u8| {
        let mut text = if pick(next, 50) == 0 {
            let mut text = vec![prefix];
            for _ in 0..[0, 9, 8][pick(next, 3)] {
                text.push(DIGITS[pick(next, 36)]);
            }
            text
        } else {
            let mut buffer = [0u8; 16];
            let len = encode(prefix, (next() & MASK) >> [0, 0, 0, 0, 3, 36, 0, 8][pick(next, 8)], &mut buffer);
            buffer[..len].to_vec()
        };
        if pick(next, 200) == 0 {
            text.make_ascii_uppercase();
        }
        text
    };
    let second = |next: &mut dyn FnMut() -> u64| format!("2026-{:02}-{:02}T{:02}:{:02}:{:02}", 9 + pick(next, 2), 1 + pick(next, 30), pick(next, 24), pick(next, 60), pick(next, 60));
    let ts: Vec<u8> = match pick(next, 40) {
        0..=19 => format!("{}Z", second(next)).into_bytes(),
        20..=24 => format!("{}{}{:02}:{:02}", second(next), ["+", "-"][pick(next, 2)], pick(next, 14), [0, 30, 45][pick(next, 3)]).into_bytes(),
        25..=36 => format!("{}", 1_791_000_000_000u64 + next() % 2_000_000_000).into_bytes(),
        37 | 38 => format!("{:0>1$}", next() % 1_000_000, 1 + pick(next, 26)).into_bytes(),
        _ => [&b""[..], b"2026-10-03 23:58:10Z", b"2026-13-03T23:58:10Z", b"1.79e12", b"-5", b"2026-10-03T23:58:10"][pick(next, 6)].to_vec(),
    };
    let kind = if pick(next, 20) == 0 {
        [&b"Purchase"[..], b"cart ", b"", b"views"][pick(next, 4)]
    } else {
        [&b"view"[..], b"view", b"cart", b"purchase"][pick(next, 4)]
    };
    let product: Vec<u8> = match pick(next, 40) {
        0 => Vec::new(),
        1 => b"P17".to_vec(),
        _ => format!("p{}", 1 + next() % 99_999).into_bytes(),
    };
    let price: Vec<u8> = match pick(next, 6) {
        0..=2 => Vec::new(),
        3 => [&b"19.99"[..], b"-5", b"0", b"250000000", b"00"][pick(next, 5)].to_vec(),
        _ => format!("{}", 100 + next() % 50_000).into_bytes(),
    };
    let ingest = if pick(next, 50) == 0 { second(next).into_bytes() } else { format!("{}Z", second(next)).into_bytes() };
    let fields = [id(next, b'e'), id(next, b'u'), ts, ingest, kind.to_vec(), product, price];
    let mut line = Vec::new();
    for (at, field) in fields.iter().enumerate() {
        if at > 0 {
            line.push(b',');
        }
        let quote = pick(next, 5) == 0;
        if quote {
            line.push(b'"');
        }
        line.extend_from_slice(field);
        if quote {
            line.push(b'"');
        }
    }
    if damage {
        let odd = b"\",\n\r 0aZ:-e";
        for _ in 0..1 + pick(next, 2) {
            let at = pick(next, line.len() as u64 + 1);
            match pick(next, 6) {
                0 if at < line.len() => {
                    line.remove(at);
                }
                1 if at < line.len() => line[at] = odd[pick(next, odd.len() as u64)],
                2 => line.truncate(at),
                3 => line.extend_from_slice(b",x"),
                _ => line.insert(at, odd[pick(next, odd.len() as u64)]),
            }
        }
    }
    line
}

#[test]
fn the_fused_reader_accepts_only_what_the_general_one_reads_the_same() {
    use super::codec::decode;
    use super::lines::{fused, split};
    use super::stamp::civil;
    let mut next = random(0xF00D_FACE_0BAD_CAFE);
    let (mut fast_calendar, mut calendar) = (Calendar::new(), Calendar::new());
    let (mut clean, mut clean_taken, mut damaged_taken) = (0u64, 0u64, 0u64);
    for round in 0..6_000_000u64 {
        let damage = round % 3 != 0;
        let mut text = event_text(&mut next, damage);
        text.push(b'\n');
        if round % 7 != 0 {
            text.extend_from_slice(&event_text(&mut next, false));
            text.push(b'\n');
        }
        text.extend_from_slice(&[0u8; 320]);
        let at = text.as_ptr();
        let shown = || String::from_utf8_lossy(&text[..text.len() - 320]).into_owned();
        let Some((len, line)) = (unsafe { fused(at, &mut fast_calendar) }) else {
            clean += u64::from(!damage);
            continue;
        };
        clean += u64::from(!damage);
        clean_taken += u64::from(!damage);
        damaged_taken += u64::from(damage);
        let (plain_len, fields) = unsafe { split(at) };
        let fields = fields.unwrap_or_else(|| panic!("accepted a malformed line: {:?}", shown()));
        assert_eq!(len, plain_len, "{:?}", shown());
        assert_eq!((line.id, line.user, line.product, line.price), (fields[0], fields[1], fields[5], fields[6]), "{:?}", shown());
        unsafe {
            assert_eq!(line.event, decode(fields[0].0, fields[0].1, b'e'), "{:?}", shown());
            assert_eq!(line.who, decode(fields[1].0, fields[1].1, b'u'), "{:?}", shown());
            assert!(line.event != NONE && line.who != NONE, "{:?}", shown());
            assert_eq!(fields[3].1, 20, "{:?}", shown());
            assert_eq!(line.ingest, civil::<1>(fields[3].0, &mut calendar), "{:?}", shown());
            assert_eq!(line.ts, timestamp(fields[2].0, fields[2].1, &mut calendar), "{:?}", shown());
            assert!(line.ingest != BAD && line.ts != BAD && fields[5].1 > 0, "{:?}", shown());
            let kind = std::slice::from_raw_parts(fields[4].0, fields[4].1);
            assert!(if line.purchase { kind == b"purchase" } else { kind == b"view" || kind == b"cart" }, "{:?}", shown());
        }
    }
    assert!(damaged_taken > 100_000, "only {damaged_taken} damaged lines were still accepted");
    assert!(clean_taken * 10 > clean * 7, "only {clean_taken} of {clean} clean lines were accepted");
}

#[test]
fn two_ids_at_once_read_as_one_at_a_time() {
    use super::codec::{decode, decode2};
    let mut next = random(0x0BAD_5EED_1234_5678);
    let alphabet = b"0123456789abcdefghijklmnopqrstuvwxyzEU\"`{/: W";
    let mut both = 0u64;
    for _ in 0..4_000_000 {
        let mut make = |prefix: u8| {
            let mut text = vec![0u8; 16];
            let len = encode(prefix, (next() & MASK) >> [0, 0, 0, 5, 20, 36][(next() % 6) as usize], (&mut text[..]).try_into().unwrap());
            text.truncate(len);
            match next() % 12 {
                0 => text[(next() % len as u64) as usize] = alphabet[(next() % alphabet.len() as u64) as usize],
                1 => text.insert((next() % (len as u64 + 1)) as usize, alphabet[(next() % alphabet.len() as u64) as usize]),
                2 => text.truncate((next() % len as u64) as usize),
                3 => text.extend_from_slice(b"zz"),
                _ => {}
            }
            let len = text.len();
            text.extend_from_slice(&[b','; 32]);
            (text, len)
        };
        let ((a, a_len), (b, b_len)) = (make(b'e'), make(b'u'));
        let (ok, one, two) = unsafe { decode2::<b'e', b'u'>(a.as_ptr(), a_len, b.as_ptr(), b_len) };
        let each = unsafe { (decode(a.as_ptr(), a_len, b'e'), decode(b.as_ptr(), b_len, b'u')) };
        let shown = (String::from_utf8_lossy(&a[..a_len]).into_owned(), String::from_utf8_lossy(&b[..b_len]).into_owned());
        assert_eq!(ok, each.0 != NONE && each.1 != NONE, "{shown:?}");
        if ok {
            assert_eq!((one, two), each, "{shown:?}");
            both += 1;
        }
    }
    assert!(both > 1_000_000);
}
