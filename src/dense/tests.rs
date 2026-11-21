
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
fn the_row_reader_takes_only_what_the_general_one_reads_the_same() {
    use super::codec::decode;
    use super::lines::split;
    use super::rows::{read, Days, Rows, PURCHASE};
    use super::stamp::civil;
    let mut next = random(0xF00D_FACE_0BAD_CAFE);
    let mut days = Days::new();
    let mut rows = Rows::new();
    let mut calendar = Calendar::new();
    let (mut clean, mut clean_taken, mut damaged_taken, mut purchases) = (0u64, 0u64, 0u64, 0u64);
    for round in 0..8_000_000u64 {
        let damage = round % 3 != 0;
        let mut text = if round % 5 == 0 { vec![0u8; 64] } else { [&[b'\n'; 40][..], &event_text(&mut next, false), b"\n"].concat() };
        let start = text.len();
        text.extend_from_slice(&event_text(&mut next, damage));
        text.push(b'\n');
        let stop = text.len();
        if round % 7 != 0 {
            text.extend_from_slice(&event_text(&mut next, false));
            text.push(b'\n');
        }
        text.extend_from_slice(&[0u8; 320]);
        let at = unsafe { text.as_ptr().add(start) };
        let shown = || String::from_utf8_lossy(&text[start..stop]).into_owned();
        let (plain_len, fields) = unsafe { split(at) };
        let row = (round % 64) as usize;
        let mut len = unsafe { read(at, &days, &mut rows, row) };
        if len == 0 {
            if let Some(fields) = fields {
                for field in [fields[2], fields[3]] {
                    if field.1 >= 10 {
                        unsafe { days.learn(field.0) };
                    }
                }
            }
            len = unsafe { read(at, &days, &mut rows, row) };
        }
        clean += u64::from(!damage);
        if len == 0 {
            continue;
        }
        clean_taken += u64::from(!damage);
        damaged_taken += u64::from(damage);
        let fields = fields.unwrap_or_else(|| panic!("took a malformed line: {:?}", shown()));
        assert_eq!(len, plain_len, "{:?}", shown());
        let ([event, who], [ts, ingest], line) = (rows.ids[row], rows.times[row], rows.lines[row]);
        assert_eq!(line & !PURCHASE, at as u64);
        unsafe {
            assert_eq!(event, decode(fields[0].0, fields[0].1, b'e'), "{:?}", shown());
            assert_eq!(who, decode(fields[1].0, fields[1].1, b'u'), "{:?}", shown());
            assert!(event != NONE && who != NONE, "{:?}", shown());
            assert_eq!(fields[3].1, 20, "{:?}", shown());
            let plain_ingest = civil::<1>(fields[3].0, &mut calendar);
            assert!(plain_ingest != BAD, "{:?}", shown());
            assert_eq!(ingest, plain_ingest, "{:?}", shown());
            let plain_ts = timestamp(fields[2].0, fields[2].1, &mut calendar);
            assert!(plain_ts != BAD && fields[5].1 > 0, "{:?}", shown());
            assert_eq!(ts, plain_ts, "{:?}", shown());
            let kind = std::slice::from_raw_parts(fields[4].0, fields[4].1);
            if line & PURCHASE == 0 {
                assert!(kind == b"view" || kind == b"cart", "{:?}", shown());
            } else {
                purchases += 1;
                assert!(kind == b"purchase", "{:?}", shown());
            }
        }
    }
    assert!(damaged_taken > 100_000, "only {damaged_taken} damaged lines were still taken");
    assert!(purchases > 100_000, "only {purchases} purchases were taken");
    assert!(clean_taken * 10 > clean * 8, "only {clean_taken} of {clean} clean lines were taken");
}

#[test]
fn four_rows_at_once_make_the_records_of_one_at_a_time() {
    use super::sink::Frame;
    use super::{Rec, EMPTY};
    let mut next = random(0x5EED_0F_F0_0D_1234);
    let (mut made, mut left_out) = (0u64, 0u64);
    for round in 0..600_000u64 {
        let window_start = 1_700_000_000_000 + (next() % 1_000_000_000) as i64;
        let window_end = window_start + 1 + (next() % (1 << 30)) as i64;
        let frame = Frame {
            user_key: next() & MASK,
            event_key: next() & MASK,
            user_bound: 1 + next() % (1 << [31, 31, 20, 40][(next() % 4) as usize]),
            event_bound: 1 + next() % (1 << [29, 40, 39, 25][(next() % 4) as usize]),
            ingest_start: window_start.div_euclid(1000) - 172_800,
            window_start,
            window_end,
            spare: 1 << 40,
        };
        let (mut ids, mut times, mut marks) = ([[0u64; 2]; 4], [[0i64; 2]; 4], [0u64; 4]);
        for row in 0..4 {
            let number = |next: &mut dyn FnMut() -> u64, bound: u64, key: u64| match next() % 8 {
                0 => next() & MASK,
                1 => scramble(bound.wrapping_sub(next() % 3) & MASK, key),
                2 => scramble((bound + next() % 3) & MASK, key),
                _ => scramble(next() % bound, key),
            };
            ids[row] = [number(&mut next, frame.event_bound, frame.event_key), number(&mut next, frame.user_bound, frame.user_key)];
            let span = window_end - window_start;
            let ts = match next() % 10 {
                0 => window_start - 1 - (next() % 3) as i64,
                1 => window_start + (next() % 3) as i64,
                2 => window_end - 1 - (next() % 3) as i64,
                3 => window_end + (next() % 3) as i64,
                4 => (next() % 10_000_000_000_000_000) as i64,
                5 => -((next() % 60_000_000_000_000) as i64),
                _ => window_start + (next() % span as u64) as i64,
            };
            let ingest = match next() % 12 {
                0 => frame.ingest_start - (next() % 3) as i64,
                1 => frame.ingest_start + (1 << 21) - 3 + (next() % 5) as i64,
                2 => (next() % 250_000_000_000) as i64 - 62_000_000_000,
                3 => ts.div_euclid(1000) + 86_400 - 1 + (next() % 3) as i64,
                4 => (ts + 86_400_000).div_euclid(1000) + (next() % 2) as i64,
                _ => ts.div_euclid(1000) + (next() % 600) as i64,
            };
            times[row] = [ts, ingest];
            marks[row] = (next() >> 1) | u64::from(next() % 16 == 0) << 63;
        }
        let mut records = [EMPTY; 4];
        let mut buckets = [0u64; 4];
        let left = unsafe { frame.four(ids.as_ptr(), times.as_ptr(), marks.as_ptr(), records.as_mut_ptr(), buckets.as_mut_ptr()) };
        assert!(left < 16);
        for row in 0..4 {
            let one = frame.one(ids[row][0], ids[row][1], times[row][0], times[row][1], Some(0));
            let shown = (round, row, ids[row], times[row]);
            if left >> row & 1 != 0 {
                assert!(one.is_none() || marks[row] >> 63 != 0, "{shown:?}");
                assert_eq!(buckets[row], frame.spare, "{shown:?}");
                left_out += 1;
            } else {
                let (bucket, Rec { a, b }) = one.unwrap_or_else(|| panic!("made a record of {shown:?}"));
                assert!(marks[row] >> 63 == 0, "{shown:?}");
                assert_eq!((buckets[row] as usize, records[row].a, records[row].b), (bucket, a, b), "{shown:?}");
                made += 1;
            }
        }
    }
    assert!(made > 500_000 && left_out > 500_000, "{made} made, {left_out} left");
}

#[test]
fn the_click_reader_takes_only_what_the_general_one_reads_the_same() {
    use super::super::canonical_at;
    use super::codec::decode;
    use super::lines::split_click;
    use super::rows::{read_click, Days, NO_CLICK};
    let mut next = random(0xC11C_C11C_0BAD_CAFE);
    let mut days = Days::new();
    let mut calendar = Calendar::new();
    let (mut clean, mut clean_taken, mut damaged_taken) = (0u64, 0u64, 0u64);
    let mut click_text = |next: &mut dyn FnMut() -> u64, damage: bool| {
        let event = event_text(next, false);
        let mut fields: Vec<Vec<u8>> = event.split(|&byte| byte == b',').take(3).map(|field| field.to_vec()).collect();
        for byte in fields[0].iter_mut().filter(|byte| **byte == b'e').take(1) {
            *byte = b'k';
        }
        let campaign: Vec<u8> = match next() % 40 {
            0 => b"c_0".to_vec(),
            1 => b"c_017".to_vec(),
            2 => b"x_17".to_vec(),
            3 => b"c_1234567".to_vec(),
            4 => Vec::new(),
            5 => b"c_".to_vec(),
            6 => b"c_12a".to_vec(),
            _ => format!("c_{}", next() % [10, 100, 1000, 10_000, 100_000, 1_000_000][(next() % 6) as usize]).into_bytes(),
        };
        let quoted = next() % 5 == 0;
        let mut line = [&fields[0][..], b",", &fields[1], b","].concat();
        if quoted {
            line.push(b'"');
        }
        line.extend_from_slice(&campaign);
        if quoted {
            line.push(b'"');
        }
        line.push(b',');
        line.extend_from_slice(&fields[2]);
        if damage {
            let odd = b"\",\n\r 0aZ:-kc_";
            for _ in 0..1 + next() % 2 {
                let at = (next() % (line.len() as u64 + 1)) as usize;
                match next() % 6 {
                    0 if at < line.len() => {
                        line.remove(at);
                    }
                    1 if at < line.len() => line[at] = odd[(next() % odd.len() as u64) as usize],
                    2 => line.truncate(at),
                    3 => line.extend_from_slice(b",x"),
                    _ => line.insert(at, odd[(next() % odd.len() as u64) as usize]),
                }
            }
        }
        line
    };
    for round in 0..8_000_000u64 {
        let damage = round % 3 != 0;
        let mut text = if round % 5 == 0 { vec![0u8; 64] } else { [&[b'\n'; 40][..], &click_text(&mut next, false), b"\n"].concat() };
        let start = text.len();
        text.extend_from_slice(&click_text(&mut next, damage));
        text.push(b'\n');
        let stop = text.len();
        if round % 7 != 0 {
            text.extend_from_slice(&click_text(&mut next, false));
            text.push(b'\n');
        }
        text.extend_from_slice(&[0u8; 320]);
        let at = unsafe { text.as_ptr().add(start) };
        let shown = || String::from_utf8_lossy(&text[start..stop]).into_owned();
        let (plain_len, fields) = unsafe { split_click(at) };
        let mut row = NO_CLICK;
        let mut len = unsafe { read_click(at, &days, &mut row) };
        if len == 0 {
            if let Some(fields) = fields {
                if fields[3].1 >= 10 {
                    unsafe { days.learn(fields[3].0) };
                }
            }
            len = unsafe { read_click(at, &days, &mut row) };
        }
        clean += u64::from(!damage);
        if len == 0 {
            continue;
        }
        clean_taken += u64::from(!damage);
        damaged_taken += u64::from(damage);
        let fields = fields.unwrap_or_else(|| panic!("took a malformed line: {:?}", shown()));
        assert_eq!(len, plain_len, "{:?}", shown());
        assert_eq!(row.line, at);
        unsafe {
            assert_eq!(row.id, decode(fields[0].0, fields[0].1, b'k'), "{:?}", shown());
            assert_eq!(row.who, decode(fields[1].0, fields[1].1, b'u'), "{:?}", shown());
            assert!(row.id != NONE && row.who != NONE, "{:?}", shown());
            let ts = timestamp(fields[3].0, fields[3].1, &mut calendar);
            assert!(ts != BAD, "{:?}", shown());
            assert_eq!(row.ts, ts, "{:?}", shown());
            let campaign = std::slice::from_raw_parts(fields[2].0, fields[2].1);
            assert!(campaign.len() >= 3 && campaign.starts_with(b"c_"), "{:?}", shown());
            let number = canonical_at(fields[2].0, fields[2].1, 2);
            assert!(number != usize::MAX, "{:?}", shown());
            assert_eq!(row.campaign, number as u64, "{:?}", shown());
        }
    }
    assert!(damaged_taken > 100_000, "only {damaged_taken} damaged lines were still taken");
    assert!(clean_taken * 10 > clean * 6, "only {clean_taken} of {clean} clean lines were taken");
}
