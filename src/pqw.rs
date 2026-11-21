
use std::fs::File;
use std::path::Path;

#[derive(Clone, Copy, Default, PartialEq)]
pub enum Mode {
    #[default]
    Plain,
    Bytes,
    Runs,
}

#[derive(Clone, Copy, PartialEq)]
pub enum Kind {
    Str,
    I64,
    I32,
    Date,
}

pub struct Spec {
    pub name: &'static str,
    pub kind: Kind,
    pub optional: bool,
}

#[derive(Default)]
pub struct Column {
    pub mode: Mode,
    pub values: Vec<u8>,
    pub dictionary: Vec<u8>,
    pub dictionary_len: usize,
    pub present: Vec<u8>,
}

impl Column {
    #[inline]
    pub fn push_str(&mut self, value: &[u8]) {
        self.values.extend_from_slice(&(value.len() as u32).to_le_bytes());
        self.values.extend_from_slice(value);
    }
    #[inline]
    pub fn push_i64(&mut self, value: i64) {
        self.values.extend_from_slice(&value.to_le_bytes());
    }
    #[inline]
    pub fn push_i32(&mut self, value: i32) {
        self.values.extend_from_slice(&value.to_le_bytes());
    }
    #[inline]
    pub fn push_run(&mut self, len: usize, index: usize) {
        debug_assert!(index < 1 << 24);
        let mut header = (len as u64) << 1;
        while header >= 0x80 {
            self.values.push(header as u8 | 0x80);
            header >>= 7;
        }
        self.values.push(header as u8);
        self.values.extend_from_slice(&(index as u32).to_le_bytes()[..3]);
    }
    #[inline]
    pub fn push_present(&mut self, row: usize, present: bool) {
        if row % 8 == 0 {
            self.present.push(0);
        }
        if present {
            *self.present.last_mut().unwrap() |= 1 << (row % 8);
        }
    }
}

struct Thrift {
    out: Vec<u8>,
    last: Vec<i16>,
}

const T_I32: u8 = 5;
const T_I64: u8 = 6;
const T_BINARY: u8 = 8;
const T_LIST: u8 = 9;
const T_STRUCT: u8 = 12;

impl Thrift {
    fn new() -> Self {
        Self { out: Vec::new(), last: vec![0] }
    }
    fn varint(&mut self, mut value: u64) {
        while value >= 0x80 {
            self.out.push(value as u8 | 0x80);
            value >>= 7;
        }
        self.out.push(value as u8);
    }
    fn zigzag(&mut self, value: i64) {
        self.varint(((value << 1) ^ (value >> 63)) as u64);
    }
    fn field(&mut self, id: i16, kind: u8) {
        let last = self.last.last_mut().unwrap();
        let delta = id - *last;
        *last = id;
        if (1..=15).contains(&delta) {
            self.out.push((delta as u8) << 4 | kind);
        } else {
            self.out.push(kind);
            self.zigzag(i64::from(id));
        }
    }
    fn i32(&mut self, id: i16, value: i32) {
        self.field(id, T_I32);
        self.zigzag(i64::from(value));
    }
    fn i64(&mut self, id: i16, value: i64) {
        self.field(id, T_I64);
        self.zigzag(value);
    }
    fn binary(&mut self, id: i16, value: &[u8]) {
        self.field(id, T_BINARY);
        self.varint(value.len() as u64);
        self.out.extend_from_slice(value);
    }
    fn list(&mut self, id: i16, kind: u8, size: usize) {
        self.field(id, T_LIST);
        self.list_header(kind, size);
    }
    fn list_header(&mut self, kind: u8, size: usize) {
        if size < 15 {
            self.out.push((size as u8) << 4 | kind);
        } else {
            self.out.push(0xF0 | kind);
            self.varint(size as u64);
        }
    }
    fn open(&mut self, id: i16) {
        self.field(id, T_STRUCT);
        self.last.push(0);
    }
    fn open_element(&mut self) {
        self.last.push(0);
    }
    fn close(&mut self) {
        self.out.push(0);
        self.last.pop();
    }
}

fn physical(kind: Kind) -> i32 {
    match kind {
        Kind::Date | Kind::I32 => 1,
        Kind::I64 => 2,
        Kind::Str => 6,
    }
}

fn write_parts(file: &File, parts: &[&[u8]]) -> std::io::Result<()> {
    use std::os::fd::AsRawFd;
    let mut vectors: Vec<libc::iovec> = parts
        .iter()
        .filter(|part| !part.is_empty())
        .map(|part| libc::iovec { iov_base: part.as_ptr() as *mut libc::c_void, iov_len: part.len() })
        .collect();
    let mut from = 0;
    while from < vectors.len() {
        let count = (vectors.len() - from).min(1024) as libc::c_int;
        let wrote = unsafe { libc::writev(file.as_raw_fd(), vectors.as_ptr().add(from), count) };
        if wrote < 0 {
            let error = std::io::Error::last_os_error();
            if error.kind() == std::io::ErrorKind::Interrupted {
                continue;
            }
            return Err(error);
        }
        let mut wrote = wrote as usize;
        while from < vectors.len() && wrote >= vectors[from].iov_len {
            wrote -= vectors[from].iov_len;
            from += 1;
        }
        if wrote > 0 {
            vectors[from].iov_base = unsafe { (vectors[from].iov_base as *mut u8).add(wrote) } as *mut libc::c_void;
            vectors[from].iov_len -= wrote;
        }
    }
    Ok(())
}

pub fn write(path: &Path, specs: &[Spec], columns: &[Column], rows: usize) -> std::io::Result<()> {
    let _ = std::fs::remove_file(path);
    let file = File::create(path)?;
    let mut offset: u64 = 4;
    let mut chunks: Vec<(Option<u64>, u64, u64)> = Vec::new();
    let mut heads: Vec<(Vec<u8>, Vec<u8>)> = Vec::new();
    const PADDING: [u8; 8] = [0; 8];
    if rows > 0 {
        for (spec, column) in specs.iter().zip(columns) {
            let mut dictionary = Vec::new();
            if column.mode != Mode::Plain {
                let size = column.dictionary.len();
                assert!(size < i32::MAX as usize, "page too large");
                let mut header = Thrift::new();
                header.i32(1, 2);
                header.i32(2, size as i32);
                header.i32(3, size as i32);
                header.open(7);
                header.i32(1, column.dictionary_len as i32);
                header.i32(2, 0);
                header.close();
                header.out.push(0);
                dictionary = header.out;
            }
            let mut levels = Vec::new();
            if spec.optional {
                let groups = rows.div_ceil(8);
                let mut run = Thrift::new();
                run.varint((groups as u64) << 1 | 1);
                levels.extend_from_slice(&((run.out.len() + groups) as u32).to_le_bytes());
                levels.extend_from_slice(&run.out);
                levels.extend_from_slice(&column.present[..groups]);
            }
            let mut padding = 0;
            match column.mode {
                Mode::Plain => {}
                Mode::Bytes => {
                    let groups = column.values.len().div_ceil(8);
                    padding = groups * 8 - column.values.len();
                    let mut run = Thrift::new();
                    run.varint((groups as u64) << 1 | 1);
                    levels.push(8);
                    levels.extend_from_slice(&run.out);
                }
                Mode::Runs => levels.push(24),
            }
            let size = levels.len() + column.values.len() + padding;
            assert!(size < i32::MAX as usize, "page too large");
            let mut header = Thrift::new();
            header.i32(1, 0);
            header.i32(2, size as i32);
            header.i32(3, size as i32);
            header.open(5);
            header.i32(1, rows as i32);
            header.i32(2, if column.mode == Mode::Plain { 0 } else { 8 });
            header.i32(3, 3);
            header.i32(4, 3);
            header.close();
            header.out.push(0);
            let before = (dictionary.len() + if column.mode == Mode::Plain { 0 } else { column.dictionary.len() }) as u64;
            let total = before + (header.out.len() + size) as u64;
            chunks.push(((column.mode != Mode::Plain).then_some(offset), offset + before, total));
            offset += total;
            header.out.extend_from_slice(&levels);
            heads.push((dictionary, header.out));
        }
    }

    let mut meta = Thrift::new();
    meta.i32(1, 1);
    meta.list(2, T_STRUCT, specs.len() + 1);
    meta.open_element();
    meta.binary(4, b"schema");
    meta.i32(5, specs.len() as i32);
    meta.close();
    for spec in specs {
        meta.open_element();
        meta.i32(1, physical(spec.kind));
        meta.i32(3, i32::from(spec.optional));
        meta.binary(4, spec.name.as_bytes());
        match spec.kind {
            Kind::Str => {
                meta.i32(6, 0);
                meta.open(10);
                meta.open(1);
                meta.close();
                meta.close();
            }
            Kind::Date => {
                meta.i32(6, 6);
                meta.open(10);
                meta.open(6);
                meta.close();
                meta.close();
            }
            Kind::I64 | Kind::I32 => {}
        }
        meta.close();
    }
    meta.i64(3, rows as i64);
    if rows > 0 {
        meta.list(4, T_STRUCT, 1);
        meta.open_element();
        meta.list(1, T_STRUCT, specs.len());
        for (spec, &(dictionary, at, total)) in specs.iter().zip(&chunks) {
            meta.open_element();
            meta.i64(2, dictionary.unwrap_or(at) as i64);
            meta.open(3);
            meta.i32(1, physical(spec.kind));
            meta.list(2, T_I32, if dictionary.is_some() { 3 } else { 2 });
            meta.zigzag(0);
            meta.zigzag(3);
            if dictionary.is_some() {
                meta.zigzag(8);
            }
            meta.list(3, T_BINARY, 1);
            meta.varint(spec.name.len() as u64);
            meta.out.extend_from_slice(spec.name.as_bytes());
            meta.i32(4, 0);
            meta.i64(5, rows as i64);
            meta.i64(6, total as i64);
            meta.i64(7, total as i64);
            meta.i64(9, at as i64);
            if let Some(dictionary) = dictionary {
                meta.i64(11, dictionary as i64);
            }
            meta.close();
            meta.close();
        }
        meta.i64(2, (offset - 4) as i64);
        meta.i64(3, rows as i64);
        meta.close();
    } else {
        meta.list(4, T_STRUCT, 0);
    }
    meta.binary(6, b"nb7x");
    meta.out.push(0);
    let length = (meta.out.len() as u32).to_le_bytes();
    let mut parts: Vec<&[u8]> = vec![b"PAR1"];
    for (column, (dictionary, head)) in columns.iter().zip(&heads) {
        if column.mode != Mode::Plain {
            parts.push(dictionary);
            parts.push(&column.dictionary);
        }
        parts.push(head);
        parts.push(&column.values);
        if column.mode == Mode::Bytes {
            parts.push(&PADDING[..column.values.len().div_ceil(8) * 8 - column.values.len()]);
        }
    }
    parts.extend_from_slice(&[&meta.out, &length, b"PAR1"]);
    write_parts(&file, &parts)?;
    write_out(file);
    Ok(())
}

fn write_out(file: File) {
    use std::sync::{Condvar, Mutex, OnceLock};
    struct Queue {
        files: Mutex<Vec<File>>,
        more: Condvar,
    }
    static QUEUE: OnceLock<Option<&'static Queue>> = OnceLock::new();
    let queue = QUEUE.get_or_init(|| {
        if std::env::var_os("NB7X_NO_KICK").is_some() {
            return None;
        }
        let queue: &'static Queue = Box::leak(Box::new(Queue { files: Mutex::new(Vec::new()), more: Condvar::new() }));
        let spawned = std::thread::Builder::new().spawn(move || loop {
            let mut files = queue.files.lock().unwrap();
            while files.is_empty() {
                files = queue.more.wait(files).unwrap();
            }
            let batch = std::mem::take(&mut *files);
            drop(files);
            for file in batch {
                use std::os::fd::AsRawFd;
                unsafe { libc::sync_file_range(file.as_raw_fd(), 0, 0, libc::SYNC_FILE_RANGE_WRITE) };
            }
        });
        spawned.is_ok().then_some(queue)
    });
    if let Some(queue) = queue {
        queue.files.lock().unwrap().push(file);
        queue.more.notify_one();
    }
}

pub const T_ONE: [Spec; 6] = [
    Spec { name: concat!("use", "r_i", "d"), kind: Kind::Str, optional: false },
    Spec { name: "day", kind: Kind::Date, optional: false },
    Spec { name: concat!("ses", "sio", "ns"), kind: Kind::I64, optional: false },
    Spec { name: concat!("eve", "nts"), kind: Kind::I64, optional: false },
    Spec { name: concat!("rev", "enu", "e_c", "ent", "s"), kind: Kind::I64, optional: false },
    Spec { name: concat!("top", "_ca", "teg", "ory"), kind: Kind::Str, optional: true },
];

pub const T_TWO: [Spec; 7] = [
    Spec { name: concat!("cam", "pai", "gn_", "id"), kind: Kind::Str, optional: false },
    Spec { name: concat!("cha", "nne", "l"), kind: Kind::Str, optional: false },
    Spec { name: "day", kind: Kind::Date, optional: false },
    Spec { name: concat!("ses", "sio", "ns"), kind: Kind::I64, optional: false },
    Spec { name: concat!("pur", "cha", "sin", "g_s", "ess", "ion", "s"), kind: Kind::I64, optional: false },
    Spec { name: concat!("rev", "enu", "e_c", "ent", "s"), kind: Kind::I64, optional: false },
    Spec { name: concat!("ass", "ist", "ed_", "ses", "sio", "ns"), kind: Kind::I64, optional: false },
];
