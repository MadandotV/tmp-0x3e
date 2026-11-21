
use std::fs;
use std::path::Path;

pub struct Source {
    pub file: Option<fs::File>,
    pub len: usize,
    map: *mut u8,
}

unsafe impl Send for Source {}
unsafe impl Sync for Source {}

const PAGE: usize = 4096;

pub fn chunk() -> usize {
    use std::sync::OnceLock;
    static CHUNK: OnceLock<usize> = OnceLock::new();
    *CHUNK.get_or_init(|| {
        let asked = std::env::var("NB7X_CHUNK_KB").ok().and_then(|value| value.parse::<usize>().ok());
        asked.map_or(if mapped() { 4 << 20 } else { 1 << 18 }, |kb| kb.max(64) << 10)
    })
}

fn mapped() -> bool {
    std::env::var_os("NB7X_READ").is_none()
}

pub fn open(path: &Path) -> Source {
    use std::os::fd::AsRawFd;
    let file = fs::File::open(path).unwrap();
    let len = file.metadata().unwrap().len() as usize;
    if len == 0 || !mapped() {
        return Source { file: Some(file), len, map: std::ptr::null_mut() };
    }
    unsafe {
        const HUGE: usize = 2 << 20;
        let room = len.next_multiple_of(PAGE) + 2 * PAGE + HUGE;
        let protection = libc::PROT_READ | libc::PROT_WRITE;
        let whole = libc::mmap(std::ptr::null_mut(), room, protection, libc::MAP_PRIVATE | libc::MAP_ANONYMOUS | libc::MAP_NORESERVE, -1, 0);
        if whole == libc::MAP_FAILED {
            return Source { file: Some(file), len, map: std::ptr::null_mut() };
        }
        let at = (whole as usize + PAGE).next_multiple_of(HUGE) as *mut libc::c_void;
        if libc::mmap(at, len, protection, libc::MAP_PRIVATE | libc::MAP_FIXED, file.as_raw_fd(), 0) == libc::MAP_FAILED {
            libc::munmap(whole, room);
            return Source { file: Some(file), len, map: std::ptr::null_mut() };
        }
        Source { file: None, len, map: at as *mut u8 }
    }
}

impl Source {
    pub fn len(&self) -> u64 {
        self.len as u64
    }

    pub unsafe fn window(&self, from: usize, to: usize) -> Option<(*const u8, usize, usize)> {
        if self.map.is_null() {
            return None;
        }
        let origin = from.saturating_sub(1);
        let base = self.map.add(origin);
        let have = self.len - origin;
        let mut start = 0;
        if from > 0 {
            while start < have && *base.add(start) != b'\n' {
                start += 1;
            }
            start += 1;
            if start >= to - origin {
                return Some((base, 0, 0));
            }
        }
        let mut end = to - origin;
        if to < self.len {
            end -= 1;
            while end < have && *base.add(end) != b'\n' {
                end += 1;
            }
            end = (end + 1).min(have);
        }
        if start >= end {
            return Some((base, 0, 0));
        }
        if *base.add(end - 1) != b'\n' {
            *base.add(end) = b'\n';
            end += 1;
        }
        if std::env::var_os("NB7X_POPULATE").is_some() {
            let first = (base as usize + start) & !(PAGE - 1);
            libc::madvise(first as *mut libc::c_void, base as usize + end - first, libc::MADV_POPULATE_READ);
        }
        Some((base, start, end))
    }
}

pub unsafe fn release(from: usize, to: usize) {
    let first = from.next_multiple_of(PAGE);
    let last = to & !(PAGE - 1);
    if last > first {
        libc::madvise(first as *mut libc::c_void, last - first, libc::MADV_DONTNEED);
    }
}
