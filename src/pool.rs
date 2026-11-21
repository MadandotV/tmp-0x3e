
use std::cell::UnsafeCell;
use std::sync::atomic::{AtomicBool, AtomicU32, AtomicU64, AtomicUsize, Ordering::SeqCst};

type Job = &'static (dyn Fn(usize) + Sync);

static STAGE: AtomicU32 = AtomicU32::new(0);
static FINISHED: AtomicU32 = AtomicU32::new(0);
static ASLEEP: AtomicU32 = AtomicU32::new(0);
static CALLER_ASLEEP: AtomicBool = AtomicBool::new(false);
static WORKERS: AtomicUsize = AtomicUsize::new(0);
static mut JOB: Option<Job> = None;
static mut WANTED: usize = 0;
static mut ALLOWED: [u64; 16] = [0; 16];
static PINNED: AtomicBool = AtomicBool::new(false);

static ENDED: [AtomicU64; 16] = [const { AtomicU64::new(0) }; 16];
static POSTED: AtomicU64 = AtomicU64::new(0);

pub fn idle() -> u64 {
    let (from, threads) = (POSTED.load(SeqCst), unsafe { WANTED }.min(16));
    let ends: Vec<u64> = (0..threads).map(|index| ENDED[index].load(SeqCst).saturating_sub(from)).collect();
    let last = ends.iter().copied().max().unwrap_or(0).max(1);
    ends.iter().map(|&end| last - end).sum::<u64>() * 100 / (last * threads.max(1) as u64)
}

static STAGED: AtomicU64 = AtomicU64::new(0);
pub fn staged_ticks() -> u64 {
    STAGED.load(SeqCst)
}
pub fn now_ticks() -> u64 {
    ticks()
}

const SPIN_TICKS: u64 = 1_000_000;

#[inline(always)]
fn ticks() -> u64 {
    unsafe { std::arch::x86_64::_rdtsc() }
}

unsafe fn futex(word: &AtomicU32, operation: libc::c_int, value: u32) {
    libc::syscall(libc::SYS_futex, word.as_ptr(), operation | libc::FUTEX_PRIVATE_FLAG, value, 0usize, 0usize, 0usize);
}

fn cpu_order() -> Vec<usize> {
    let mask = unsafe { &*std::ptr::addr_of!(ALLOWED) };
    let allowed = |cpu: usize| cpu < 1024 && mask[cpu / 64] >> (cpu % 64) & 1 != 0;
    let mut first = Vec::new();
    let mut rest = Vec::new();
    let mut seen = [false; 1024];
    for cpu in (0..1024).filter(|&cpu| allowed(cpu)) {
        if seen[cpu] {
            continue;
        }
        seen[cpu] = true;
        first.push(cpu);
        let path = format!("/sys/devices/system/cpu/cpu{cpu}/topology/thread_siblings_list");
        let Ok(text) = std::fs::read_to_string(path) else { continue };
        for part in text.trim().split(',') {
            let mut ends = part.split('-').filter_map(|end| end.parse::<usize>().ok());
            let Some(from) = ends.next() else { continue };
            let to = ends.next().unwrap_or(from);
            for sibling in from..=to.min(1023) {
                if allowed(sibling) && !seen[sibling] {
                    seen[sibling] = true;
                    rest.push(sibling);
                }
            }
        }
    }
    first.extend(rest);
    first
}

fn pin(cpu: usize) {
    let mut mask = [0u64; 16];
    mask[cpu / 64] |= 1 << (cpu % 64);
    unsafe { libc::syscall(libc::SYS_sched_setaffinity, 0, 128usize, mask.as_ptr()) };
}

pub fn start(threads: usize) {
    if threads < 2 || WORKERS.load(SeqCst) != 0 {
        return;
    }
    let order = unsafe {
        let got = libc::syscall(libc::SYS_sched_getaffinity, 0, 128usize, std::ptr::addr_of_mut!(ALLOWED));
        if got > 0 && std::env::var_os("NB7X_PIN").is_some() { cpu_order() } else { Vec::new() }
    };
    let order = if order.len() >= threads { order } else { Vec::new() };
    for index in 1..threads {
        let cpu = order.get(index).copied();
        let spawned = std::thread::Builder::new().spawn(move || {
            if let Some(cpu) = cpu {
                pin(cpu);
            }
            worker(index)
        });
        if spawned.is_err() {
            break;
        }
        WORKERS.fetch_add(1, SeqCst);
    }
    if let Some(&cpu) = order.first() {
        pin(cpu);
        PINNED.store(true, SeqCst);
    }
}

pub fn threads() -> usize {
    WORKERS.load(SeqCst) + 1
}

pub fn unpin() {
    if PINNED.swap(false, SeqCst) {
        unsafe { libc::syscall(libc::SYS_sched_setaffinity, 0, 128usize, std::ptr::addr_of!(ALLOWED)) };
    }
}

fn worker(index: usize) {
    let mut seen = 0;
    loop {
        let since = ticks();
        loop {
            let stage = STAGE.load(SeqCst);
            if stage != seen {
                seen = stage;
                break;
            }
            if ticks().wrapping_sub(since) < SPIN_TICKS {
                std::hint::spin_loop();
                continue;
            }
            ASLEEP.fetch_add(1, SeqCst);
            unsafe { futex(&STAGE, libc::FUTEX_WAIT, stage) };
            ASLEEP.fetch_sub(1, SeqCst);
        }
        unsafe {
            if index < WANTED {
                if let Some(job) = JOB {
                    job(index);
                    if index < 16 {
                        ENDED[index].store(ticks(), SeqCst);
                    }
                }
            }
        }
        FINISHED.fetch_add(1, SeqCst);
        if CALLER_ASLEEP.load(SeqCst) {
            unsafe { futex(&FINISHED, libc::FUTEX_WAKE, 1) };
        }
    }
}

pub fn run<F: Fn(usize) + Sync>(threads: usize, job: F) {
    let workers = WORKERS.load(SeqCst);
    if threads <= 1 {
        job(0);
        return;
    }
    if threads > workers + 1 {
        std::thread::scope(|scope| {
            for index in 1..threads {
                let job = &job;
                scope.spawn(move || job(index));
            }
            job(0);
        });
        return;
    }
    unsafe {
        let borrowed: &(dyn Fn(usize) + Sync) = &job;
        JOB = Some(std::mem::transmute::<&(dyn Fn(usize) + Sync), Job>(borrowed));
        WANTED = threads;
    }
    POSTED.store(ticks(), SeqCst);
    FINISHED.store(0, SeqCst);
    STAGE.fetch_add(1, SeqCst);
    if ASLEEP.load(SeqCst) != 0 {
        unsafe { futex(&STAGE, libc::FUTEX_WAKE, i32::MAX as u32) };
    }
    job(0);
    ENDED[0].store(ticks(), SeqCst);
    let since = ticks();
    loop {
        let finished = FINISHED.load(SeqCst);
        if finished as usize == workers {
            break;
        }
        if ticks().wrapping_sub(since) < SPIN_TICKS {
            std::hint::spin_loop();
            continue;
        }
        CALLER_ASLEEP.store(true, SeqCst);
        if FINISHED.load(SeqCst) == finished {
            unsafe { futex(&FINISHED, libc::FUTEX_WAIT, finished) };
        }
        CALLER_ASLEEP.store(false, SeqCst);
    }
    STAGED.fetch_add(ticks().wrapping_sub(POSTED.load(SeqCst)), SeqCst);
    unsafe { JOB = None };
}

struct Slots<T>(Vec<UnsafeCell<Option<T>>>);
unsafe impl<T: Send> Sync for Slots<T> {}
impl<T> Slots<T> {
    fn at(&self, index: usize) -> *mut Option<T> {
        self.0[index].get()
    }
}

pub fn map<T: Send, F: Fn(usize) -> T + Sync>(threads: usize, job: F) -> Vec<T> {
    let slots = Slots((0..threads.max(1)).map(|_| UnsafeCell::new(None)).collect());
    let filled = &slots;
    run(threads, |index| unsafe { *filled.at(index) = Some(job(index)) });
    slots.0.into_iter().map(|slot| slot.into_inner().unwrap()).collect()
}

pub fn consume<S: Send, T: Send, F: Fn(usize, S) -> T + Sync>(items: Vec<S>, job: F) -> Vec<T> {
    let threads = items.len();
    let items = Slots(items.into_iter().map(|item| UnsafeCell::new(Some(item))).collect());
    let items = &items;
    map(threads, |index| job(index, unsafe { (*items.at(index)).take().unwrap() }))
}

pub fn each<S: Send, F: Fn(usize, &mut S) + Sync>(items: &mut [S], job: F) {
    struct Base<S>(*mut S);
    unsafe impl<S: Send> Sync for Base<S> {}
    let base = Base(items.as_mut_ptr());
    impl<S> Base<S> {
        fn at(&self, index: usize) -> *mut S {
            unsafe { self.0.add(index) }
        }
    }
    let base = &base;
    run(items.len(), |index| job(index, unsafe { &mut *base.at(index) }));
}

pub fn fill<T: Send, F: Fn(usize) -> T + Sync>(threads: usize, count: usize, job: F) -> Vec<T> {
    let slots = Slots((0..count).map(|_| UnsafeCell::new(None)).collect());
    let next = AtomicUsize::new(0);
    let filled = &slots;
    run(threads.min(count), |_| loop {
        let index = next.fetch_add(1, SeqCst);
        if index >= count {
            break;
        }
        unsafe { *filled.at(index) = Some(job(index)) };
    });
    slots.0.into_iter().map(|slot| slot.into_inner().unwrap()).collect()
}
