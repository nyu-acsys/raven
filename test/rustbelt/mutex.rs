#![feature(register_tool)]
#![register_tool(rr)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
// inspired by https://whenderson.dev/blog/rust-mutexes/

use std::thread;
use std::sync::atomic::Ordering;
use std::marker::PhantomData;
use std::sync::atomic::AtomicBool;

use std::ops::{Deref};

// We have some sort of resource algebra MaxAuthNat:
// type CompletedNat = data {
//   case bot();
//   case exact(n: Int);
//   case top();
// }
//
// type CounterRA = data {
//   case pair(left: CompletedNat, right: Nat)
// }
//
// And the operation · is described
// (bot, n)·(x, m) == (x, max(n, m))
// (y, n)·(bot, m) == (y, max(n, m))
// (_, n)·(_, m) == (top, max(n, m)) otherwise
// where valid is true if the left hand side is bot, or if the right hand side lower bounds the left,
// and fpu is allowed for the following situation: (exact(n), m) ~> (exact(n + r), m + r)

// based on the following:
// https://iris-project.org/tutorial-pdfs/lecture12-counter-modules.pdf

#[rr::refined_by("(ℓval, iFloor)" : "(Ref * Int)")]
#[rr::invariant(#own "ℓval" : "pair(bot, iFloor)")]
#[rr::invariant(#type "ℓval" : "pair(bot, iFloor)" @ "CounterRA")]
#[derive(Copy, Clone)]
pub struct Mutex {
    #[rr::field("ℓval")]
    inner: *mut i64,
    status: *mut AtomicBool,
    #[rr::field("iFloor")]
    _val: PhantomData<i64>
}


unsafe impl Send for Mutex {}
unsafe impl Sync for Mutex {}

#[rr::refined_by("(ℓval, iFloor, iAuth)" : "(Ref * Int * Int)")]
#[rr::exists("iAuth" : "Int")]
#[rr::invariant(#own "ℓval" : "pair(exact(iAuth), iFloor)")]
#[rr::invariant(#type "ℓval" : "pair(exact(iAuth), iFloor)" @ "CounterRA")] // implying iFloor <= iAuth
pub struct MutexGuard {
    #[rr::field("ℓval, iFloor")]
    mutex: Mutex,
    #[rr::field("iAuth")]
    _auth: PhantomData<i64>,
}

impl Mutex {
    #[rr::params("ival" : "Int")]
    #[rr::args("ival")]
    #[rr::returns("(ℓval, ival)" : "(Ref * Int)")]
    pub fn new(data: i64) -> Self {
        let inner = Box::new(data);
        let status = Box::new(AtomicBool::new(false));
        Mutex {
            inner: Box::<i64>::into_raw(inner),
            status: Box::<AtomicBool>::into_raw(status),
            _val: PhantomData
        }
    }

    #[rr::params("ℓval" : "Ref", "iFloor" : "Int")]
    #[rr::args("(ℓval, iFloor)")]
    #[rr::returns("(ℓval, iFloor, iAuth)" : "(Ref * Int * Int)")]
    pub fn lock(self) -> MutexGuard {
        loop {
            match unsafe { (*self.status).compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed) } {
              Ok(_) => return MutexGuard { mutex: self , _auth: PhantomData /* supply self.mutex.inner.get() */ },
              Err(_) => continue
          };
        }
    }
}

impl MutexGuard {
    #[rr::params("ℓval" : "Ref", "iFloor" : "Int", "iAuth" : "Int")]
    #[rr::args("(ℓval, iFloor, iAuth)")]
    #[rr::returns("(ℓval, iFloor + 1, ivalNew + 1)" : "(Ref * Int * Int)")]
    fn incr(&self) {
        unsafe { *&mut *self.mutex.inner += 1; }
    }
}

// Doesn't take into account panics/failures,
// which the ordinary mutex does by setting the flag to
// "poisoned"
impl Drop for MutexGuard {
    #[rr::params("ℓval" : "Ref", "iFloor" : "Int", "iAuth" : "Int")]
    #[rr::args("(ℓval, iFloor, iAuth)")]
    #[rr::requires(#own "ℓval" : "pair(exact(iAuth), iFloor)")]
    #[rr::requires(#type "ℓval" : "pair(exact(iAuth), iFloor)" @ "CounterRA")]
    #[rr::ensures(#own "ℓval" : "pair(exact(iAuth), iFloor)")]
    #[rr::requires(#type "ℓval" : "pair(bot, iFloor)" @ "CounterRA")]
    fn drop(&mut self) {
        unsafe { (*self.mutex.status).store(false, Ordering::Relaxed) };
    }
}

impl Deref for MutexGuard {
    type Target = i64;

    #[rr::params("ℓval" : "Ref", "iFloor" : "Int", "iAuth" : "Int")]
    #[rr::args("(ℓval, iFloor, iAuth)")]
    #[rr::requires(#own "ℓval" : "pair(exact(iAuth), iFloor)")]
    #[rr::requires(#type "ℓval" : "pair(exact(iAuth), iFloor)" @ "CounterRA")]
    #[rr::returns("iAuth")]
    fn deref(&self) -> &Self::Target {
        unsafe { &*self.mutex.inner }
    }
}


#[rr::params("ℓval" : "Ref", "iFloor" : "Int", "iWhen" : "Int")]
#[rr::args("(ℓval, iFloor)", "iWhen")]
#[rr::requires("iWhen <= iFloor")]
#[rr::params("ℓval" : "Ref", "iFloor" : "Int")]
#[rr::args("(ℓval, iFloor)")]
#[rr::returns("v" : "(Ref * Int)")]
#[rr::ensures("v == RustValue.mutex(ℓval, iFloor + 1)")]
fn threadfn(mutex: Mutex, i_when: i64) -> Mutex {
    // ℓmutex.value ↦ RustValue.mutex(ℓval, iFloor) &&
    // isTypedBy(RustValue.mutex(ℓval, iFloor), TypeTag.isMutex()) &&
    // ℓiWhen.value ↦ i_when
    let mut guard_val = i_when - 1;
    // ℓmutex.value ↦ RustValue.mutex(ℓval, iFloor) &&
    // isTypedBy(RustValue.mutex(ℓval, iFloor), TypeTag.isMutex()) &&
    // ℓiWhen.value ↦ iWhen &&
    // ℓguardVal.value ↦ iWhen - 1
    // which is equivalently
    // ℓmutex.value ↦ RustValue.mutex(ℓval, iFloor) &&
    // ℓval.value ↦ (bot, iFloor) &&
    // ℓiWhen.value ↦ iWhen &&
    // ℓguardVal.value ↦ (iWhen - 1)

    // invariant:
    // exists v : Int :: (ℓguardVal.value ↦ v) &&
    //                   ((v >= iWhen) ==> ℓval.value ↦ (bot, iFloor + 1)) &&
    //                   ((v < iWhen) ==> ℓval.value ↦ (bot, iFloor))
    //
    while guard_val < i_when {
        let guard = mutex.lock();
        // ℓval.value ↦ (bot, iFloor) becomes
        // exists v: Int :: ℓval.value ↦ (v, iFloor) and
        guard_val = *guard;
        // ℓguardVal.value ↦ v
        if guard_val < i_when {
            continue;
        }
        // ℓguardVal.value ↦ v && v >= iWhen
        guard.incr();
        // ℓval.value ↦ (v + 1, iFloor + 1)
    }
    mutex
}

struct ThreadData {
    mutex: Mutex,
    i_when: i64
}

impl FnOnce<()> for ThreadData {
    type Output = Mutex;
    extern "rust-call" fn call_once(self, _args: ()) -> Mutex {
        threadfn(self.mutex, self.i_when)
    }
}

fn main() {
    let mutex = Mutex::new(0);
    // ℓmutex.value ↦ RustValue.mutex(ℓval, 0) && typedBy(RustValue.mutex(ℓval, 0), TypeTag.isMutex())
    // can be copied:
    // ℓmutex.value ↦ RustValue.mutex(ℓval, 0) && typedBy(RustValue.mutex(ℓval, 0), TypeTag.isMutex())
    //                                         && typedBy(RustValue.mutex(ℓval, 0), TypeTag.isMutex())
    let thread_data = ThreadData { mutex: mutex, i_when: 0 };
    thread::spawn(thread_data);
    // ℓmutex.value ↦ RustValue.mutex(ℓval, 0) && typedBy(RustValue.mutex(ℓval, 0), TypeTag.isMutex())
    let mut guard_val = 0;
    // ℓmutex.value ↦ RustValue.mutex(ℓval, 0) && typedBy(RustValue.mutex(ℓval, 0), TypeTag.isMutex())
    // ℓguardVal.value ↦ 0
    // loop invariant:
    // exists v: Int :: ℓmutex.value ↦ RustValue.mutex(ℓval, 0) && ℓguardVal.value ↦ v &&
    // ℓval.value ↦ pair(bot, v)
    while guard_val < 1 {
        let guard = mutex.lock();
        // exists v: Int :: ℓguard.value ↦ RustValue.mutexGuard(v, 0)
        guard_val = *guard;
        // ℓguardVal.value ↦ v
    }
    // exists v: Int :: ℓmutex.value ↦ RustValue.mutex(ℓval, 0) && ℓguardVal.value ↦ v &&
    // ℓval.value ↦ pair(bot, v) && v >= 1 by hoare rule
    assert!(1 <= guard_val);
}
// Rather than modeling ownership transfer across threads,
// (which is uninteresting given it is roughly equivalent to "exhale")
// this is a program that, though operating concurrently,
// can easily be shown to refine a sequential one and is therefore correct
// with respect to a sequential counter.
