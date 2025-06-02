#![feature(register_tool)]
#![register_tool(rr)]
// inspired by https://whenderson.dev/blog/rust-mutexes/

use std::thread;
use std::sync::atomic::Ordering;
use std::marker::PhantomData;
use std::sync::atomic::AtomicBool;

use std::cell::UnsafeCell;
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
#[rr::invariant(#type "ℓstatus" : "pair(bot, iFloor)" @ "CounterRA")]
pub struct Mutex {
    #[rr::field("ℓval")]
    inner: UnsafeCell<i64>,
    #[rr::field("ℓstatus")]
    status: AtomicBool,
    #[rr::field("iFloor")]
    _val: PhantomData<i64>
}

unsafe impl Send for Mutex {}
unsafe impl Sync for Mutex {}

#[rr::refined_by("(ℓval, iFloor, iAuth)" : "(Ref * Int * Int)")]
#[rr::exists("iAuth" : "Int")]
#[rr::invariant(#own "ℓval" : "pair(exact(iAuth), iFloor)")]
#[rr::invariant(#type "ℓval" : "pair(exact(iAuth), iFloor)" @ "CounterRA")] // implying iFloor <= iAuth
pub struct MutexGuard<'a> {
    #[rr::field("ℓval, iFloor")]
    mutex: &'a Mutex,
    #[rr::field("iAuth")]
    _auth: PhantomData<i64>,
}

impl Mutex {
    #[rr::params("ival" : "Int")]
    #[rr::args("ival")]
    #[rr::returns("(ℓval, iFloor)" : "(Ref * Int)")]
    pub fn new(data: i64) -> Self {
        Mutex {
            inner: UnsafeCell::new(data),
            status: AtomicBool::new(false),
            _val: PhantomData
        }
    }

    #[rr::args("ɣGuard" : "Ref")]
    #[rr::exists("ℓval" : "Ref", "iFloor" : "Int")]
    #[rr::requires("Res ɣGuard (ℓval, iFloor)")]
    #[rr::returns("(ℓval, iFloor, iAuth)" : "(Ref * Int * Int)")]
    #[rr::invariant(#own "ℓval" : "pair(bot, iFloor)")]
    #[rr::invariant(#type "ℓval" : "pair(bot, iFloor)" @ "CounterRA")]
    pub fn lock<'a>(&'a self) -> MutexGuard<'a> {
        loop {
          match self.status.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed) {
              Ok(_) => return MutexGuard { mutex: self , _auth: PhantomData /* supply self.mutex.inner.get() */ },
              Err(_) => continue
          };
        }
    }
}

impl<'a> MutexGuard<'a> {
    #[rr::params("ℓval" : "Ref", "iFloor" : "Int", "iAuth" : "Int")]
    #[rr::args("(ℓval, iFloor, iAuth)")]
    #[rr::returns("(ℓval, iFloor + 1, ivalNew + 1)" : "(Ref * Int * Int)")]
    fn incr(&self) {
        unsafe { *&mut *self.mutex.inner.get() += 1; }
    }
}

// Doesn't take into account panics/failures,
// which the ordinary mutex does by setting the flag to
// "poisoned"
impl<'a> Drop for MutexGuard<'a> {
    #[rr::params("ℓval" : "Ref", "iFloor" : "Int", "iAuth" : "Int")]
    #[rr::args("(ℓval, iFloor, iAuth)")]
    #[rr::requires(#own "ℓval" : "pair(exact(iAuth), iFloor)")]
    #[rr::requires(#type "ℓval" : "pair(exact(iAuth), iFloor)" @ "CounterRA")]
    #[rr::ensures(#own "ℓval" : "pair(exact(iAuth), iFloor)")]
    #[rr::requires(#type "ℓval" : "pair(bot, iFloor)" @ "CounterRA")]
    fn drop(&mut self) {
        self.mutex.status.store(false, Ordering::Relaxed);
    }
}

impl<'a> Deref for MutexGuard<'a> {
    type Target = i64;

    #[rr::params("ℓval" : "Ref", "iFloor" : "Int", "iAuth" : "Int")]
    #[rr::args("(ℓval, iFloor, iAuth)")]
    #[rr::requires(#own "ℓval" : "pair(exact(iAuth), iFloor)")]
    #[rr::requires(#type "ℓval" : "pair(exact(iAuth), iFloor)" @ "CounterRA")]
    #[rr::returns("iAuth")]
    fn deref(&self) -> &Self::Target {
        unsafe { &**&self.mutex.inner.get() }
    }
}


#[rr::params("ɣMutexRef" : "Ref", "iWhen" : "Int")]
#[rr::requires("iWhen <= iFloor")]
#[rr::exists("ℓval" : "Ref", "iFloor" : "Int")]
#[rr::requires("Res ɣMutexRef (ℓval, iFloor)")]
#[rr::requires(#own "ℓval" : "pair(bot, iFloor)")]
#[rr::requires(#type "ℓval" : "pair(bot, iFloor)" @ "CounterRA")]
#[rr::ensures(#own "ℓval" : "pair(bot, iFloor + 1)")]
#[rr::ensures(#type "ℓval" : "pair(bot, iFloor + 1)" @ "CounterRA")]
fn threadfn(mutex_ref: &Mutex, iWhen: i64) {
    loop {
        let guard = mutex_ref.lock();
        if iWhen <= *guard {
            guard.incr();
            break;
        }
    }
}

fn main() {
    let mutex = Mutex::new(0);
    let mutex_ref = &mutex;
    // mutex_ref ↦ (ℓval, 0) * ℓval ↦ (bot, 0)
    // duplicable: mutex_ref ↦ (ℓval, 0) * ℓval ↦ (bot, 0) * ℓval ↦ (bot, 0)
    thread::scope(move |s| {
        s.spawn(move ||
                threadfn(mutex_ref, 0));
        // mutex_ref ↦ (ℓval, 0) * ℓval ↦ (bot, 0)
    });
    loop {
        // mutex_ref ↦ (ℓval, 0) * ℓval ↦ (bot, 0)
        let guard = mutex_ref.lock();
        // mutex_ref ↦ (ℓval, 0) * ℓval ↦ (exact(m), 0)
        if 1 <= *guard {
            break;
        }
        // we have 1 <= m so it is safe to update the state
        // mutex_ref ↦ (ℓval, 0) * ℓval ↦ (exact(m), 1)
        unsafe { assert!(1 <= *guard); }
        // assertion should pass now.
    }
}
