#![feature(register_tool)]
#![register_tool(rr)]
#![feature(unboxed_closures)]
#![feature(fn_traits)]
// inspired by https://whenderson.dev/blog/rust-mutexes/

use std::cell::UnsafeCell;
use std::thread;
use std::sync::atomic::Ordering;
use std::marker::PhantomData;
use std::sync::atomic::AtomicBool;

use std::ops::{Deref};

#[rr::refined_by("(ℓval, ℓstatus)" : "(Ref * Ref)")]
#[rr::exists("value" : "MaybeInit(Int)")]
#[rr::exists("status" : "Bool")]
#[rr::shared_invariant(#type "ℓval" : "value" @ "MaybeInit(Int)")]
#[rr::shared_invariant(#type "ℓstatus" : "status" @ "Bool")]
#[rr::shared_invariant("status" ? "value != uninit() && status != uninit()" : "true")]
#[allow(unused)]
pub struct SharedMutexInvariant {
    #[rr::field("ℓvalue")]
    inner: UnsafeCell<i64>,
    #[rr::field("ℓstatus")]
    status: AtomicBool,
}

// based on the following:
// https://iris-project.org/tutorial-pdfs/lecture12-counter-modules.pdf
#[rr::refined_by("(ℓval, ℓstatus, value, status)" : "(Ref * Ref * Int * Bool)")]
#[rr::invariant(#type "ℓval" : "value" @ "MaybeInit(Int)")]
#[rr::invariant(#type "ℓstatus" : "status" @ "Bool")]
#[rr::invariant("status" ? "value != uninit() && status != uninit()" : "true")]
#[allow(unused)]
pub struct MutexInvariant {
    #[rr::field("ℓvalue")]
    inner: UnsafeCell<i64>,
    #[rr::field("ℓstatus")]
    status: AtomicBool,
    #[rr::field("value")]
    _inner: i64,
    #[rr::field("status")]
    _status: bool,

}

// Raw pointers are used here allowing the memory to leak
// for simplicity purposes.
#[rr::refined_by("(ℓval, ℓstatus)" : "(Ref * Ref)")]
#[rr::exists("value" : "MaybeInit(Int)")]
#[rr::exists("status" : "Bool")]
#[rr::shared_invariant(#type "ℓval" : "value" @ "MaybeInit(Int)")]
#[rr::shared_invariant(#type "ℓstatus" : "status" @ "Bool")]
#[rr::shared_invariant("status" ? "value != uninit() && status != uninit()" : "true")]
#[derive(Clone, Copy)]
pub struct Mutex {
    #[rr::field("ℓval")]
    inner: *const UnsafeCell<i64>,
    #[rr::field("ℓstatus")]
    status: *const AtomicBool,
}

unsafe impl Send for Mutex {}
unsafe impl Sync for Mutex {}

#[rr::refined_by("ɣhandle" : "Ref", "ℓinv" : "Ref")]
pub struct MutexGuard<'a> {
    #[rr::field("ɣhandle")]
    inner: &'a Mutex,
    #[rr::field("ℓinv")]
    inv: PhantomData<*mut MutexInvariant>
}

impl Mutex {
    #[rr::args("data": "Int")]
    #[rr::params("data")]
    #[rr::ensures(#type "ℓinv" : "(ℓval, ℓstatus)" @ "SharedMutexInvariant")]
    #[rr::returns("(ℓval, ℓstatus)" : "(Ref * Ref)", "ℓinv" : "Ref")]
    pub fn new(data: i64) -> (Self, PhantomData<UnsafeCell<SharedMutexInvariant>>) {
        let boxed_inner = Box::new(UnsafeCell::new(data));
        let boxed_status = Box::new(AtomicBool::new(false));
        let inner = Box::into_raw(boxed_inner);
        let status = Box::into_raw(boxed_status);
        (Mutex { inner, status }, PhantomData)
    }

    #[rr::params("ɣself" : "Ref", "ℓinv" : "Ref")]
    #[rr::exists("valueOriginal" : "MaybeInit(Int)")]
    #[rr::exists("statusOriginal" : "Bool")]
    #[rr::exists("value" : "Int")]
    #[rr::returns("(ℓval, ℓstatus)" : "(Ref * Ref)")]
    #[rr::atomic_requires("(Res ɣself (ℓval, ℓstatus))")]
    #[rr::atomic_requires(#type "ℓinv" : "(ℓval, ℓstatus, valueOriginal, statusOriginal)" @ "MutexInvariant")]
    #[rr::atomic_ensures(#type "ℓinv" : "(ℓval, ℓstatus, Some(value), true)" @ "MutexInvariant")]
    pub fn lock(&self, _lock_invariant: PhantomData<UnsafeCell<MutexInvariant>>) -> MutexGuard {
        loop {
            let status: &AtomicBool = unsafe { &*(self.status) };
            match status.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed) {
              Ok(_) => return MutexGuard { inner: self , inv: PhantomData },
              Err(_) => continue
            }
        }
    }
}
impl<'a> MutexGuard<'a> {
    #[rr::params("(ɣself, ℓinv)" : "(Ref * Ref)")]
    #[rr::exists("value" : "Int")]
    #[rr::atomic_requires("(Res ɣself (ℓval, ℓstatus))")]
    #[rr::atomic_requires(#type "ℓinv" : "(ℓval, ℓstatus, Some(value), true)" @ "MutexInvariant")]
    #[rr::atomic_ensures(#type "ℓinv" : "(ℓval, ℓstatus, Some(value + 1), true)" @ "MutexInvariant")]
    pub fn incr(&self) {
        unsafe { *(*(self.inner.inner)).get() += 1; }
    }
}

// Doesn't take into account panics/failures,
// which the ordinary mutex does by setting the flag to
// "poisoned"
impl<'a> Drop for MutexGuard<'a> {
    #[rr::params("(ɣself, ℓinv)" : "(Ref * Ref)")]
    #[rr::exists("value" : "MaybeInit(Int)")]
    #[rr::atomic_requires("(Res ɣself (ℓval, ℓstatus))")]
    #[rr::atomic_requires(#type "ℓinv" : "(ℓval, ℓstatus, value, true)" @ "MutexInvariant")]
    #[rr::atomic_ensures(#type "ℓinv" : "(ℓval, ℓstatus, uninit(), false)" @ "MutexInvariant")]
    fn drop(&mut self) {
        let status = unsafe { &*self.inner.status };
        status.store(false, Ordering::Relaxed);
    }
}

impl<'a> Deref for MutexGuard<'a> {
    type Target = i64;

    #[rr::params("(ɣself, ℓinv)" : "(Ref * Ref)")]
    #[rr::args("(ɣself, ℓinv)")]
    #[rr::atomic_requires("(Res ɣself (ℓval, ℓstatus))")]
    #[rr::atomic_requires(#type "ℓinv" : "(ℓval, ℓstatus, value, true)" @ "MutexInvariant")]
    #[rr::returns("value" : "Int")]
    fn deref(&self) -> &i64 {
        unsafe { &*(*self.inner.inner).get() }
    }
}

#[rr::params("ɣMutex" : "Ref", "iWhen" : "Int", "ℓinv" : "Ref")]
#[rr::exists("(ℓval, ℓstatus)" : "(Ref * Ref)")]
#[rr::requires("Res ɣMutex (ℓval, ℓstatus)")]
#[rr::requires(#type "ℓinv" : "(ℓval, ℓstatus)" @ "SharedMutexInvariant")]
fn threadfn(mutex: Mutex, i_when: i64, _lock_invariant: PhantomData<UnsafeCell<SharedMutexInvariant>>) {
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
        let guard = mutex.lock(PhantomData);
        // ℓval.value ↦ (bot, iFloor) becomes
        // exists v: Int :: ℓval.value ↦ (v, iFloor) and
        guard_val = *guard;
        // ℓguardVal.value ↦ v
        if guard_val >= i_when {
          // ℓguardVal.value ↦ v && v >= iWhen
          guard.incr();
          // ℓval.value ↦ (v + 1, iFloor + 1)
        }
    }
}

// this is ordinarily auto-generated, but made explicit here to
// make the translation easier
struct ThreadData {
    mutex: Mutex,
    i_when: i64,
    lock_invariant: PhantomData<UnsafeCell<SharedMutexInvariant>>
}

// this is ordinarily auto-generated, but made explicit here to
// make the translation easier
impl FnOnce<()> for ThreadData {
    type Output = ();
    extern "rust-call" fn call_once(self, _args: ()) {
        threadfn(self.mutex, self.i_when, self.lock_invariant)
    }
}

fn main() {
    let (mutex, lock_invariant) = Mutex::new(0);
    let thread_data = ThreadData { mutex: mutex, i_when: 0, lock_invariant };
    thread::spawn(thread_data);
    let mut guard_val = 0;
    while guard_val < 1 {
        let guard = mutex.lock(PhantomData);
        guard_val = *guard;
    }
    assert!(1 <= guard_val);
}
