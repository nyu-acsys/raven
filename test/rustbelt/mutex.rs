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

use std::ops::Deref;

// look over refined rust to try to find abstract predicates
// replace this with ticket-lock and a simpler thread function

// Extra specs file can look like this:
// include "ticket-lock.rav"
//
// module Resource : LockResource {
//   rep type T;
//   ...
// }
//
// module OptionR = Option[Prod[RefType, Resource]];

#[rr::refined_by("(ℓstatus, value, status)" : "(Ref * OptionR * Bool)")]
#[rr::invariant(#iris "own(value.thing.left, resource, value)")]
#[rr::invariant(#iris "status ? (value == OptionR.some(value.thing)) : true")]
#[rr::invariant(#type "ℓstatus" : "status" @ "Bool")] // invariant of all atomicbool
#[rr::invariant(#iris "value == OptionR.some(value.thing) ? resource(value.thing) : true")]
#[allow(unused)]
pub struct MutexInvariant {
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
#[rr::exists("value" : "OptionR")]
#[rr::exists("status" : "Bool")]
#[rr::shared_invariant(#iris "own(ℓval, resource, value)")]
#[rr::shared_invariant(#iris "status ? (value == OptionR.some(Prod.cons(ℓval, value.thing.right))) : true")]
#[rr::shared_invariant(#type "ℓstatus" : "status" @ "Bool")] // invariant of all atomicbool
#[rr::shared_invariant("value == OptionR.some(value.thing) ? resource(value.thing.right) : true")]
#[derive(Copy, Clone)]
pub struct Mutex {
    #[rr::field("ℓval")]
    inner: *const UnsafeCell<i64>,
    #[rr::field("ℓstatus")]
    status: *const AtomicBool,
}

unsafe impl Send for Mutex {}
unsafe impl Sync for Mutex {}

#[rr::refined_by("ɣhandle" : "Ref")]
#[rr::exists("value" : "Resource.T")]
#[rr::invariant("Res ɣhandle (ℓval, ℓstatus)")]
#[rr::invariant(#iris "own(value.thing.left, resource, value)")]
#[rr::invariant(#iris "value == OptionR.some(value.thing) && resource(value.thing)")]
pub struct MutexGuard<'a> {
    #[rr::field("ɣhandle")]
    inner: &'a Mutex,
}

impl Mutex {
    #[rr::args("data" : "Int")]
    #[rr::params("data")]
    #[rr::returns("(ℓval, ℓstatus)" : "(Ref * Ref)")]
    pub fn new(data: i64) -> Self {
        let boxed_inner = Box::new(UnsafeCell::new(data));
        let boxed_status = Box::new(AtomicBool::new(false));
        let inner = Box::into_raw(boxed_inner);
        // ℓval.value ↦ RustValue.literalInt(data)
        let status = Box::into_raw(boxed_status);
        // ℓstatus.value ↦ RustValue.literalBool(false)
        Mutex { inner, status }
    }

    #[rr::args("ɣself" : "Ref")]
    #[rr::params("ɣself")]
    #[rr::exists("value" : "Resource.T")]
    #[rr::returns("(ɣhandle, ℓinv)" : "(Ref * Ref)")]
    #[rr::atomic_requires("Res ɣself (ℓval, ℓstatus)")]
    #[rr::atomic_ensures("Res ɣhandle (ℓval, ℓstatus)")]
    #[rr::atomic_ensures(#type "ℓinv" : "(ℓstatus, OptionR.some(ℓval, value), true)" @ "MutexInvariant")]
    pub fn lock(&self) -> (MutexGuard, PhantomData<*mut MutexInvariant>) {
        loop {
            // Res ɣself (ℓval, ℓstatus)
            // ℓval.resource ↦ value && ℓstatus.value ↦ false
            let status: &AtomicBool = unsafe { &*(self.status) };
            // Res ɣstatus ℓstatus
            match status.compare_exchange(false, true, Ordering::Acquire, Ordering::Relaxed) {
              Ok(_) => return (MutexGuard { /* ℓstatus.value ↦ false */ inner: self }, PhantomData),
              Err(_) => continue
            }
        }
    }
}

impl<'a> MutexGuard<'a> {
    #[rr::params("(ɣself, ℓinv)" : "(Ref * Ref)")]
    #[rr::exists("value" : "Resource.T")]
    #[rr::atomic_requires("(Res ɣself (ℓval, ℓstatus))")]
    #[rr::atomic_requires(#type "ℓinv" : "(ℓstatus, OptionR.some(ℓval, value.thing.right), true)" @ "MutexInvariant")]
    #[rr::atomic_ensures(#type "ℓinv" : "(ℓstatus, OptionR.some(ℓval, value.thing.right + 1), true)" @ "MutexInvariant")]
    pub fn incr(&self) {
        /* just treat this as atomic */
        unsafe { *(*(self.inner.inner)).get() += 1; }
    }
}

// Doesn't take into account panics/failures,
// which the ordinary mutex does by setting the flag to
// "poisoned"
impl<'a> Drop for MutexGuard<'a> {
    #[rr::params("(ɣself, ℓinv)" : "(Ref * Ref)")]
    #[rr::exists("value" : "LockResource")]
    #[rr::atomic_requires("(Res ɣself (ℓval, ℓstatus))")]
    #[rr::atomic_requires(#type "ℓinv" : "(ℓstatus, value, true)" @ "MutexInvariant")]
    #[rr::atomic_ensures(#type "ℓinv" : "(ℓstatus, OptionR.none, false)" @ "MutexInvariant")]
    fn drop(&mut self) {
        // Res ɣself (ℓval, ℓstatus)
        // ℓval.resource ↦ value && ℓstatus.value ↦ status
        // (by unfolding precondition)
        let status = unsafe { &*self.inner.status };
        // Res ɣself (ℓval.resource, ℓstatus.value)
        status.store(false, Ordering::Relaxed);
        // ℓval.resource ↦ value && ℓstatus.value ↦ status
    }
}

impl<'a> Deref for MutexGuard<'a> {
    type Target = i64;

    #[rr::params("(ɣself, ℓinv)" : "(Ref * Ref)")]
    #[rr::exists("value" : "LockResource")]
    #[rr::args("(ɣself, ℓinv)")]
    #[rr::atomic_requires("(Res ɣself (ℓval, ℓstatus))")]
    #[rr::atomic_requires(#type "ℓinv" : "(ℓstatus, value, true)" @ "MutexInvariant")]
    #[rr::atomic_requires("value == OptionR.some(ℓval, value.thing.right)")]
    #[rr::returns("value" : "Int")]
    fn deref(&self) -> &i64 {
        // Treat as atomic: value.
        unsafe { &*(*self.inner.inner).get() }
    }
}

#[rr::params("ɣMutex" : "Ref", "iWhen" : "Int")]
#[rr::exists("(ℓval, ℓstatus)" : "(Ref * Ref)")]
#[rr::requires("Res ɣMutex (ℓval, ℓstatus)")]
fn threadfn(mutex: &Mutex) {
    // mutex.value ↦ ɣMutex && prophecyResolvesTo(ɣMutex, (ℓval, ℓstatus), m)
    // && isTypedBy((ℓval, ℓstatus), TypeTag.isMutex(), m)
    let (guard, _inv) = mutex.lock();
    // ℓguard.value ↦ (ɣhandle, ℓinv) &&
    // Res ɣself (ℓval, ℓstatus) &&
    // Res ɣhandle (ℓval, ℓstatus) &&
    // ℓinv.value ↦ (ℓstatus, OptionR.some(ℓval, value), true)
    // &&
    // isTypedBy(RustValue.mutexInvariant(ℓstatus, OptionR.some(ℓval, value), true),
    //           TypeTag.isMutex(TypeTag.isInt()), m)
    // unfold then
    guard.incr();
}

// this is ordinarily auto-generated, but made explicit here to
// make the translation easier
impl FnOnce<()> for Mutex {
    type Output = ();
    extern "rust-call" fn call_once(self, _args: ()) {
        threadfn(&self)
    }
}

fn main() {
    let mutex = Mutex::new(0);
    // ℓmutex.value ↦ (ℓval, ℓstatus) &&
    // ℓval.resource ↦ value
    // ℓstatus.value ↦ false
    // && shared invariant clauses
    // copy into param for spawn
    thread::spawn(mutex);
    // ℓmutex.value ↦ (ℓval, ℓstatus) &&
    // ℓval.resource ↦ value
    // ℓstatus.value ↦ false
    // && shared invariant clauses
    // copy again into param for spawn
    thread::spawn(mutex);
}
