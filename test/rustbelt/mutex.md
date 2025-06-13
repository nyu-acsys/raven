# Purpose
The purpose of this document is to show how concurrent rust code can be verified using
a type system analagous to that of Refined Rust's and using Raven as a backend.

# Code
The file `mutex.rs` contains the implementation of a concurrent primitive, namely a mutex, and
uses it to encode a concurrent counter.

The mutex code is a simplified version of the code contained in the blog `https://whenderson.dev/blog/rust-mutexes/`, which is itself based on the mutex code in `https://doc.rust-lang.org/stable/src/std/sys/sync/mutex/futex.rs.html`. To implement the mutex without reference to a thread scheduler, the mutex has a permission bit; the mutex is locked when it is set to true, unlocked when it is set to false, and a thread can ensure exclusive ownership by performing a CAS loop on the permission bit.

The concurrent counter is shared with another thread, allowing the main thread to block until the concurrent
code finishes.

# Mutex Specification (Informal)
The specification of the mutex is *assumed* to be correct and left unproven, given that mutexes are concurrency primitives.


The specification of the mutex essentially works as follows:

1. In the unlocked state, referred to in the rust code as `Mutex`, the field `inner` is associated with
   a location `ℓval`, which concretely points to a 64 bit integer, and in ghost code points to ghost state.
2. Ghost state for the "concurrent counter" RA (https://iris-project.org/tutorial-pdfs/lecture12-counter-modules.pdf) is manually added in order to prove facts about lower bounds of the mutex value.
   The ghost state is specified using pairs `({bot, excl(n ∈ Int), top}, m ∈ Int)`, where the left hand side
   represents the _actual_ value, only visible when the lock is locked,
   and the right hand side refers to _a single_ lower bound of the actual value, visible to all threads.
3. From a shared borrow of the Mutex, represented as a prophecy variable that resolves to
   `(bot, m ∈ Nat)`, one can retrieve _some_ locked mutex, referred to in the rust code as `MutexGuard`,
    that allows you to access the inner value, represented as `exists n ∈ Int, (n ∈ Int, m ∈ Int) && m <= n`
4. When the mutex is deallocated, it is considered unlocked, and this is represented as
   `exists n ∈ Int, (n ∈ Int, m ∈ Int) && m <= n`.

# Threaded Procedures Specification (Informal)
The specification of the procedures, on the other hand, is not assumed to be correct, but is checked step-by-step.

```rust
fn main() {
    let mutex = Mutex::new(0);
    let mutex_ref = &mutex;
    // mutex_ref ↦ (ℓval, 0) && ℓval ↦ (bot, 0) && typedBy(mutex_ref, x, )
    // duplicable: mutex_ref ↦ (ℓval, 0) && ℓval ↦ (bot, 0) * ℓval ↦ (bot, 0)
    thread::scope(move |s| {
        s.spawn(move ||
                threadfn(mutex_ref, 0));
        // mutex_ref ↦ (ℓval, 0) && ℓval ↦ (bot, 0)
    });
    loop {
        // mutex_ref ↦ (ℓval, 0) && ℓval ↦ (bot, 0)
        let guard = mutex_ref.lock();
        // mutex_ref ↦ (ℓval, 0) && ℓval ↦ (exact(m), 0)
        if 1 <= *guard {
            break;
        }
        // we have 1 <= m so it is safe to update the state
        // mutex_ref ↦ (ℓval, 0) && ℓval ↦ (exact(m), 1)
        unsafe { assert!(1 <= *guard); }
        // assertion should pass now.
    }
}
```

In the above specification, a "Mutex" is first allocated, resulting in the ghost state of
`// mutex_ref ↦ (ℓval, 0) && ℓval.value ↦ (bot, 0)`

you can then duplicate the resource, which is logically equivalent:
`// mutex_ref ↦ (ℓval, 0) && ℓval ↦ (bot, 0) && ℓval ↦ (bot, 0)`

consume it by spawning a thread:
```
thread::scope(move |s| {
    s.spawn(move ||
            threadfn(mutex_ref, 0));
    // mutex_ref ↦ (ℓval, 0) && ℓval ↦ (bot, 0)
});
```

and locking the guard:
```
        // mutex_ref ↦ (ℓval, 0) && ℓval ↦ (bot, 0)
        let guard = mutex_ref.lock();
        // mutex_ref ↦ (ℓval, 0) && ℓval ↦ (exact(m), 0)
```

You can then use the properties of the resource algebra to show that the value is lower bounded:
```
        if 1 <= *guard {
            break;
        }
        // we have 1 <= m so it is safe to update the state
        // mutex_ref ↦ (ℓval, 0) && ℓval ↦ (exact(m), 1)
```

And therefore show that the assertion passes:
```
        unsafe { assert!(1 <= *guard); }
        // assertion should pass now.
```
And so the execution is the same as the linear execution (TODO).

# Mutex Specification

To make the mutex spec. work in raven, we need to first define the resource algebra:

```
module CounterRA : ResourceAlgebra {
  type CompletedNat = data {
    case bot();
    case exact(n: Int);
    case top();
  }

  type T = data {
    case pair(left: CompletedNat, right: Nat)
  }

  func valid(x: T) {
    (x.left == CompletedNat.exact(x.left.n) && (x.right <= x.left.n)) || (x.left == bot)
  }

  func comp(x: T, y: T) {
    (x.left == CompletedNat.bot) ? pair(y.left, max(x.right, y.right)) :
    (y.left == CompletedNat.bot) ? pair(x.left, max(x.right, y.right)) :
    top
  }

  func fpuAllowed(a: T, b: T) {
    exists x : Nat ::
    a.left == CompletedNat.exact(a.left.n) && (b.left == CompletedNat.exact(a.left.n + x)) &&
                                              (b.right == CompletedNat.exact(b.left.n + x))
  }
}
```

We can then define the possible values,

```
module RustValue: Library.Type {
  rep type T = data {
    case literalInt(v: Int);
    case literalBool(b: Int);
    case mutBorrow1(initialValueForMut: T, finalBorrowNameForMut1: Ref);
    case mutBorrow2(initialRefForMut: Ref, finalBorrowNameForMut2: Ref);
    case immutBorrow1(borrowNameForImmut: Ref);
    case immutBorrow2(valueForImmut: T);
    case rawPointer(referenceToPointed: Ref);
    case array(lenForArray: Int, mapForArray: Map[Int, T]);
    case uninit();
    case isDeref(borrowNameForDeref: Ref);
    case mutex(lVal: Ref, iFloor: Int);
    // mutex yoinked 1-4, allowing each of the components to be made
    // borrows
    case mutexGuard(lVal: Ref, iFloor: Int, iAuth: Int);
    // mutex guard yoinked 1-8, allowing each of the components to be made
    // borrows
  }
}
```

as well as the types that describe them:

```
module TypeTag {
  rep type T = data {
    case isInt();
    // fix int later with some size
    case isBool();
    case isMutBorrow(mutPointedType: T);
    case isSharedBorrow(sharedPointedType: T);
    case isRawPointer();
    case isArrayOf(collectedType: T);
    case isUninit();
    case isMaybeInit(potentiallyInitializedType: T);
    isMutex();
    isMutexGuard();
    case isMutexYoinked(lValBlocked1: Bool, iFloorBlocked1: Bool);
    case isMutexGuard(lVal: Ref, iFloor: Int, iAuth: Int);
    case isMutexGuardYoinked(lValBlocked2: Bool, iFloorBlocked2: Bool, iAuthBlocked: Bool)
  }
}

pred typedBy(t: RustValue, tag: TypeTag, m: ResolutionMap) {
  exists pointed: RustValue ::
  derefsTo(t, pointed, m) &&
  ...
  ((tag == TypeTag.isMutex()) ==>
    isMutexIsTypedBy(pointed, tag, m))
  &&
  ((tag == TypeTag.isMutexGuard()) ==>
    isMutexGuardIsTypedBy(pointed, tag, m))
  &&
  ((tag == TypeTag.isMutexYoinked(tag.TypeTag.lValBlocked1, tag.TypeTag.iFloorBlocked1)) ==>
    isMutexYoinkedIsTypedBy(pointed, tag, m))
  &&
  ((tag == TypeTag.isMutexGuardYoinked(tag.TypeTag.lValBlocked2, tag.TypeTag.iFloorBlocked2, tag.TypeTag.iAuthBlocked)) ==>
    isMutexGuardYoinkedIsTypedBy(pointed, tag, m))
}

pred isMutexIsTypedBy(t: RustValue, tag: TypeTag, m: ResolutionMap) {
  (t == RustValue.mutex(t.RustValue.lVal, t.RustValue.iFloor)) &&
  t.RustValue.lVal.value ↦ t.RustValue.iFloor
}

pred isMutexGuardIsTypedBy(t: RustValue, tag: TypeTag, m: ResolutionMap) {
  (t == RustValue.mutex(t.RustValue.lVal, t.RustValue.iFloor)) &&
  t.RustValue.lVal.value ↦ t.RustValue.iFloor
}
```

And then axiomatize the procedures:
```
axiom newMutex(iVal: Int, m: ResolutionMap)
  returns (v: RustValue)
  ensures (exists lVal: Ref :: (v == RustValue.mutex(lVal, iVal)) &&
                               typedBy(RustValue.mutex(lVal, iVal), TypeTag.isMutex(), m))

axiom lockMutex(ɣGuard: Ref, implicit ghost ℓval: Ref, m: ResolutionMap,
                implicit ghost iFloor: Int, implicit ghost iAuth: Int)
  returns (v: RustValue)
  requires (prophecyResolvesTo(ɣGuard RustValue.mutex(ℓval, iFloor)))
  ensures (v == RustValue.mutexGuard(lVal, iFloor, iAuth)) && isTypedBy(RustValue.mutexGuard(lVal, iFloor, iAuth), TypeTag.isMutexGuard(), m)
  ensures (exists lVal: Ref :: (v == RustValue.mutex(lVal, iVal)) &&
                               typedBy(RustValue.mutex(lVal, iVal), TypeTag.isMutex(), m))

axiom incr(ℓval: Ref, iFloor: Int, iAuth: Int, m: ResolutionMap)
  returns (v: RustValue)
  requires typedBy(RustValue.isMutexGuard(ℓval, iFloor, iAuth), TypeTag.isMutexGuard(), m)
  ensures (v == RustValue.isMutexGuard(ℓval, iFloor + 1, iAuth + 1))

axiom drop(ℓval: Ref, iFloor: Int, iAuth: Int, m: ResolutionMap)
  returns (v: RustValue)
  requires typedBy(RustValue.isMutexGuard(ℓval, iFloor, iAuth), TypeTag.isMutexGuard(), m)
  ensures (v == RustValue.isMutexGuard(ℓval, iFloor + 1, iAuth + 1))

axiom deref(ℓval: Ref, iFloor: Int, m: ResolutionMap)
  returns (iAuth: Int)
  requires typedBy(RustValue.isMutexGuard(ℓval, iFloor, iAuth), TypeTag.isMutexGuard(), m)
```

# Threaded Procedure & Main FN Specification (Raven)
Then the `threadfn` and `main` function can be spec'd.

layout of thread fn:
```
bb0;
bb1;
bb2;
while guard_val < i_when {
  bb3;
  bb4;
  bb5;
  if guard_val >=  i_when {
    bb6;
    bb7;
  } else {
    bb7;
  }
}
```

layout of main fn:
```
bb0;
bb1;
bb2;
bb3;
while (x < 1) {
  bb5;
  bb6;
  bb7;
}
bb8;
bb10;
bb12;
```
