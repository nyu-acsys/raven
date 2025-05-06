# Purpose
This document describes the translation of this example from annotated Rust to Raven.

# Terminology
This document re-uses the terminology of the Refined Rust paper, adopting without modification
the annotation system of Refined Rust.

It also invents a new terminology for the Raven development:

The Rust in Raven system is called Pierre,
`Place Types and Invariants Extracted from Rust to RavEn` after Pierre Bonnard, the impressionist painter.

# Original Example
In the original example, the authors of Refined Rust (2024) use their toolchain to
verify the following specification:

```rust
#![feature(register_tool)] // Allow annotations with the prefix: rr
#![register_tool(rr)]      //

#[rr::refined_by("(b, c)" : "(loc * Z)")]              // Instances of this struct are represented
                                                       // by the tuple (b : Location, c: Int)
#[rr::invariant("{size_of T} * c  <= max_int isize")]  // c * sizeof(T) is less than the maximum allocated size
#[rr::invariant(#own "freeable b (c * {size_of T})")]  // exists (ys : list (option T)), (b ↦* ys) /\ (length ys == c)
struct RawVec<T> {
    #[rr::field("b")] ptr: *mut T, // links RawVec.ptr to b
    #[rr::field("c")] cap: usize   // links RawVec.cap to c
}

// Instances of this struct are represented by lists of borrows of T
#[rr::refined_by("xs" : "list (bor {math_type T})")]
// The struct has the invariant:
// exists c: Z, b: loc, els: list (bor(option(bor T))),
// (b: els @ Vector.t (Option T) c) /\
// forall i: Int, 0 <= i < (length xs) -> (els !!! i == Some (xs !!! i)) /\
//                (length xs) <= i < c -> (els !!! i == None)
// Or, read in english:
// If you have an instance of Vec<T>, it can be represented by a list of borrows
// of T, called `xs`, for which the following predicate holds:
// there exists some length `c`, some location `b`, and some list of borrows `els` of
// potentially initialized borrows of T, for which the following holds:
//
// `b`, the location, is place typed by `els`, which is a vector of length `c`,
// and the first (length xs) elements of `els` are initialized to some value,
// and the rest are uninitialized.
#[rr::exists("c" : "Z", "b" : "loc", "els" : "list (bor (option (bor {math_type T})))")]
#[rr::invariant(#type "b" : "els" @ "array_t (maybe_init {T}) c")]
#[rr::invariant("∀ i, 0 <= i < length xs --> els !!! i = #(Some (xs !!! i))")]
#[rr::invariant("∀ i, length xs <= i < c --> els !!! i = #None")]
#[rr::invariant("len xs <= c")]
struct Vec<T> {
    #[rr::field("(b, c)")] buf: RawVec<T>, // associate Vec.buf with (b, c)
                                          // and ensure the invariant of RawVec holds for it.
    #[rr::field("(length xs)") len: usize] len: usize // associate len with (length xs)
}

// The spec of the following function says:
// take a mutable borrow of a vector, represented as a pair (xs, γ), where
// xs is the list of borrows of T for which the vector invariant holds,
// and γ is a prophecy variable representing the final value of the list.
// Return a mutable borrow of i'th index of the vector, represented as the pair
// (xs !!! i, γi), and resolve γ to xs[i := *γi], ensuring that the final
// value of the list is equivalent to the original value for every index
// except i, for which it is equivalent to the prophesized value γi.
#[rr::params("xs" : "list (bor {math_type T})", "γ" : "gname", "i" : "Z")]
#[rr::args("(#xs, γ)", "i")]
#[rr::requires("i < length xs")]
#[rr::exists("γi")]
#[rr::returns("(xs !!! i, γi)")]
#[rr::ensures(#iris "Res γ (<[i := *γi]>xs)")]
unsafe fn Vec::get_unchecked_mut<'a>(&'a mut self, idx: usize) -> &'a mut T {
    unsafe {
        let p = self.buf.ptr().add(idx);
        let ret = &'b mut *p;
        ret
    }
}
```

# Updated Example
To translate this example into the restricted format that is currently in Raven, this code is edited to the following:

```rust
#![feature(register_tool)] // Allow annotations with the prefix: rr
#![register_tool(rr)]      //

#[rr::refined_by("γ" : "gname", "cap" : "Z", "len" : "Z")]
#[rr::exists("map": "Int -> option (bor T)")]
#[rr::invariant("γ" : "bor (array (option T))")]
#[rr::invariant("∀ i, 0 <= i < len ==> map !!! i : bor T")]
#[rr::invariant("∀ i, len <= i < cap ==> map !!! i : uninit")]
#[rr::invariant("0 <= len <= cap")]
struct Vec<T> {
    #[rr::field("γ")] buf: *mut T,
    #[rr::field("cap")] cap: usize,
    #[rr::field("len")] len: usize
}

#[rr::params("xs" : "list (bor {math_type T})", "γ" : "gname",  "γi" : "gname", "i" : "Z")]
#[rr::args("(#xs, γ)", "i")]
#[rr::requires("i < length xs")]
#[rr::exists("γi")]
#[rr::returns("(xs !!! i, γi)")]
#[rr::ensures(#iris "Res γ (<[i := *γi]>xs)")]
unsafe fn Vec::borrow_ith(&mut self, idx: usize) -> &mut T {
    unsafe {
        let p = self.buf.ptr().add(idx);
        ptr = &mut *p;
    }
}
```

Allowing the translation process to dodge, for now, the issue of lifetimes, because it simply manually
ensures that `ɣi`, the eventual value of the index, is resolved after `ɣ`, the eventual value of the vector.

The translation process will also dodge, for now, the issue of invariants that arise from nested structures; this can be dealt with later by more sophisticated code.

# Updated Example translated to Raven
First, the type `Vec<T>` is translated to the following Raven type:
```Raven
interface VecI: DataInvariant {
  // ...
  val tag: TypeTag;
  // ...
}
```

Where `DataInvariant` is a Raven module allowing one to describe annotated Rust structures by supplying a `lenForSD`, or number of fields of the structure, and a `mapForSD` or a map from field index to type, as well as an invariant for structures with `lenForSD` fields that satisfy the `mapForSD` types at each index.

The `lenForSD` and `mapForSD` are then supplied:

```Raven
  val lenForSD: Int = 3;
  val mapForSD: Map[Int, TypeTag] = {| i: Int :: (i == 0) ? TypeTag.isInt(): ((i == 1) ? TypeTag.isInt(): TypeTag.isArrayOf(TypeTag.isMaybeInit(tag))) |};
```

describing a 3-tuple of two integers and a partially initialized array of a user supplied type "tag".

The 3-tuple is then associated with an invariant:

```Raven
pred dataInv(rustValue: RustValue, m: ResolutionMap) {
  exists structure: RustValue, cap: Int, len: Int, map: Map[Int, RustValue] ::
  isStructure(rustValue, structure, m)
  &&
  isCapField(structure, cap, m)
  &&
  isLenField(structure, len, m)
  &&
  (len <= cap)
  &&
  isBufField(structure, cap, map, m)
  &&
  typedBy(RustValue.array(cap, map), TypeTag.isArrayOf(TypeTag.isMaybeInit(tag)), m)
  &&
  initializedForLen(len, cap, map, m)
}
```

Which is a translation of the "updated invariant",

```
#[rr::refined_by("γ" : "gname", "cap" : "Z", "len" : "Z")]
#[rr::exists("map": "Int -> option (bor T)")]
#[rr::invariant("γ" : "bor (array (option T))")]
#[rr::invariant("∀ i, 0 <= i < len ==> map !!! i : bor T")]
#[rr::invariant("∀ i, len <= i < cap ==> map !!! i : uninit")]
#[rr::invariant("0 <= len <= cap")]
```

Corresponding thusly:

1. First, `γ` is left out. This is because we simply do not borrow the structure in our example
2. Second, values of the structure are named explicitly by `rustValue`, and are assumed to be nested
   dereferences; these nested dereferences are assumed to dereference to a final value, `structure`.
   The projections of this `structure`, namely `cap`, `len`, and `map`, are then made explicit.

   This differs from the original invariant in that some amount of indirection is built-in to the invariant.
   This is because in RefinedRust, there are place types, allowing the user to manipulate the types at
   locations; for Pierre, at this point, the distinction has not yet been made, and so a value may be buried
   behind a nested locations or prophecies.

Then, the function "getUncheckedMut" of the updated example:

```rust
#[rr::params("xs" : "list (bor {math_type T})", "γ" : "gname",  "γi" : "gname", "i" : "Z")]
#[rr::args("(#xs, γ)", "i")]
#[rr::requires("i < length xs")]
#[rr::exists("γi")]
#[rr::returns("(xs !!! i, γi)")]
#[rr::ensures(#iris "Res γ (<[i := *γi]>xs)")]
unsafe fn Vec::borrow_ith(&mut self, idx: usize) -> &mut T {
    unsafe {
        let p = self.buf.ptr().add(idx);
        ptr = &mut *p;
    }
}
```

is translated via the following three step process:

First, the pre and post-conditions are translated to predicates, allowing variables to be assigned to the fields:

```Raven
  pred getUncheckedMutPre(xs: RustValue, gamma: Ref, idx: Int, gammaI: Ref, len: Int, m: ResolutionMap) {
    exists structure: RustValue,
    cap: Int, map: Map[Int, RustValue] :: typedBy(RustValue.mutBorrow1(xs, gamma), TypeTag.isMutBorrow(TypeTag.isStructuredData()), m)
    &&
    isStructure(xs, structure, m)
    &&
    isLenField(structure, len, m)
    &&
    isBufField(structure, cap, map, m)
    &&
    (0 <= idx < len)
    &&
    isProphecy(gamma)
    &&
    isProphecy(gammaI)
  }

  pred getUncheckedMutPost(xs: RustValue, gamma: Ref, idx: Int, len: Int, m: ResolutionMap, xi: RustValue, gammaI: Ref) {
    exists structure: RustValue, cap: Int, map: Map[Int, RustValue] ::
    isStructure(xs, structure, m)
    &&
    isBufField(structure, cap, map, m)
    &&
    resolvedProphecy(gamma, RustValue.array(cap, (map[idx := RustValue.isDeref(gammaI)])), m)
    &&
    (map[idx] == xi)
    &&
    isProphecy(gammaI)
  }
```

Then, the type of the function is translated, associating each mutable borrow `&mut` with a prophecy variable which fortells the final value of each of the mutable borrows:

```
  proc getUncheckedMut(xs: RustValue, gamma: Ref, idx: Int, len: Int, m: ResolutionMap)
    returns (xi: RustValue, gammaI: Ref)
```

Finally, the body of the function is translated, unfolding the type, accessing the invariant (to ensure that the index "idx" is allocated), and updating the vector's value to resolve to the final value of the index:

```
  proc getUncheckedMut(xs: RustValue, gamma: Ref, idx: Int, len: Int, m: ResolutionMap)
    returns (xi: RustValue, gammaI: Ref)
    requires getUncheckedMutPre(xs, gamma, idx, gammaI, len, m)
    ensures getUncheckedMutPost(xs, gamma, idx, len, m, xi, gammaI)
     {
    // Unfold the precondition:
    var structure: RustValue;
    var cap: Int;
    var map: Map[Int, RustValue];
    unfold getUncheckedMutPre(xs, gamma, idx, gammaI, len, m)[structure := structure, cap:= cap, map := map];
    // Unfold the typedBy predicate, following dereferences:
    var pointed1: RustValue;
    unfold typedBy(RustValue.mutBorrow1(xs, gamma),TypeTag.isMutBorrow(TypeTag.isStructuredData()),m)[pointed1 := pointed];
    assert pointed1 == RustValue.mutBorrow1(xs, gamma);
    // Yoink the invariant from the data
    unfold mutBorrow1IsTypedBy(RustValue.mutBorrow1(xs, gamma), TypeTag.isMutBorrow(TypeTag.isStructuredData()), m);
    var pointed: RustValue;
    unfold typedBy(xs, TypeTag.isStructuredData(), m)[pointed := pointed];
    unfold isStructuredDataIsTypedBy(pointed, m);
    dataInvFromDerefsTo(xs, pointed, m);
    fold isYoinkedIsTypedBy(pointed, m);
    fold typedBy(xs, TypeTag.isYoinked(), m)[pointed := pointed];
    // Unfold the invariant
    var cap2: Int;
    var len1: Int;
    var borrowName: Ref;
    var map2: Map[Int, RustValue];
    var structure1: RustValue;
    unfold dataInv(xs, m)[cap2 := cap, len1:= len, map2:= map, structure1 := structure];
    // The field is accessed by both the precondition and the invariant;
    // assert that they are equal
    isStructureSurj(xs, structure, structure1, m);
    assert (structure == structure1);
    assert isBufField(structure, cap, map, m);
    assert isBufField(structure1, cap2, map2, m);
    isBufFieldSurj(structure, cap, map, cap2, map2, m);
    isLenFieldSurj(structure, len, len1, m);
    // Resolve the prophecy variable
    resolveProphecy(gamma, RustValue.array(cap, map[idx := RustValue.isDeref(gammaI)]), m);
    // Fold the postcondition
    assert isStructure(xs, structure, m);
    assert isBufField(structure, cap, map, m);
    assert isProphecy(gammaI);
    assert resolvedProphecy(gamma, RustValue.array(cap, (map[idx := RustValue.isDeref(gammaI)])), m);
    xi := map[idx];
    fold getUncheckedMutPost(xs, gamma, idx, len, m, xi, gammaI)[structure := structure, cap:= cap, map := map];
    // Because we have no place types yet, the type is only asserted
    // over the pure rust value "xs";
    // no need to reestablish the type at a location.
    // So we are done.
  }
```
