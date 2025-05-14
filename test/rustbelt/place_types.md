# Purpose
The purpose of this document is to describe the implementation of Refined Rust's place types in Raven,
using an example in which they are neccessary.

# Place Types
Are a mechanism used by Refined Rust to assign types to locations carrying ghost state.

There are two reasons this ghost state may be used in the proof of Rust code:
First, the ghost state can be called for directly by the specification, in the form of the annotation

```rust
#![rr::invariant(#own "freeable ℓ v")]
```

Which means that the location `ℓ` maps to a Rust Value `v`.

Second, the ghost state can be used to store copies of function parameters.

This has the advantage of allowing changes in program state, called for by the source program,
to be verified using procedures that modify the type at the ghost state.

# Rust Code
To explore the first case, where explicit ghost state is used, the following is written:

```rust
#![feature(register_tool)]
#![register_tool(rr)]

#![rr::refined_by("ℓ": "Ref")]
#![rr::refined_by("(ℓ, i)" : "(Ref * Int)")]
#![rr::exists("v": "RustValue")]
#![rr::invariant(#own "ℓ" "v")]
#![rr::invariant(#type "ℓ" : "i" @ "Int")]
struct Mirrored {
  #[rr::field("ℓ")]
  raw: *mut i32,
  #[rr::field("i")]
  mirror: i32
}

#[rr::params("ℓ" : "Loc", "i" : "Int")]
#[rr::args("(ℓ, i)")]
#[rr::returns("(ℓ, i + 10)")]
#[rr::ensures(#iris "Res γ (ℓ, i + 10)")]
fn update_mirrored(mut x: Mirrored) -> Mirrored {
  unsafe {
    *&mut *x.inner.raw = *x.inner.raw + 10;
  }
  let mirror': &mut i32 = &mut x.mirror;
  *mirror' += 10;
  x
}
```

In the above code, the type "Singular" describes structures with a single field "raw", which evaluates to a pointer to a 32 bit integer.

The type "Nested" describes structures with fields "inner" and "mirror", where "inner" evaluates to an instance of "raw" and "mirror" evaluates to an integer.

The invariants added then express the folloiwng constraints:
1. raw stores a value "v" at "ℓ"
2. "ℓ" is mirrored by the field "mirror"'s value, called "i", which is a 32 bit integer.

# Tranlsation To Raven

To translate this to Raven, a new predicate, `placeTypedBy(ℓ: Location, v: RustValue, τ: TypeTag)` is needed,
accompanied by the axiom:

```
own(ℓ, v, τ) && placeTypedBy(ℓ, v, τ) <==> own(ℓ, v, τ) && typedBy(v, fromTypeTag(τ))
```

Where fromTypeTag(τ) changes the fields of τ to all be borrowed.

The translation design is then the following

```
// translate the rust struct “Nested” into an instantiation of
// DataInv, endowing structs that look like { raw: Loc, mirror: Int }
// with the invariant that ℓ owns a value and is placed typed by
// Int at that value.
module Nested : DataInv {
  // ...
  val mapForSD: TypeTag := {| raw: Loc, mirror: Int |};
  val lenForSD: Int := 2;
  // ...
  pred dataInv(x: RustValue, m: ResoulutionMap) {
    ∃ (v: RustValue) ::
    (x.raw ↦ v) && placeTypedBy(x.raw, v, Int) &&
    (x.mirror == deref(mirror.borrowName) ?
     (m[x.mirror] == v) : (x.mirror == v))
  }
}

proc update_nested(ℓ: Loc, i: Int, m: ResolutionMap)
  requires Nested.typedBy({raw: ℓ, mirrored: i}, Int, m)
  ensures Nested.typedBy({raw: ℓ, mirrored: i + 10}, Int, m)
 {
  var ℓ’: Ref := box({| raw: ℓ, mirrored: i |});
  // So now we have
  // (ℓ’.value ↦ {| raw: ℓ, mirrored: i |}) && placeTypedBy(ℓ’, {| raw: ℓ, mirrored: i |} && Nested.dataInv(...)) which means we have
  assert (ℓ’.value ↦ {| raw: ℓ, mirrored: i |}) && Nested.TypedBy(2, isStructuredData(), m)
  yoink(ℓ’);
  // So now we have:
  assert (ℓ’.value ↦ {| raw: ℓ, mirrored: i |}) &&
         Nested.TypedBy(2, {| raw: isBorrowOf(Loc), mirror: isBorrowOf(Int) |}, m) &&
         Nested.dataInv({| raw: ℓ, mirrored: i |}, m); // equivalently
  assert (ℓ’.value ↦ {| raw: ℓ, mirrored: i |}) &&
         Nested.TypedBy(2, {| raw: isBorrowOf(Loc), mirror: isBorrowOf(Int) |}, m) &&
         ℓ’.value.raw.value ↦ i;
  exhale ℓ’.value.raw.value ↦ i;
  inhale ℓ’.value.raw.value ↦ (i + 10);
  var mirror1: RustValue := mirrored.mutably_borrow(ℓ’);
  assert (ℓ’.value ↦ {| raw: ℓ, mirrored: γ |}) &&
         Nested.TypedBy(2, {| raw: isBorrowOf(Loc), mirror: blocked(Int) |}, m) &&
         ℓ’.value.mirrored ↦ (i + 10) &&
         mirror1 := (i, γ);
  resolveProphecy(γ, i + 10);
  mirrored.end_mutable_borrow(ℓ’, mirror1);
  assert (ℓ’.value ↦ {| raw: ℓ, mirrored: γ |}) &&
         Nested.TypedBy(2, {| raw: isBorrowOf(Loc), mirror: isBorrowOf(Int) |}, m) &&
         ℓ’.value.mirrored ↦ (i + 10) &&
         mirror1 := (i, γ) &&
         Res(γ, i + 10);
  unyoink(ℓ’);
  assert (ℓ’.value ↦ {| raw: ℓ, mirrored: γ |}) &&
         Nested.TypedBy(2, isStructuredData, m) &&
         ℓ’.value.mirrored ↦ (i + 10) &&
         mirror1 := (i, γ) &&
         Res(γ, i + 10);
  unbox(ℓ’, {| raw: ℓ, mirrored: i + 10 |});
  fold Nested.typedBy({raw: ℓ, mirrored: i + 10}, isStructuredData, m);
}
```
