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
#![rr::invariant(#own "ℓ" "i")]
#![rr::invariant(#type "ℓ" : "i" @ "Int")]
struct Mirrored {
  #[rr::field("ℓ")]
  raw: *mut i32,
  #[rr::field("i")]
  mirror: i32
}

#[rr::params("ℓ" : "Loc", "i" : "Int")]
#[rr::args("(ℓ, i)" : "Mirrored")]
#[rr::returns("(ℓ, i + 10)")]
#[rr::ensures(#iris "Res γ (ℓ, i + 10)")]
fn update_nested(mut x: Mirrored) -> Mirrored {
  unsafe {
    let rebor: &mut i32 = &mut *x.raw;
    *rebor = *rebor + 10;
  }
  x.mirror += 10;
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

// TODO
// Push the typechecks as much as possible into Raven's typesystem

// have a safe procedure that calls update_nested
// reading out mirror + raw

// Have the actual implementation of verifying the unsafe code w/
// place types

proc update_nested(ℓ: Loc, i: Int, m: ResolutionMap)
  requires argTypedBy(RustValue.mirrored(ℓ, i), TypeTag.isMirrored());
  ensures returnTypedBy(RustValue.mirrored(ℓ, i + 10), TypeTag.isMirrored(), m)
 {
  // Remove maps; replace with types emitted by the translation from Rust to Raven
  var ℓ': Ref;
  unfold argTypedBy(RustValue.mirrored(ℓ, i), TypeTag.isMirrored())[ℓ' := ℓ];
  // These locations are used for the intermediate references:
  // ℓ_intermediate_0: return pointer
  // ℓ_intermediate_2: reborrow of "mirror"
  // ℓ_intermediate_3: the value read from the reborrow
  // ℓ_intermediate_4: result of adding reborrow & 10
  // ℓ_intermediate_5: result of adding mirror & 10
  // ℓ_intermediate_6: mutable pointer to 32 bit integer
  var ℓ_intermediate_0: Ref;
  var ℓ_intermediate_2: Ref;
  var ℓ_intermediate_3: Ref;
  var ℓ_intermediate_4: Ref;
  var ℓ_intermediate_5: Ref;
  var ℓ_intermediate_6: Ref;
  // So now we have
  assert (ℓ’.value ↦ RustValue.mirrored(ℓ, i)) && TypedBy(RustValue.mirrored(ℓ, i), TypeTag.isBorMirrored(), m);
  yoink(ℓ’);
  // So now we have:
  assert (ℓ’.value ↦ RustValue.mirrored(ℓ, i)) &&
         typedBy(RustValue.mirrored(ℓ, i), TypeTag.isYoinkedMirrored(false, false), m) &&
         dataInv(RustValue.mirrored(ℓ, i), m); // equivalently
  unfold dataInv(RustValue.mirrored(ℓ, i), m);
  assert (ℓ’.value ↦ RustValue.mirrored(ℓ, i)) &&
         typedBy(RustValue.mirrored(ℓ, i), TypeTag.isYoinkedMirrored(false, false), m) &&
         ℓ.value ↦ i;
  ℓ_intermediate_6 := Mirrored.raw.deref_copy(ℓ’);
  assert (ℓ_intermediate_6.value ↦ ℓ);
  assert placeTypedBy(ℓ_intermediate_6, TypeTag.isRawPointer(), m);
  ℓ_intermediate_2 := reborrow(ℓ_intermediate_6, TypeTag.isInt());
  unfold reborrowed(ℓ_intermediate_2, ℓ_intermediate_6)[ɣ := ɣ];
  assert (ℓ_intermediate_6.value ↦ ℓ);
  assert (ℓ_intermediate_2.value ↦ (i, ɣ));
  assert (ℓ.value ↦ RustValue.isDeref(ɣ));
  assert placeTypedBy(ℓ_intermediate_2, TypeTag.isMutBorrowOf(TypeTag.isInt()), m);
  ℓ_intermediate_3 := deref_copy(ℓ_intermediate_2);
  assert (ℓ_intermediate_3.value ↦ i);
  assert placeTypedBy(ℓ_intermediate_3, TypeTag.isMutBorrowOf(TypeTag.isInt()), m);
  ℓ_intermediate_4 := add_with_overflow(copy(ℓ_intermediate_3), 10);
  assert (ℓ_intermediate_4.value ↦ (i + 10));
  assert placeTypedBy(ℓ_intermediate_4, TypeTag.isInt(), m);
  deref_move(ℓ_intermediate_2, ℓ_intermediate_4);
  assert (ℓ_intermediate_2.value ↦ (i, ɣ)) && prophecyResolvesTo(ɣ, i + 10, m);
  assert placeTypedBy(ℓ_intermediate_2, TypeTag.isMutBorrow(TypeTag.isInt()), m);
  ℓ_intermediate_5 := add_with_overflow(Mirrored.mirror.copy(ℓ’), 10);
  assert Mirrored.mirror.copy(ℓ’) == i
  assert (ℓ_intermediate_5.value ↦ (i + 10));
  Mirrored.mirror.move(ℓ_intermediate_0, Mirrored.mirror.read(ℓ_intermediate_5))
  assert Mirrored.mirror.copy(ℓ’) == i + 10
  fold dataInv(RustValue.mirrored(ℓ, i + 10), m);
  fold returnTypedBy(RustValue.mirrored(ℓ, i), TypeTag.isMirrored())[ℓ := ℓ_intermediate_0];
}
```

# TODO
- [x] Write a procedure that calls update_nested
- [x] Make the suggestions from the meeting
- [ ] Push typechecks into Raven's type system
- [ ] Actually implement the Raven code
