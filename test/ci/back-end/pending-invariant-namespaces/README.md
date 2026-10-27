# Pending invariant namespace scenarios

These fixtures retain the reproductions used to design frozen namespace contracts.
Their cram tests are disabled until that machinery is implemented. The recorded
diagnostics come from provisional checks and must be reviewed when enabling each test.

- `invariant_alias_mask_collapse` identifies two formal invariant regions with one
  actual invariant.
- `invariant_alias_mask_reentrancy` and `invariant_defined_formal_reentrancy` identify
  a functor parameter's invariant with a captured concrete invariant.
- `invariant_hidden_footprint` hides a concrete invariant behind a wrapper with
  unrelated outer arguments.
- `invariant_required_footprint` exposes a nested dependency only after instantiation.
- `invariant_footprints_*` exercise overlapping implementations and checked views.
- `predicate_hidden_invariant*` exercise predicates carrying invariant dependencies.
  Such dependencies are legitimate; the final contract design must preserve their
  mask requirements rather than reject them unconditionally.

Several reproductions demonstrate invalid proofs accepted without namespace-contract
validation. They are not passing regression coverage for that validation.
