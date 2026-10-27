# Pending invariant namespace scenarios

These end-to-end fixtures are disabled until namespace-contract analysis becomes
the default verifier pipeline. Their expectations describe that pipeline, rather
than the legacy default. Active unit tests cover inference and realization.

The failure cases exercise alias collapse, reentrancy, hidden dependencies and
required footprints. The successful cases exercise unused sharing and predicates
that contain invariants. Sharing alone is valid; obligations arise when a proof
relies on separation.

Activation also requires a precise model of permission grants for opaque predicates
returned by calls or exposed by fresh invariant construction. Dependency upper
bounds must not be expanded into granted permissions.
