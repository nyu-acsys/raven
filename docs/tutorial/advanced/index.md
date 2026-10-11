# 5. Scaling Up

This chapter brings the preceding ideas together in four capstones.

The guiding idea of this chapter is that the toolkit doesn't change, only how convenient it is to
use. This is also the one part of the tutorial that is designed so you can start reading here
directly. A reader who already knows separation logic/Iris (or who's willing to take the core
assertions from Parts 1–4 on faith) should be able to begin with this part. This is a deliberate
tradeoff against the idea, stated in the [introduction](../index.md), of one example growing
across the whole tutorial. We resolve it by referring back to *specific* earlier subsections
rather than re-teaching them. Each section opens with a one-line "Assumes" pointer naming exactly
what's carried over from earlier parts.

- **[5.1. Resource Algebras in Practice](./fork-join/)**: a fork/join handle that transfers
  a task's result and its owned resource between threads, built from the toolkit in Parts 1–4.
- **[5.2. Atomic Contracts](./atomic-contracts/)**: a ticket lock, verified first with a
  shared invariant and then with atomic contracts for its acquisition loop.
- **[5.3. Iterated Separating Conjunctions](./iterated-star/)**: a shelf of counters protected
  by a shared invariant owning an indexed family of cells.
- **[5.4. Prophecies](./prophecies/)**: a distributed counter whose `get` uses prophecy
  variables and a helping protocol to establish its linearization point.

{{ref app:automation}} collects the automation features used throughout these capstones.
