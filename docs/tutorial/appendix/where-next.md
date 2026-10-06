# Appendix F: Where to Go Next

The main repository contains many more worked examples than this tutorial covers:

- **`test/concurrent/lock/`**: this tutorial only used the ticket lock. The same directory has
  a spin lock, an MCS lock, and a CLH lock, each proved against the same `Lock` interface from
  Part 5.2.
- **`test/concurrent/counter/`**: the original files that
  [`hit_counter_ghost.rav`](../ghost-and-concurrency/hit_counter_ghost.rav) was adapted from,
  plus a variant with no invariant at all that is worth comparing against.
- **`test/concurrent/templates/`**: substantially harder, template-based proofs of realistic
  concurrent data structures. These include `give-up.rav` (a lock-coupling search tree),
  `bplustree.rav`, and the flow/keyset resource algebras (`flows_ra.rav`, `keyset_ra.rav`) that
  those proofs are built on. This is a reasonable next step once Part 5's capstones feel
  comfortable. It's where the techniques from the "shelf of counters" are applied to something
  with actual branching structure instead of a flat family of cells.
- **`test/arrays/`** and **`test/iterated-star/`**: more iterated-separating-conjunction
  examples beyond those in Part 5.3, including binary search and an in-place partition (`dutch-flag.rav`)
  over the same abstract-array pattern.
- **`test/comparison/`**: the same data structures (an atomic reference-counted pointer, a
  ticket-based reader-writer lock) proved in multiple ways, with invariants, with atomic
  contracts, and (deliberately) incorrectly. These are worth reading once the comparison of the
  two versions of the same proof in Part 5.2 makes sense to you.
- **`test/ext/prophecy/rdcss.rav`**: Part 5.4's distributed counter is this tutorial's
  introduction to *prophecy variables* and thread *helping* (one thread completing another's
  pending operation on its behalf). RDCSS (restricted double-compare-single-swap) needs the same
  two ingredients, applied to a real building block for software transactional memory rather than
  a teaching example. It is not simply harder, though. It uses *multi-shot* prophecies to
  predict every interfering thread's schedule in advance, but its helping protocol only ever
  tracks one pending thread at a time. So unlike the distributed counter with its `forall` over a
  whole registered set, it doesn't need an ISC at all. This is a good next step once Part 5.4
  feels comfortable.

Beyond the repository, the CAV and thesis papers describing Raven's design and metatheory (see
this repository's `README.md` for citations) go considerably deeper into *why* Raven's fragment
of concurrent separation logic is sound relative to Iris. You don't need this to use the tool,
but it's the right place to look if the "why does this work at all" question from Part 4 is
still on your mind.
