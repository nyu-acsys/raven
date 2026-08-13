# Appendix E: Where to Go Next

More worked examples than this tutorial covers, all in the main repository:

- **`test/concurrent/lock/`** — this tutorial only used the ticket lock; the same directory has
  a spin lock, an MCS lock, and a CLH lock, each proved against the same `Lock` interface from
  Part 5.2.
- **`test/concurrent/counter/`** — the real files [`hit_counter_ghost.rav`](../ghost-and-concurrency/hit_counter_ghost.rav)
  was adapted from, plus a variant with no invariant at all worth comparing against.
- **`test/concurrent/templates/`** — substantially harder, template-based proofs of realistic
  concurrent data structures: `give-up.rav` (a lock-coupling search tree), `bplustree.rav`, and
  the flow/keyset resource algebras (`flows_ra.rav`, `keyset_ra.rav`) those proofs are built on.
  This is a reasonable next stop once Part 5's capstones feel comfortable — it's where the
  "shelf of counters"-style techniques get applied to something with actual branching structure
  instead of a flat family of cells.
- **`test/arrays/`** and **`test/iterated-star/`** — more iterated-separating-conjunction
  examples beyond Part 5.3's, including binary search and an in-place partition (`dutch-flag.rav`)
  over the same abstract-array pattern.
- **`test/comparison/`** — the same data structure (an atomic reference-counted pointer, a
  ticket-based reader-writer lock) proved multiple ways — with invariants, with atomic
  contracts, and (deliberately) incorrectly — worth reading once Part 5.2's two-versions-of-the-
  same-proof comparison made sense to you.
- **`test/ext/prophecy/rdcss.rav`** — Part 5.4's distributed counter is this tutorial's
  introduction to *prophecy variables* and thread *helping* (one thread completing another's
  pending operation on its behalf). RDCSS (restricted double-compare-single-swap) needs the same
  two ingredients, applied to a real building block for software transactional memory rather than
  a teaching example — not simply harder, though: it reaches for *multi-shot* prophecies to
  predict every interfering thread's schedule in advance, but its helping protocol only ever
  tracks one pending thread at a time, so unlike the distributed counter's `forall` over a whole
  registered set, it doesn't need an ISC at all. A solid next stop once Part 5.4 feels comfortable.

Beyond the repository, the CAV and thesis papers describing Raven's design and metatheory (see
this repository's `README.md` for citations) go considerably deeper into *why* Raven's fragment
of concurrent separation logic is sound relative to Iris — not needed to use the tool, but the
right place if the "why does this work at all" question from Part 4 is still on your mind.
