# Appendix D: Where to Go Next

More worked examples than this tutorial covers, all in the main repository:

- **`test/concurrent/lock/`** — this tutorial only used the ticket lock; the same directory has
  a spin lock, an MCS lock, and a CLH lock, each proved against the same `Lock` interface from
  Part 5b.
- **`test/concurrent/counter/`** — the real files [`hit_counter_ghost.rav`](../ghost-and-concurrency/hit_counter_ghost.rav)
  was adapted from, plus a variant with no invariant at all worth comparing against.
- **`test/concurrent/templates/`** — substantially harder, template-based proofs of realistic
  concurrent data structures: `give-up.rav` (a lock-coupling search tree), `bplustree.rav`, and
  the flow/keyset resource algebras (`flows_ra.rav`, `keyset_ra.rav`) those proofs are built on.
  This is a reasonable next stop once Part 5's capstones feel comfortable — it's where the
  "shelf of counters"-style techniques get applied to something with actual branching structure
  instead of a flat family of cells.
- **`test/arrays/`** and **`test/iterated-star/`** — more iterated-separating-conjunction
  examples beyond Part 5c's, including binary search and an in-place partition (`dutch-flag.rav`)
  over the same abstract-array pattern.
- **`test/comparison/`** — the same data structure (an atomic reference-counted pointer, a
  ticket-based reader-writer lock) proved multiple ways — with invariants, with atomic
  contracts, and (deliberately) incorrectly — worth reading once Part 5b's two-versions-of-the-
  same-proof comparison made sense to you.
- **`test/ext/prophecy/rdcss.rav`** — nothing in this tutorial's capstones needed *prophecy
  variables*, Raven's extension for reasoning about *future*-dependent linearization points: a
  call whose linearization point depends on what some other thread will do later, rather than
  anything true yet at the point it happens. RDCSS (restricted double-compare-single-swap) is a
  real example that needs exactly that, plus thread *helping* (one thread completing another's
  pending operation on its behalf) — genuinely advanced material, and a solid next stop once
  Part 5's capstones feel comfortable. This tutorial doesn't yet have a capstone built around
  prophecies; RDCSS itself is more than this tutorial would want to start with, and a simpler
  worked example belongs here eventually.

Beyond the repository, the CAV and thesis papers describing Raven's design and metatheory (see
this repository's `README.md` for citations) go considerably deeper into *why* Raven's fragment
of concurrent separation logic is sound relative to Iris — not needed to use the tool, but the
right place if the "why does this work at all" question from Part 4 is still on your mind.
