# 5b. Atomic Contracts — Capstone: The Ticket Lock

*Assumes: Part 3's interface/functor pattern (`LockResource`, a module parameterizing over an
abstract protected resource) and Part 4's invariant fold/unfold discipline, ghost fields, and
`fpu`. Not re-taught here — if either feels shaky, skim [Part 3](../../03-modules/) and
[Part 4](../../04-ghost-and-concurrency/) first; [5a](../fork-join/) exercises the same
material end to end and is good warm-up if you haven't done it yet.*

A **ticket lock**, also called the *bakery algorithm*, is a mutual-exclusion lock where waiting
threads are served in first-come-first-served order, like a numbered queue at a bakery counter.
A thread calling `acquire` atomically draws a ticket number and then spins, watching a shared
"now serving" counter, until it's called.

If 5a's fork/join felt comfortable, most of the shape here should too: the same
existentials-plus-boolean-flag invariant pattern, the same `LockResource`/`Lock`-as-functor
structure as `Instance`/`ForkJoin` there. What's new in this section is what happens once mutual
exclusion (rather than a one-shot handoff) needs a *retry loop*, and the more ergonomic way —
atomic contracts — of stating what that loop guarantees.

We'll look at two files that implement the same algorithm with the same underlying resources:

- [`ticket_lock_invariant.rav`](./ticket_lock_invariant.rav) proves `acquire`/`release` correct
  with a plain shared invariant, exactly Part 4's toolkit.
- [`ticket_lock_atomic.rav`](./ticket_lock_atomic.rav) proves the *same* two procedures correct
  again, using **atomic contracts** instead.

Reading them side by side is the point of this section: nothing about the underlying reasoning
changes, only its ergonomics.

## The problem: linearizability, stated to a client

The invariant version's `acquire` has this contract:

```raven
proc acquire(l: Ref, implicit ghost r: R)
  requires lock_inv(l, r)
  ensures resource(r) && locked(l)
```

This is true and useful, but notice what it *doesn't* say: nothing here describes *when*,
relative to other threads, the lock actually got acquired — only that, by the time `acquire`
returns, you have `locked(l)`. A client that wants to reason about the lock as a single atomic
step in a bigger proof (the way you'd reason about a hardware `cas`) has to somehow reconstruct
that from `lock_inv`'s internals, which are supposed to be private to the lock's implementation.

Compare the atomic-contract version:

```raven
proc acquire(l: Ref, implicit ghost r: R)
  atomic requires is_lock(l, r)
  atomic ensures is_lock(l, r) && locked(l) && resource(r)
```

An **atomic triple** — `atomic requires P` / `atomic ensures Q` — says: "this call, however many
physical steps it actually takes, has *one* atomic step (its *linearization point*) at which the
abstract state visibly moves from something satisfying `P` to something satisfying `Q`; every
other step is invisible to the outside". That's a strictly stronger, and strictly more useful,
promise than an ordinary Hoare contract: from a logical perspective, a client can now treat
`acquire` as a single step in its own reasoning, the same way it would treat a primitive `cas`.

## The mechanics: `bindAU`/`openAU`/`abortAU`/`commitAU`

Look at `wait_loop` in `ticket_lock_atomic.rav`:

```raven
proc wait_loop(l: Ref, x: Int, implicit ghost r: R)
  requires own(l.tickets, AuthDisjInts.frag(IntSet.set({|x|})))
  atomic requires is_lock(l, r)
  atomic ensures is_lock(l, r) && locked(l) && resource(r)
{
  ghost val phi := bindAU()
  ghost var b: Bool
  r := openAU(phi)
  unfold is_lock(l)[b := b]
  val c: Int := l.curr

  if (x == c) {
    fold is_lock(l, r)[b := true]
    commitAU(phi, ())
    return
  } else {
    fold is_lock(l, r)[b := b]
    abortAU(phi)
    r := openAU(phi)
    wait_loop(l, x)
    commitAU(phi, ())
  }
}
```

Every call to an atomically-contracted procedure carries a ghost **atomic update** token,
manipulated by four ghost statements:

- **`bindAU()`** gets a handle (`phi`) on the token for *this* call.
- **`openAU(phi)`** exchanges it for the current atomic precondition's resources — `is_lock(l,
  r)` here — for exactly one atomic step, the same one-step discipline Part 4's invariants
  enforce.
- **`abortAU(phi)`** closes that step by re-establishing the same precondition and handing the
  resources back unchanged — used here every time this iteration *isn't* the winning one
  (`x != c`), because nothing observable happened yet.
- **`commitAU(phi, ...)`** closes the step at the actual linearization point, by establishing the
  atomic postcondition instead — used here exactly when `x == c`, the one iteration where the
  ticket is actually being served. Raven checks, at every return point of an atomically-
  contracted procedure, that its token was committed somewhere on the path to get there — a
  return without a `commitAU` first is rejected, the same way an unfolded invariant that's never
  folded back is.

The overall shape — open, do one step, either abort-and-retry or commit — is structurally
identical to the invariant version's unfold/fold-around-a-retry-loop. Atomic contracts aren't a
different proof technique so much as a more expressive *vocabulary* for the one you already
know.

## Debugging Corner

The atomicity-analysis vocabulary from Part 4 reappears here verbatim, just guarding
`bindAU`/`openAU`/`abortAU`/`commitAU` instead of `fold`/`unfold`: `Atomic token %s is already
open`, `Cannot commitAU: atomic token %s is not open` (and likewise for `abortAU`), and — when a
path reaches the end of the body with the token still open — `Missing commitAU or abortAU for
open atomic update phi`, reported at the closing brace with the `openAU` that opened it as a
Related Location, exactly like Part 4's never-folded invariant. Recognizing these as *the same
family* of error as Part 4's is the
actual point — there's nothing new to learn here, just a new pair of statements that the same
one-step discipline applies to.

## What's next

[5c](../iterated-star/) is the next capstone: an array of independently-lockable counters,
which needs a way to own an entire *family* of resources — one per array slot — at once, rather
than one at a time. [5d](../automation/) then collects the smaller automation features
(implicit parameters, witness computation, `auto` lemmas, triggers) that all three capstones
lean on without calling out by name.
