# 5b. Atomic Contracts — Capstone: The Ticket Lock

*Assumes: Part 3's interface/functor pattern (`LockResource`, a module parameterizing over an
abstract protected resource) and Part 4's invariant fold/unfold discipline, ghost fields, and
`fpu`. Not re-taught here — if either feels shaky, skim [Part 3](../../modules/) and
[Part 4](../../ghost-and-concurrency/) first; [5a](../fork-join/) exercises the same
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

We'll look at three files that implement the same algorithm with the same underlying resources:

- [`ticket_lock_invariant.rav`](./ticket_lock_invariant.rav) proves `acquire`/`release` correct
  with a plain shared invariant, exactly Part 4's toolkit.
- [`ticket_lock_atomic_direct.rav`](./ticket_lock_atomic_direct.rav) proves the *same*
  procedures correct using **atomic contracts** for the first time, in the most direct way
  possible: `acquire`'s retry loop, `wait_loop`, has no atomic contract of its own at all.
- [`ticket_lock_atomic.rav`](./ticket_lock_atomic.rav) is the version Raven's own test suite
  actually ships: the same algorithm again, but with `wait_loop` given its *own*, independent
  atomic contract and token, **composed** into `acquire`'s.

Reading all three side by side is the point of this section: nothing about the underlying
reasoning changes from the first file to the second — only its ergonomics. Going from the second
file to the third *does* change something, but not the reasoning either: it's a purely structural
choice about where one atomic step's worth of bookkeeping is allowed to live, and it's the best
concrete illustration this tutorial has of a claim worth taking seriously — an atomic
specification describes something *logically* atomic, not something *physically* atomic.

## The problem: linearizability, stated to a client {#sec:linearizability-to-client}

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

## The mechanics: `bindAU`/`openAU`/`abortAU`/`commitAU` {#sec:au-mechanics}

`acquire` itself, in `ticket_lock_atomic_direct.rav`, is where the atomic-update protocol starts:

```raven
proc acquire(l: Ref, implicit ghost r: R)
  atomic requires is_lock(l, r)
  atomic ensures is_lock(l, r) && locked(l) && resource(r)
{
  ghost val phi := bindAU()
  ghost var b : Bool
  r := openAU(phi)
  unfold is_lock(l)[b := b]
  val nxt: Int := l.next
  fold is_lock(l, r)[b := b]
  abortAU(phi)
  // ... draws a ticket via cas, retries on failure -- see the full file
}
```

Every call to an atomically-contracted procedure carries a ghost **atomic update token**,
manipulated by four ghost statements:

- **`bindAU()`** gets a handle on the token for *this* call — `phi` here. Its type is
  `AtomicToken<acquire>`: a token is permanently tagged with *which* atomically-contracted
  procedure (and, implicitly, which call to it) it belongs to, so passing `acquire`'s token where
  `release`'s was expected is a type error.
- **`openAU(phi)`** exchanges it for the current atomic precondition's resources — `is_lock(l,
  r)` here — for exactly one atomic step, the same one-step discipline Part 4's invariants
  enforce. Its return value, when there is one, is `acquire`'s own *implicit* parameters — here,
  just `r` — freshly rebound to whatever value currently makes the precondition hold. (`acquire`
  has one implicit parameter, hence one variable on `openAU`'s left-hand side; a procedure with
  none would write plain `openAU(phi);`, and one with several would list all of them.)
- **`abortAU(phi)`** closes that step by re-establishing the same precondition and handing the
  resources back unchanged — used here because drawing a ticket number via `cas` isn't yet the
  actual linearization point of `acquire`; nothing observable has happened yet.
- **`commitAU(phi, ...)`** closes the step at the actual linearization point, by establishing the
  atomic postcondition instead. Its last argument is a tuple of `acquire`'s own *return values* —
  here, `()`, since `acquire` has no `returns` clause at all; a procedure declared `returns (v:
  Int)` would instead write `commitAU(phi, someValue)`. Raven checks, at every return point of an
  atomically-contracted procedure, that its token was committed somewhere on the path to get
  there — a return without a `commitAU` first is rejected, the same way an unfolded invariant
  that's never folded back is.

## Threading a token through a retry loop directly {#sec:token-direct}

`acquire`'s retry loop is where it gets interesting: drawing a ticket via `cas` can fail (someone
else drew first) or succeed-but-not-yet-be-served (someone else is still ahead in line), and
either way `acquire` has to keep trying without ever pretending its *own* atomic step has
happened more than once. The implementation
in [`ticket_lock_atomic_direct.rav`](./ticket_lock_atomic_direct.rav) makes the most direct
choice possible: give the retry loop, `wait_loop`, no atomic contract of its own, and instead
hand it `acquire`'s own token straight through, still uncommitted:

```raven
proc wait_loop(l: Ref, x: Int, ghost token: AtomicToken<acquire>, implicit ghost r: R)
  requires own(l.tickets, AuthDisjInts.frag(IntSet.set({|x|})))
  requires au<acquire>(token, l)
  ensures auCommit<acquire>(token, l, ())
{
  ghost var b: Bool
  r := openAU(token, l)
  unfold is_lock(l)[b := b]
  val c: Int := l.curr

  if (x == c) {
    fold is_lock(l, r)[b := true]
    commitAU(token, l, ())
    return
  } else {
    fold is_lock(l, r)[b := b]
    abortAU(token, l)
    wait_loop(l, x, token)
  }
}
```

Two new assertion forms show up in `wait_loop`'s own (perfectly ordinary, non-atomic) contract:
`au<acquire>(token, l)` is the resource-level fact "I am holding `acquire`'s atomic update
obligation, still uncommitted, for a call `acquire(l)` represented by `token`" — the
*precondition* side; `auCommit<acquire>(token, l, ())` is its counterpart once committed, naming
the same call together with the return values it committed with. Both take the token, then the
owning procedure's own concrete (non-implicit) arguments as a tuple — `l` alone here, since
`acquire`'s only other parameter, `r`, is implicit.  `wait_loop` never calls `bindAU()` itself;
there is exactly one token in this entire story, created once by `acquire`, and `wait_loop`'s job
is entirely about eventually committing that same token, not creating one of its own.

That's also why every `openAU`/`abortAU`/`commitAU` call on `token` inside `wait_loop` spells out
`l` explicitly, unlike `acquire`'s own bare `openAU(phi)`/`abortAU(phi)`: those shortcuts only
work when a procedure is manipulating a token that's *its own* — Raven can read the enclosing
call's own arguments off the surrounding scope automatically. A token belonging to some *other*
procedure — `acquire`'s, as far as `wait_loop` is concerned — always needs its owner's arguments
supplied by hand, exactly the way `au`/`auCommit` do in the contract above. The overall shape is
just open, read, then either abort-and-recurse or commit-and-return — the retry recursion is
transparently just more of `acquire`'s own single step, which is precisely what it always was.

## Composing atomic contracts {#sec:composing-atomic-contracts}

[`ticket_lock_atomic.rav`](./ticket_lock_atomic.rav) — the version Raven's own test suite ships —
makes a different structural choice: `wait_loop` gets an atomic contract of its own, and its own,
independent token:

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

`acquire` now calls it as an ordinary, atomically-specified procedure — `wait_loop(l, nxt)` —
right after re-opening its own token, then closes with its own `commitAU(phi, ())` once
`wait_loop` returns. That "re-open, call, commit" shape is the key thing to notice: calling an
atomically-contracted procedure while your own token is open is legal, and it consumes *exactly*
that one open step, no matter how many physical statements — or recursive calls — the callee
actually takes to get there. `wait_loop` might retry an unbounded number of times before it
commits; from `acquire`'s point of view, none of that is visible, because `wait_loop`'s own
contract already guarantees the whole thing behaves as one atomic step. That's the payoff of
having a *nested* atomic contract in the first place: `wait_loop` becomes an independently
reusable, independently understandable atomic operation — usable anywhere a client needs exactly
this ticket-serving step — rather than logic that only makes sense spliced into `acquire`'s own
body.

Compare the two versions side by side and the underlying lesson becomes concrete rather than
just a slogan: **an atomic specification describes something logically atomic, not something
physically atomic.** The direct version's retry loop and the composed version's separately
atomic `wait_loop` produce the *exact same* observable contract for `acquire` — the same `atomic
requires`/`atomic ensures` pair, unchanged — despite one of them taking a visibly different,
strictly more recursive, more multi-step path to get there internally.

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
