# 5.2. Atomic Contracts

*Assumes: Part 3's interface/functor pattern (`LockResource`, a module parameterizing over an
abstract protected resource) and Part 4's invariant fold/unfold discipline, ghost fields, and
`fpu`. These are not re-taught here. If either feels shaky, skim [Part 3](../../modules/) and
[Part 4](../../ghost-and-concurrency/) first. [5.1](../fork-join/) exercises the same
material from start to finish and is a good warm-up if you haven't done it yet.*

A **ticket lock**, also called the *bakery algorithm*, is a mutual-exclusion lock where waiting
threads are served in first-come-first-served order, like a numbered queue at a bakery counter.
A thread calling `acquire` atomically draws a ticket number and then spins, watching a shared
"now serving" counter, until it's called.

If 5.1's fork/join felt comfortable, most of the structure here should too. It uses the same
existentials-plus-boolean-flag invariant pattern, and the same `LockResource`/`Lock`-as-functor
structure as `Instance`/`ForkJoin` there. What's new in this section is what happens once mutual
exclusion (rather than a one-shot handoff) needs a *retry loop*, and atomic contracts, a more
convenient way of stating what that loop guarantees.

We'll look at three files that implement the same algorithm with the same underlying resources:

- [`ticket_lock_invariant.rav`](./ticket_lock_invariant.rav) proves `acquire`/`release` correct
  with a plain shared invariant, using exactly the toolkit from Part 4.
- [`ticket_lock_atomic_direct.rav`](./ticket_lock_atomic_direct.rav) proves the *same*
  procedures correct using **atomic contracts** for the first time, in the most direct way
  possible: `acquire`'s retry loop, `wait_loop`, has no atomic contract of its own at all.
- [`ticket_lock_atomic.rav`](./ticket_lock_atomic.rav) is the version included in Raven's own
  test suite. It is the same algorithm again, but with `wait_loop` given its *own*, independent
  atomic contract and token, **composed** into `acquire`'s.

This section is meant to be read with all three files side by side. Nothing about the
underlying reasoning changes from the first file to the second, only how it is expressed. Going
from the second file to the third *does* change something, but again not the reasoning. It's a
purely structural choice about where the bookkeeping for one atomic step is allowed to live. It
is also the best concrete illustration in this tutorial of an important point: an atomic
specification describes something *logically* atomic, not something *physically* atomic.

## The problem: linearizability, stated to a client {#sec:linearizability-to-client}

The invariant version's `acquire` has this contract:

```raven
proc acquire(l: Ref, implicit ghost r: R)
  requires lock_inv(l, r)
  ensures resource(r) && locked(l)
```

This is true and useful, but notice what it *doesn't* say. Nothing here describes *when*,
relative to other threads, the lock was actually acquired. It only says that by the time
`acquire` returns, you have `locked(l)`. A client that wants to reason about the lock as a single atomic
step in a bigger proof (the way you'd reason about a hardware `cas`) has to somehow reconstruct
that from `lock_inv`'s internals, which are supposed to be private to the lock's implementation.

Compare the atomic-contract version:

```raven
proc acquire(l: Ref, implicit ghost r: R)
  atomic requires is_lock(l, r)
  atomic ensures is_lock(l, r) && locked(l) && resource(r)
```

An **atomic triple**, `atomic requires P` / `atomic ensures Q`, says: "this call, however many
physical steps it actually takes, has *one* atomic step (its *linearization point*) at which the
abstract state visibly moves from something satisfying `P` to something satisfying `Q`. Every
other step is invisible to the outside." This is a strictly stronger, and more useful, promise
than an ordinary Hoare contract. From a logical perspective, a client can now treat `acquire` as
a single step in its own reasoning, the same way it would treat `cas` itself.

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

- **`bindAU()`** gets a handle on the token for *this* call, here `phi`. Its type is
  `AtomicToken<acquire>`. A token is permanently tagged with *which* atomically-contracted
  procedure (and, implicitly, which call to it) it belongs to, so passing `acquire`'s token where
  `release`'s was expected is a type error.
- **`openAU(phi)`** exchanges it for the resources of the current atomic precondition (here,
  `is_lock(l, r)`) for exactly one atomic step. This is the same one-step discipline that Part 4's
  invariants enforce. Its return value, when there is one, consists of `acquire`'s own *implicit*
  parameters (here, just `r`), freshly rebound to whatever value currently makes the precondition
  hold. (`acquire` has one implicit parameter, hence one variable on `openAU`'s left-hand side. A
  procedure with none would write plain `openAU(phi);`, and one with several would list all of
  them.)
- **`abortAU(phi)`** closes that step by re-establishing the same precondition and handing the
  resources back unchanged. It is used here because drawing a ticket number via `cas` isn't yet
  the actual linearization point of `acquire`, so nothing observable has happened yet.
- **`commitAU(phi, ...)`** closes the step at the actual linearization point by establishing the
  atomic postcondition instead. Its last argument is a tuple of `acquire`'s own *return values*,
  here `()`, since `acquire` has no `returns` clause at all. A procedure declared `returns (v:
  Int)` would instead write `commitAU(phi, someValue)`. At every return point of an
  atomically-contracted procedure, Raven checks that its token was committed somewhere on the path
  leading there. A return without a preceding `commitAU` is rejected, just like an unfolded
  invariant that's never folded back.

## Threading a token through a retry loop directly {#sec:token-direct}

`acquire`'s retry loop is where things get interesting. Drawing a ticket via `cas` can fail
(someone else drew first), or succeed while the thread is not yet served (someone else is still
ahead in line). Either way, `acquire` has to keep trying without ever pretending its *own* atomic
step has happened more than once. The implementation in
[`ticket_lock_atomic_direct.rav`](./ticket_lock_atomic_direct.rav) makes the most direct choice
possible. It gives the retry loop, `wait_loop`, no atomic contract of its own, and instead passes
it `acquire`'s own token, still uncommitted:

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

Two new assertion forms show up in `wait_loop`'s own (perfectly ordinary, non-atomic) contract.
On the *precondition* side, `au<acquire>(token, l)` is the resource-level fact "I am holding
`acquire`'s atomic update obligation, still uncommitted, for a call `acquire(l)` represented by
`token`." Its counterpart once committed is `auCommit<acquire>(token, l, ())`, which names the
same call together with the return values it committed with. Both take the token, followed by
the owning procedure's own concrete (non-implicit) arguments as a tuple. Here that is just `l`,
since `acquire`'s only other parameter, `r`, is implicit. `wait_loop` never calls `bindAU()`
itself. There is exactly one token in this whole proof, created once by `acquire`, and
`wait_loop`'s job is to eventually commit that same token, not to create one of its own.

This is also why every `openAU`/`abortAU`/`commitAU` call on `token` inside `wait_loop` spells
out `l` explicitly, unlike `acquire`'s own bare `openAU(phi)`/`abortAU(phi)`. Those shortcuts
only work when a procedure is manipulating a token that's *its own*, because then Raven can read
the enclosing call's arguments off the surrounding scope automatically. A token belonging to some
*other* procedure (`acquire`, from the perspective of `wait_loop`) always needs its owner's
arguments supplied by hand, exactly as `au`/`auCommit` do in the contract above. The overall
structure is simply open, read, and then either abort-and-recurse or commit-and-return. The retry
recursion is just part of `acquire`'s own single step, which is what it always was.

## Composing atomic contracts {#sec:composing-atomic-contracts}

[`ticket_lock_atomic.rav`](./ticket_lock_atomic.rav), the version in Raven's own test suite,
makes a different structural choice. `wait_loop` gets an atomic contract of its own, and its own
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

`acquire` now calls it as an ordinary, atomically-specified procedure, `wait_loop(l, nxt)`,
right after re-opening its own token, and then closes with its own `commitAU(phi, ())` once
`wait_loop` returns. This "re-open, call, commit" pattern is the key thing to notice. Calling an
atomically-contracted procedure while your own token is open is legal, and it consumes *exactly*
that one open step, no matter how many physical statements (or recursive calls) the callee
actually takes. `wait_loop` might retry an unbounded number of times before it commits. From
`acquire`'s point of view, none of that is visible, because `wait_loop`'s own contract already
guarantees that the whole thing behaves as one atomic step. This is the benefit of a *nested*
atomic contract. `wait_loop` becomes an atomic operation that can be reused and understood on
its own, wherever a client needs exactly this ticket-serving step, rather than logic that only
makes sense as part of `acquire`'s body.

Comparing the two versions side by side makes the underlying lesson concrete: **an atomic
specification describes something logically atomic, not something physically atomic.** The
retry loop of the direct version and the separately atomic `wait_loop` of the composed version
produce *exactly the same* observable contract for `acquire`, with the same `atomic
requires`/`atomic ensures` pair. This holds even though the second version takes a visibly
different, more recursive, multi-step path internally.

The opposite direction exists too, and is worth knowing about even though it isn't needed
here: code that really does take several steps, which you want *treated* as one. This is
`atomic { ... }`, or `atomic proc` for a whole procedure body. Unlike everything else in this
section, it is asserted rather than proved. By definition, Raven's semantics executes the block
as a single step, and whether the target machine actually does so is up to you. It is how the
library's primitives, such as `cas`, are written: as an `atomic proc` with an ordinary contract
describing its one step, which needs no atomic update token, since there is no other step to
hide. {{ref sec:anatomy}} and {{ref sec:atomic-block-standalone}} cover both forms. Strict mode
flags this assumption; see {{ref sec:strict-mode}} for how to enable it in VS Code.

## Calling an atomic procedure during invariant accesses {#sec:atomic-call-during-invariant-access}

Since a client can treat an atomically specified call as one step, it can make the call while
an invariant is open, just as it would use `cas`: unfold the invariant, let the call take its
atomic precondition from the invariant's contents, and fold the invariant again from the atomic
postcondition.

The call is one step only logically, though. While the callee runs its other steps, the
invariant is in fact closed, and other threads can open it. The callee may also abort and retry,
as `acquire` does above, which hands its atomic precondition back. So the invariant has to be
closable not only after the call commits, but also if it aborts: from what the caller still
holds, together with the atomic precondition, but without what the ordinary precondition handed
to the callee for the whole call. Raven checks this for the invariants open around the call.

[`broken/abort_unclosable.rav`](./broken/abort_unclosable.rav) shows a call that this check
rejects, although folding the invariant after the call succeeds:

```raven
inv dInv(x: Ref) {
  exists n: Int :: own(x.d, 0, 1.0) && own(x.c, n, 1.0)
}

proc p(x: Ref, implicit ghost n: Int)
  requires own(x.d, 0, 1.0)
  ensures own(x.d, 0, 1.0)
  atomic requires own(x.c, n, 1.0)
  atomic ensures own(x.c, n + 1, 1.0)

proc writer(x: Ref)
  requires dInv(x)
{
  unfold dInv(x);
  p(x);
  fold dInv(x);
}
```

`p` holds `own(x.d, 0, 1.0)` for its whole run, and its body writes `1` to `x.d` before its
linearization point, while `dInv` is closed and other threads rely on `x.d` being `0`. Raven
reports `An invariant open around this atomic call may not be closable if the call aborts` at
the call, with the `unfold` of `dInv` as a Related Location. To fix such a call, give it the
resources of its ordinary precondition from outside the invariant, or move them into its atomic
precondition, so that the callee uses them only at its linearization point.

The same holds for an atomic update that is open around the call: if the callee aborts, the
caller must still be able to abort its own update, giving back its atomic precondition, while
also closing every open invariant. Before checking this, Raven refolds the predicates unfolded
since the update or invariant was opened, using the variables an `unfold` bound its
existentials to as witnesses. A ghost update that cannot be undone this way, such as an `fpu`,
belongs after the call. Otherwise Raven reports `The atomic update open around this atomic call
may not be abortable if the call aborts`, or `A predicate unfolded around this atomic call may
not be refoldable if the call aborts`.

## Debugging Corner

The atomicity-analysis messages from Part 4 reappear here almost verbatim, now guarding
`bindAU`/`openAU`/`abortAU`/`commitAU` instead of `fold`/`unfold`. They are `Atomic token %s is
already open`, `Cannot commitAU: atomic token %s is not open` (and likewise for `abortAU`), and,
when a path reaches the end of the body with the token still open, `Missing commitAU or abortAU
for open atomic update phi`. The last one is reported at the closing brace with the `openAU` that
opened the token as a Related Location, exactly like Part 4's never-folded invariant. The main
thing is to recognize these as *the same family* of errors as in Part 4. There's nothing new to
learn here, just new statements to which the same one-step discipline applies.

One message is specific to calling an atomically specified procedure while an invariant is open:
`An invariant open around this atomic call may not be closable if the call aborts`, explained in
{{ref sec:atomic-call-during-invariant-access}}, together with its counterparts for an open
atomic update and for predicates unfolded since.

## What's next

[5.3](../iterated-star/) is the next capstone: an array of independently-lockable counters,
which needs a way to own an entire *family* of resources (one per array slot) at once, rather
than one at a time. {{ref app:automation}} collects the smaller automation features
(implicit parameters, witness computation, `auto` lemmas, triggers) that all four capstones
rely on without discussing them explicitly.
