# 5.4. Prophecies — Capstone: A Distributed Counter

*Assumes: Part 4's shared invariants ({{ref sec:shared-invariants}}), ghost fields and resource
algebras ({{ref sec:ghost-fields-resource-algebras}}), and frame-preserving updates
({{ref sec:frame-preserving-updates}}); [5.1](../fork-join/)'s one-shot ownership-transfer pattern;
[5.2](../atomic-contracts/)'s atomic-update mechanics ({{ref sec:au-mechanics}}); and
[5.3](../iterated-star/)'s iterated separating conjunction ({{ref sec:the-isc}}). This capstone
combines all four rather than teaching new material from any one of them — not re-taught here.*

Every proof so far has reasoned about the past and the present: what a thread has already done,
what's true of the heap right now. A **prophecy variable** lets a proof reason about the future
instead — specifically, about the outcome of a nondeterministic choice (which thread's `incr` runs
next, what a scheduler decides) that hasn't happened yet, but that the proof needs to name and
reason about *before* it happens. This section builds up to that idea with a small warm-up
([`lazy_coin.rav`](./lazy_coin.rav)), then spends most of its time on the capstone proper: a
counter whose `get` operation doesn't always know its own linearization point without help from a
concurrent `incr` ([`dist_counter.rav`](./dist_counter.rav)).

> Raven's support for prophecy variables follows the design laid out in **The Future is Ours:
> Prophecy Variables in Separation Logic**, by Ralf Jung, Rodolphe Lepigre, Gaurav Parthasarathy,
> Marianna Rapoport, Amin Timany, Derek Dreyer, and Bart Jacobs (*POPL 2020*,
> **DOI:** [10.1145/3371113](https://doi.org/10.1145/3371113)).
>
> `lazy_coin.rav`, this section's warm-up example, is based on an example from that paper; the
> distributed counter that follows it was designed specifically for this tutorial.

## Predicting a value that hasn't been decided yet {#sec:predicting-the-future}

`Proph[T, 1]` is the type of a **one-shot prophecy**: a ghost value that predicts a single,
not-yet-determined value of type `T`. Allocating one is a statement of its own:

```raven
var myProph: Proph[Int, 1]
var myPred: Int
myProph, myPred := new Proph[Int, 1]
```

`myPred` comes back completely unconstrained — as far as this point in the proof knows, it could
be anything. That's the point: it is a *name* for whatever the real outcome eventually turns out to
be, fixed the moment the prophecy is created, usable in reasoning from here on regardless of
whether that outcome is known yet. The resource `Proph.proph(myProph, myPred)` — automatically
held right after `new Proph[Int, 1]`, the same way an ordinary `new(...)` hands back `own` facts
for the fields it just wrote — is the permission "I know this prophecy's predicted value." It
behaves like any other `own`-shaped resource (under the hood, a `Proph[T, 1]` value *is* a `Ref`,
the same erasure trick `AtomicToken` uses; the prediction is just another ghost field on it), with
one distinctive rule: `Proph.resolve` spends it for good.

```raven
var actual: Int
Proph.resolve(myProph, actual)
assert myPred == actual
```

`Proph.resolve(p, v)` gives up the resource `Proph.proph(p, myPred)` for good — nothing hands it
back afterward, so a second `Proph.resolve` on the same `p` has nothing left to give up (see
Debugging Corner) — and in exchange, assumes `v == myPred`. That's not a proof obligation `Proph.resolve` is asking *you* to
discharge, the way an `assert` would be: it doesn't check that `v` matches some hidden truth about
the future. It simply marks the program point where the prophesied value is tethered to the value
the execution actually produces — before this point, `myPred` was only ever a handle on a value not
yet observed, not a claim about what that value is. The reasoning `myPred` took part in between its
allocation and this `Proph.resolve` already had to go through for *every* value it might have
turned out to be, so by the time resolution ties it to the one concrete `v` this execution actually
computed, there's nothing left to verify — that's exactly what makes the technique sound rather
than a trust-me shortcut.

## A coin that already knows its own answer {#sec:reading-the-coin}

`lazy_coin.rav` is a coin that's undetermined until first read, but — read once by any number of
threads — always reads the same way after that. All the code below is in that file.

```raven
module PLC {
  field c: Library.Option[Bool]
  field p: Proph[Bool, 1]
  // pred lazy_coin, proc new_lazy_coin, proc read_lazy_coin below
}
```

```raven
pred lazy_coin (coin: Ref, b: Bool) {
  exists b': Library.Option[Bool], p': Proph[Bool, 1] ::
    own(coin.c, b') && own(coin.p, p') &&
    (b' == Library.Option.some(b'.Library.Option.value) ?
      b'.Library.Option.value == b :
      Proph.proph(p', b)
    )
}
```

Read `b` as "the coin's eventual answer" — fixed forever the moment the coin is created, whether
or not anyone has actually looked at it yet. The predicate's own two branches are just the two
ways that fixed answer can currently be represented: physically, if the field `c` already holds
`some(v)` (`v == b`, an ordinary equality), or purely as a prediction, if nobody has read the coin
yet (`c == none`, and `Proph.proph(p', b)` stands in for the missing physical value). Either way,
`b` is the coin's answer as far as any client is concerned — nobody outside `PLC` needs to know
which of the two branches currently applies.

```raven
proc new_lazy_coin() returns (ret: Ref, implicit ghost b: Bool)
  ensures lazy_coin(ret, b)
{
  var p1: Proph[Bool, 1]
  var z: Bool
  p1, z := new Proph[Bool, 1]
  var x: Ref := new(c: Library.Option.none, p: p1)
  fold lazy_coin(x, z)
  return x, z
}
```

Creating the coin allocates the prophecy first, then a fresh `Ref` with `c: none` — nothing
physical has been decided — and folds `lazy_coin` with `z`, the prophecy's own freshly-predicted
value, as the witness for `b`. That fold goes through for free: `c == none` puts the proof on
`lazy_coin`'s second branch, and `new Proph[Bool, 1]` already handed back `Proph.proph(p1, z)`
automatically. `z` is exposed to the caller as the implicit ghost return `b` — the coin's answer
already has a name, even though nobody has computed it yet.

```raven
proc read_lazy_coin(coin: Ref, implicit ghost b: Bool)
  returns (ret: Bool)
  requires lazy_coin(coin, b)
  ensures lazy_coin(coin, b) && ret == b
{
  unfold lazy_coin(coin, b)
  var c_val := coin.c
  ghost var proph_id := coin.p
  if (c_val == Library.Option.none) {
      var b: Bool
      havoc b
      coin.c := Library.Option.some(b)
      Proph.resolve(proph_id, b)
      fold lazy_coin(coin, b)
      return b
  } else {
      var res := c_val.Library.Option.value
      fold lazy_coin(coin, b)
      return res
  }
}
```

The `else` branch is the easy case: the coin was already decided, so read the stored value and
you're done. The `if` branch is the first read: `var b: Bool` declares a fresh local, and `havoc b`
assigns it an arbitrary value — chosen anew, unconstrained, every time this statement runs — which
is the real nondeterministic choice this coin models. That value is then written physically, and
`Proph.resolve(proph_id, b)` ties it to the answer the coin's creation already fixed. Notice the
local `var b: Bool` shadows the outer implicit ghost parameter `b` for the rest of this branch;
that's legal, and deliberate.
It can look, at a glance, like the postcondition `ret == b` is holding by naming coincidence — it
isn't. `Proph.resolve` is exactly what establishes the (till-then unknown) equality between the two
`b`s; before that statement, nothing forces the freshly-tossed local value to match the outer one
at all.

## A linearization point that depends on the future {#sec:future-dependent-linearization}

`dist_counter.rav` is the capstone proper: a counter whose value is split across two cells, `a`
and `b`, each bumped independently by `incr` to spread out contention.

```raven
type Counter = data { case counter(a: Ref, b: Ref, shared: Ref) }
```

`get` has to report `a.count + b.count` as of one single instant, but physically reads the two
fields one after another, and any number of `incr` calls may run in between those reads. If none
do, `get`'s own two reads are unambiguously its linearization point, the same shape as every atomic
contract in [5.2](../atomic-contracts/). But if a concurrent `incr` lands between the reads and
happens to bring the running total to exactly the value `get` ends up reporting, *that* `incr`
call — not either of `get`'s own reads — is really `get`'s linearization point. Worse: at the
moment `get` needs to commit *some* atomic step (`bindAU`/`openAU`/`commitAU`, {{ref sec:au-mechanics}}),
it cannot yet know which case it's in — whether some future `incr` will land on its answer before
it finishes its own two reads, or whether it will end up linearizing on its own. Compare
[5.2](../atomic-contracts/)'s ticket lock: `wait_loop` also doesn't know its linearization point in
advance, but it's always resolved by *its own* next loop iteration, on the same thread. Here it can
be resolved by a *different* thread's `incr` — one that, at the moment `get` calls `bindAU()`,
might not even have started yet.

## The helping protocol: predict, register, let someone else finish for you {#sec:the-helping-protocol}

The recipe `get` and `incr` use together, before looking at any of the ghost-field bookkeeping
that realizes it:

1. `get` predicts its own eventual return value with a one-shot prophecy, *before* reading either
   field.
2. It allocates a **helping cell** — an ordinary `Ref` — recording its live snapshot of the total
   at registration time, its own still-open atomic-update token, and its prediction.
3. It registers that cell with the counter's shared invariant, then proceeds with its own two
   reads as normal.
4. Every `incr`, right after its own physical increment and its own `commitAU`, advances every
   registered cell's snapshot to match the new total — and if a cell's snapshot has just reached
   that cell's own prediction, `incr` commits *that* `get` call's atomic update on its behalf,
   using the token the cell carries.
5. If `get`'s own snapshot already matched its prediction the moment it registered — no concurrent
   `incr` was ever going to catch it — `get` commits its own atomic update immediately, right
   there, without registering as pending anything.

This is a **helping protocol**: one thread completing another thread's still-open atomic update,
because it happens to be the one in a position to do so. It's a direct use of something
[5.2](../atomic-contracts/) already established: an atomic-update token can be committed by
whichever thread is holding it, not necessarily the thread whose pending call it belongs to —
`wait_loop` threading `acquire`'s own token by hand is the same mechanism, on a single retry loop
rather than across threads.

The ghost fields this needs:

```raven
ghost field total: Int
ghost field count_a_max: AuthMaxNat
ghost field count_b_max: AuthMaxNat
ghost field regs_auth: Auth[SetRA[Ref]]

ghost field snap: Int
ghost field token: AtomicToken<get>
ghost field count_proph: Int
ghost field snap0: Int
```

`AuthMaxNat = Auth[MaxNat]` is exactly the construction [Part 4](../../ghost-and-concurrency/)'s
`hit_counter_ghost.rav` builds for a single monotonically-growing counter — here applied to
`a.count` and `b.count` *individually*, not just their sum. That's not redundancy: `get` reads them
at two different times (`a` first, `b` second), and pinning down that its registration snapshot
`snap0` is a valid lower bound on its eventual answer needs each field's *own* monotonicity — a
fact about the combined total alone wouldn't rule out the case that `b.count` grows and `a.count`
shrinks between the two reads, but their sum at the point of the second read is still larger than
the sum at the point of the first read. In this scenario, there would be no point between the two
reads at which both counters sum up to the value that `get` eventually returns, violating
linearizability. `regs_auth: Auth[SetRA[Ref]]` is a different flavor of the same Part 4 idea:
`SetRA[X]`'s composition is set union, and its frame-preserving updates only ever grow the set
(`fpuAllowed` requires the old set to be a subset of the new one) — the same "can only move
forward" shape `MaxNat` gives numbers, here giving the *set of currently-registered helping cells*.
`counter_inv` always holds `Auth.full(...)` of it (auth and fragment equal, no split) — it isn't
used to hand out lower-bound witnesses the way `count_a_max`/`count_b_max` are, only to license an
`fpu` when `get` adds a new cell.

The last four fields are per-helping-cell: `snap` is that cell's live view of the total, kept in
lockstep by every `incr`; `token` is that `get` call's own atomic-update token, held so a helping
`incr` can commit on its behalf; `count_proph` is the value that call's prophecy predicted; `snap0`
is the total as of registration, frozen forever after.

## The counter's invariant, and an ISC over a set {#sec:counter-invariant}

```raven
inv helping_prot_state(hcell: Ref, c: Counter) {
  (exists n: Int, token: AtomicToken<get>, np: Int, snap0: Int ::
    own(hcell.snap, n, 0.5) &&
    own(hcell.token, token, 0.5) &&
    own(hcell.count_proph, np, 0.5) &&
    own(hcell.snap0, snap0, 0.5) &&
    snap0 <= n &&
    (snap0 <= np ==> (np <= n ? done(c, token, np) : pending(c, token))))
}
```

Every field here is held as a 0.5 share — {{ref sec:fractional-permissions}}'s fractional
discipline again, just with the *other* half in a different place depending on the field. `snap`'s
other half lives directly in `counter_inv` itself, kept in lockstep with the real total on every
fold; `snap0`'s other half is retained by `get` and never spent elsewhere, so that whenever `get`
later re-unfolds `helping_prot_state`, the two fractions of that same field are forced to agree —
handing `get` back its own registration snapshot as the invariant's own internal witness, for free,
with no need to thread it through as an extra parameter. `snap0 <= n` holds
unconditionally: `snap` only ever moves up from its registration value `snap0` (`bump_all`'s sole
update is `n -> n+1`), so this is just monotonicity, restated as an invariant. The guard
`snap0 <= np` on the interesting fact is what makes registering *before* knowing whether your own
prediction is even plausible safe: if the prediction `np` turns out to be *lower* than the
registration snapshot `snap0` — impossible in the end, but not yet known to be impossible at
registration time — the whole implication holds vacuously, nothing to prove, nothing ruled out
yet. `get` closes that gap for real later (see below), once its own prophecy has actually
resolved and both fields' monotonicity is available to invoke.

```raven
inv counter_inv(c: Counter) {
  exists na: Int, nb: Int ::
    own(c.a.count, na) && own(c.b.count, nb) &&
    own(c.shared.total, na + nb, 0.5) &&
    own(c.shared.count_a_max, AuthMaxNat.auth_frag(na, na)) &&
    own(c.shared.count_b_max, AuthMaxNat.auth_frag(nb, nb)) &&
    (exists regs: FinSet[Ref] ::
       own(c.shared.regs_auth, Auth.full(SetRA.set(regs))) &&
       (forall hcell: Ref ::
          hcell in regs ==>
            own(hcell.snap, na + nb, 0.5) && helping_prot_state(hcell, c)))
}
```

The `forall hcell: Ref :: hcell in regs ==> ...` line is [5.3](../iterated-star/)'s iterated
separating conjunction again ({{ref sec:the-isc}}) — one `own`/`helping_prot_state` fact per
registered cell, all folded and unfolded together as a single unit — just indexed by set
membership instead of an integer range. It doesn't need 5.3's own injectivity side condition
({{ref sec:injectivity-side-condition}}): that condition existed there because `S.loc(s, i)` was
an axiom that, without `all_diff`, could in principle send two different indices to the same
location. Here there's no addressing function to go wrong — membership in a `FinSet[Ref]` already
guarantees each element is counted at most once, so there's nothing separate left to prove.

## `get`: predict, register, maybe finish on the spot {#sec:get-predict-register}

```raven
proc get(c: Counter, implicit ghost n: Int) returns (ret: Int)
  requires is_counter(c)
  atomic requires counter_state(c, n)
  atomic ensures counter_state(c, n) && ret == n
{
  ghost var phi := bindAU()
  ghost var regs: FinSet[Ref]
  ghost var predicted: Int
  ghost var proph_id: Proph[Int, 1]
  proph_id, predicted := new Proph[Int, 1]
  ghost var snap0: Int
  unfold counter_inv(c)[regs := regs]
  snap0 :| own(c.shared.total, snap0, 0.5)
  ghost val hcell := new(snap: snap0, token: phi, count_proph: predicted, snap0: snap0)
  {!
    if (snap0 == predicted) {
      ghost val opened_: Int := openAU(phi)
      commitAU(phi, predicted)
    }
  !}
  fold helping_prot_state(hcell, c)
  fpu(c.shared.regs_auth, Auth.auth(SetRA.set(regs)), Auth.full(SetRA.set(regs ++ {|hcell|})))
  val n1 := c.a.count
  fold counter_inv(c)[regs := regs ++ {|hcell|}]

  unfold counter_inv(c)[regs := regs]
  val n2 := c.b.count
  Proph.resolve(proph_id, n1 + n2)
  unfold helping_prot_state(hcell, c)
  fold helping_prot_state(hcell, c)
  fold counter_inv(c)[regs := regs]
  return n1 + n2
}
```

The prophecy is allocated before either field read — `predicted` is fixed from here on, entirely
unconstrained, possibly a value the counter has already passed by the time `get` even registers.
`snap0 :| own(...)` is {{ref sec:bind-statement}}'s bind statement, recovering the invariant's
current total as a plain ghost value. The `{! if (snap0 == predicted) { ... } !}` block — a ghost
block ({{ref sec:ghost-blocks-erasure}}), since it branches on ghost state — is the "lucky case"
from the recipe above: if the total already equals the prediction, there is provably no concurrent
`incr` left that could still bring the total *up to* that value later (it's already there), so
`get` commits its own atomic update immediately rather than registering as pending. Either way,
`fold helping_prot_state(hcell, c)` closes the cell's own invariant — trivially true if just
committed, or true by `helping_prot_state`'s vacuous case otherwise — and `fpu` extends the
registered set by exactly one element, [5.3](../iterated-star/)-style bookkeeping around a
[5.3](../iterated-star/)-shaped `forall`, now licensed by `SetRA`'s own frame-preserving-update
rule rather than `MaxNat`'s.

The two field reads (`n1`, then `n2`) happen with the cell already registered, exactly as the
recipe describes. `Proph.resolve(proph_id, n1 + n2)` is where the prediction meets reality: from
here on, `predicted == n1 + n2`. The closing `unfold`/`fold` of `helping_prot_state` is where
`snap0 <= n1 + n2` gets nailed down for real — `a.count` can only have grown since `n1` was read
from it (`count_a_max`'s own monotonicity), and `b.count` *is* `n2`, read directly — closing the
gap `helping_prot_state`'s guard left open at registration. The same two facts, read the other way,
also give `n1 + n2 <= n`, where `n` is the counter's *current* total at this second unfold —
`a.count`'s current value can only be `>= n1`, and `b.count`'s current value *is* `n2`, so their sum
is at least `n1 + n2`. Both halves of `helping_prot_state`'s guard are now pinned down at once, and
only one branch of it survives: `np <= n` holds, so this cell is provably already `done` — its
atomic update has already been committed, whether by `get` itself, back in the lucky case above, or
by some concurrent `incr`'s `bump_all` in the meantime.

## `incr` and `bump_all`: helping on someone else's behalf {#sec:bump-all-helping}

```raven
lemma bump_all(c: Counter, n: Int, regs: FinSet[Ref])
  requires counter_state(c, n+1)
  requires forall hcell0: Ref :: hcell0 in regs ==> own(hcell0.snap, n, 0.5) && helping_prot_state(hcell0, c)
  ensures forall hcell0: Ref :: hcell0 in regs ==> own(hcell0.snap, n + 1, 0.5) && helping_prot_state(hcell0, c)
  ensures counter_state(c, n+1)
  decreases regs
{
  if (regs != {||}) {
    ghost val hcell := choose(regs)
    bump_all(c, n, regs -- {|hcell|})
    unfold helping_prot_state(hcell, c)
    hcell.snap := n + 1
    var np: Int
    np :| own(hcell.count_proph, np, 0.5)
    var tok: AtomicToken<get>
    tok :| own(hcell.token, tok, 0.5)
    if (n + 1 == np) {
      val opened_: Int := openAU(tok, c)
      commitAU(tok, c, np)
    }
    fold helping_prot_state(hcell, c)
  }
}
```

`choose(regs)` is [Part 1](../../sequential/)'s `choose`, picking one element out of a `FinSet` to
recurse on. For each registered cell, `bump_all` advances its `snap` to the new total, then checks
whether that bump *just* reached the cell's own prediction (`n + 1 == np`) — if so, this is that
`get` call's real linearization point, wherever `get`'s own control flow has gotten to, and
`bump_all` opens and commits *that call's* token, using its owner's own arguments explicitly, the
same way `wait_loop` in [5.2](../atomic-contracts/) manipulates `acquire`'s token from the outside.

```raven
proc incr(c: Counter, implicit ghost n: Int)
  requires counter_inv(c)
  atomic requires counter_state(c, n)
  atomic ensures counter_state(c, n + 1)
{
  // ... draws a target cell, faa's it, and advances count_a_max/count_b_max -- see the full file
  commitAU(phi, ())
  bump_all(c, n, regs)
  fold counter_inv(c)[regs := regs]
}
```

`incr` commits its *own* atomic update first — its own linearization point is always its own
physical `faa`, never in question — and only then calls `bump_all`, which may, as a side effect,
also commit some unrelated `get` call's atomic update, on a different token, for a different
thread. Nothing about `incr`'s own contract mentions that; it's invisible from the outside, exactly
as an atomic specification is supposed to be.

## Beyond counters: the same protocol elsewhere

Nothing about this recipe — predict your own answer, register a helping cell, let a concurrent
operation complete you if it lands on your prediction — is specific to counters. It's the same
shape as the "helping" technique used to prove non-blocking data structures whose linearization
point is decided by a *different* thread's successful `cas`: a `contains` or `find` call on a
lock-free set can have its own answer settled by a concurrent `insert` or `remove`,
exactly the way `get` here can have its answer settled by a concurrent `incr`. Registering a
helping cell in a shared invariant, and having every mutating operation check the registry after
its own physical step, transfers almost one-to-one. `test/ext/prophecy/rdcss.rav` (mentioned again
in Appendix E) applies the same two ingredients — prophecy and helping — to restricted
double-compare-single-swap, a real building block for software transactional memory, not just a
teaching example. It isn't simply harder: it reaches for *multi-shot* prophecies, predicting the
schedules of every interfering thread in advance, which this capstone's one-shot `Proph[Int, 1]`
never needed to. Its own helping protocol, on the other hand, only ever has one thread's call to
track as pending at a time — unlike `counter_inv`'s `forall` over a whole registered set, it
doesn't need an ISC at all.

## Debugging Corner

A one-shot prophecy's `Proph.proph(p, v)` resource is given up for good the moment
`Proph.resolve(p, ...)` runs — nothing hands it back, unlike an invariant's fold/unfold.
Resolving the same prophecy twice ([`broken/double_resolve.rav`](./broken/double_resolve.rav))
tries to give up a resource that's no longer there:

```
[Error] File "./double_resolve.rav", line 12, columns 2-32:
12 |   Proph.resolve(myProph, actual)
       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Verification Error: This prophecy's resource is not available here -- it may already have
been resolved, or it may still be held elsewhere in the proof.
[Error] File "./double_resolve.rav", line 12, columns 2-32:
12 |   Proph.resolve(myProph, actual)
       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
Related Location: This own predicate may not hold.
```

Notice the message doesn't actually claim the prophecy was already resolved — only that its
resource isn't available *at this point in the proof*. In `double_resolve.rav` that's because it
really was already spent, two lines up, but the same message fires for a differently-shaped
mistake too: calling `Proph.resolve` before the resource has actually been brought into scope here
(still sitting inside an unopened invariant, say) looks identical from `Proph.resolve`'s own
point of view, so the diagnostic doesn't guess between the two.

It's also worth being precise about what a single `Proph.resolve` actually connects: `v == myPred`
holds for the *specific* `Proph.proph` resource it just gave up — resolving one prophecy ties down
that one value and nothing else; it has no bearing on any other value elsewhere in your proof
state, prophesied or otherwise.

## What's next

[5.5](../automation/) collects the smaller automation features — implicit parameters, witness
computation, `auto` lemmas, triggers, `assert ... with` — that all four capstones have been
quietly leaning on without calling out by name, this one included (`get`'s
`implicit ghost n: Int`, `is_counter`/`counter_state` as `auto pred`s, `helping_prot_state`'s own
guarded existential).
