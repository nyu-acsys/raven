# lclist notes

NOTE: OK, here's a new, hopefully more consolidated idea of what should be done:
- predicate that defines the general structure of the linked list, probably
also the sortedness requirement
- predicates that define the concurrent locking behavior of the list ---
how how threads must hold locks, how different threads interact with the locks
 - this might require me to define a new resource algebra...but this part
   is unclear
 - we'll probably need to specify linearizability with ghost state, possibly
   as part of a resource algebra
- each operation must be a FPU (if we need to use a resource algebra) that
preserves the expected invariants (both concrete and ghost)

IMPORTANT NOTE: Raven uses resource algebra types to model ghost state (just
like concrete types---i.e. Int, Bool, Ref---are used to model concrete state)
the default resource algebra is Frac

NOTE: Raven models the heap through typed fields---all separation logic
statements about the heap are done using typed fields

NOTE: Raven invariants are maintained *by every atomic computation step*
this makes them duplicable (and also easier to reason about, but less
expressive)

NOTE: own(x, c, v, 1.0) means we have ownership over field c of location x,
the value at x.c is n, and we own 1.0 fractional permission over the field
x.c

NOTE: It appears that a big point of the ARC resource algebra is to connect
global state to local state --- i.e. ensuring that any increase/decrease
in the local readers/permissions is reflected in the global readers/permissions.
Updates that satisfy this are the frame-preserving updates allowed in the
resource algebra.

QUESTION: What is a shareable predicate in Raven?
ANSWER: Seems like it's just what the name implies: a predicate that is
shareable (permission-wise) between multiple threads. It's an example of
a higher order module.

---

NOTE: need a specification and proof of lock behavior (we already have this with
spin-lock.rav)
NOTE: each node in the lclist has 3 fields --- a location with a value,
a tail pointer to the next node, and a lock

an invariant to describe the structure of the list, should be preserved
after every operation
I guess the whole locking situation and concurrency invariants will need
to be encoded in ghost state somehow --- generally, ghost state allows us
to connect concrete heap details with protocol adherence
resource algebras in Raven as an abstract way to define specifications ---
I guess they are the building blocks with which we can construct our proofs?
resource algebras as a way to constrain global behavior in a system
