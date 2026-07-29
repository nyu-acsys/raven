open Base

(** Canonically represents a set of elements *modulo subsumption* under a
    caller-supplied partial order on the element type: the set is stored
    as a sorted, deduplicated list of its own *maximal* elements, an
    antichain (no two stored elements are comparable) standing for the
    down-closed set (order ideal) of everything at or below them. Each
    stored element represents itself and everything the order places
    beneath it; an element that's already covered by some other, distinct
    element in the set contributes nothing and is dropped.

    [Ord.meet] supplies the order: [meet a b = Some m] means [m] is the
    greatest lower bound of [a] and [b] (their down-sets' intersection);
    [None] means [a] and [b] are unrelated/incomparable, and their true
    meet is the bottom (empty) element, which this representation never
    stores explicitly. [canon] drops any element whose meet with some
    distinct other element in the set is itself (that other element
    already covers it, so it's redundant); [union] is the antichain of the
    pointwise union of two down-sets; [inter] is the antichain of their
    pointwise intersection -- the meet of every pair drawn one from each
    side, discarding pairs with no meet.

    For an element type with no meaningful subsumption between distinct
    elements, [let meet a b = if compare a b = 0 then Some a else None]
    recovers an ordinary flat set: nothing is ever subsumed by anything but
    itself, so [canon] only dedups, and [inter] degenerates to plain
    element-wise intersection.

    Also useful, independent of the above, as a substitute for [Base.Set]
    when the element type has a [compare] but no (real) [sexp_of_t]:
    [Base.Set] needs a [Comparator.S], which requires both, and
    [sexp_of_t] fundamentally can't be derived for a type built on an
    *extensible* variant (a type with a [.. ] case, e.g. an AST node type
    with a plugin/extension-hook constructor) -- ppx_sexp_conv can't
    generate a serializer for a variant whose full set of cases isn't known
    at the point of derivation, since other files may still add more cases
    later. [compare] can still be written by hand for such a type (e.g. by
    tag-comparing [Obj.repr]), but [sexp_of_t] can't be, the same way, so
    [Comparator.Make] is a dead end without a throwaway hand-written
    [sexp_of_t] used for nothing but diagnostics. Don't reach for this as a
    general substitute for [Base.Set] beyond that, though: it re-sorts on
    every [union] (O(n log n) per call, not O(log n) amortized like a
    balanced-tree set), which is fine for small, infrequently-updated sets,
    not for anything performance-sensitive. *)

module Make (Ord : sig
  type t

  val compare : t -> t -> int

  (** The meet (greatest lower bound) of two elements under whatever
      partial order this element type represents, if one exists -- [None]
      means the two elements are unrelated/incomparable. *)
  val meet : t -> t -> t option
end) : sig
  type elt = Ord.t
  type t = elt list

  val empty : t
  val compare_elt : elt -> elt -> int

  (** Sorts, deduplicates, and drops any element subsumed by a distinct
      other element in the set (i.e. whose meet with that other element is
      itself) -- the canonical antichain of *maximal* elements this list
      denotes under [Ord.meet]'s partial order. *)
  val canon : t -> t

  (** Set equality: order- and duplicate-insensitive (canonicalizes both
      sides first). *)
  val equal : t -> t -> bool

  val union : t -> t -> t
  val union_list : t list -> t

  (** Set intersection, partial-order-aware: the meet of every pair drawn
      one element from each side (pairs with no meet contribute nothing),
      canonicalized. E.g. an element covering everything, met with a more
      specific one, correctly yields the more specific one -- the largest
      thing guaranteed by *both* sides -- rather than the empty set a
      plain element-wise intersection would (incorrectly) produce, since
      neither side literally contains the other's exact element.
      Degenerates to ordinary element-wise intersection when [Ord.meet]
      only ever relates identical elements. *)
  val inter : t -> t -> t
end = struct
  type elt = Ord.t
  type t = elt list

  let empty = []
  let compare_elt = Ord.compare

  (* [a] contributes nothing beyond some distinct [b] already in the set --
     i.e. [a] is already covered by [b]. *)
  let is_subsumed_by (a : elt) (b : elt) : bool =
    Ord.compare a b <> 0
    &&
    match Ord.meet a b with
    | Some m -> Ord.compare m a = 0
    | None -> false

  let canon (s : t) : t =
    let deduped = List.dedup_and_sort s ~compare:Ord.compare in
    List.filter deduped ~f:(fun a ->
        not (List.exists deduped ~f:(fun b -> is_subsumed_by a b)))

  let equal (s1 : t) (s2 : t) : bool =
    List.equal (fun e1 e2 -> Ord.compare e1 e2 = 0) (canon s1) (canon s2)

  let union (s1 : t) (s2 : t) : t = canon (s1 @ s2)
  let union_list (ss : t list) : t = canon (List.concat ss)

  let inter (s1 : t) (s2 : t) : t =
    let meets =
      List.concat_map s1 ~f:(fun a -> List.filter_map s2 ~f:(fun b -> Ord.meet a b))
    in
    canon meets
end
