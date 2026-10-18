(** Fingerprints of proof obligations: digests of everything the check of an obligation
    can use, so that a check whose fingerprint is unchanged would give the same result. *)

open Base
open Ast
module Graph = Dependencies.Graph

let digest text = Stdlib.Digest.(to_hex (string text))

(** The obligations among [placed] (as [Dependencies.analyze] places them), each with its
    fingerprint. It covers the symbols the obligation uses by [deps], with the auto lemmas
    about them by [auto], and the auto lemmas in the obligation's solver scope that
    mention a function, predicate or variable covered, with what they use, until no more
    are. Since the solver instantiates quantifiers only through their triggers, these are
    the facts in scope that a proof can use. Of the other procedures and lemmas, only the
    contracts count, since a proof uses no more of them. Each symbol counts by
    [symbol_text], so that only its lowered form matters, together with [run_key], for
    what the run fixes. *)
let compute ~(run_key : string) ~(symbol_text : Module.symbol -> string)
    ~(reify : QualIdent.t -> Module.symbol) ~(deps : Graph.t) ~(auto : Graph.t)
    (placed : (Ident.t list * QualIdent.t list) list) : (QualIdent.t * string) list =
  let symbols = Hashtbl.create (module QualIdent) in
  let symbol q = Hashtbl.find_or_add symbols q ~default:(fun () -> reify q) in
  (* What [q] contributes when it is not the obligation. *)
  let used q =
    match symbol q with
    | CallDef ({ call_def = ProcDef _; _ } as c) ->
        Module.CallDef { c with call_def = ProcDef { proc_body = None } }
    | sym -> sym
  in
  let digests = Hashtbl.create (module QualIdent) in
  let used_digest q =
    Hashtbl.find_or_add digests q ~default:(fun () -> digest (symbol_text (used q)))
  in
  let succs q =
    let uses =
      match used q with
      | CallDef ({ call_def = ProcDef _; _ } as c) -> Callable.symbols c
      | _ -> Graph.succs deps q
    in
    Set.union uses (Graph.succs auto q)
  in
  (* [roots], the symbols they use, and the auto lemmas about them. *)
  let reachable roots =
    let rec go seen = function
      | [] -> seen
      | q :: todo ->
          let next = Set.diff (succs q) seen in
          go (Set.union seen next) (Set.fold next ~init:todo ~f:(fun todo q -> q :: todo))
    in
    go roots (Set.to_list roots)
  in
  let is_auto_lemma q =
    match symbol q with CallDef c -> Dependencies.is_auto_lemma c | _ -> false
  in
  let mentions q =
    match used q with
    | CallDef c ->
        Set.filter (Callable.symbols c) ~f:(fun q ->
            match symbol q with TypeDef _ -> false | _ -> true)
    | _ -> Graph.empty_vertex_set
  in
  let placed = List.mapi placed ~f:(fun i (path, scc) -> (i, path, scc)) in
  (* What is declared when the symbols placed [i]th, at [path], are checked: what enclosing
     scopes hold, and what this scope holds up to them. *)
  let in_scope ~i ~path (j, path', _) =
    if List.equal Ident.equal path path' then j <= i
    else List.is_prefix path ~prefix:path' ~equal:Ident.equal
  in
  let rec cover covered lemmas =
    let lemmas = List.filter lemmas ~f:(fun l -> not (Set.mem covered l)) in
    match
      List.filter lemmas ~f:(fun l -> not (Set.are_disjoint (mentions l) covered))
    with
    | [] -> covered
    | used ->
        cover (Set.union covered (reachable (Set.of_list (module QualIdent) used))) lemmas
  in
  let fingerprint ~i ~path q =
    let lemmas =
      List.filter placed ~f:(in_scope ~i ~path)
      |> List.concat_map ~f:(fun (_, _, scc) -> List.filter scc ~f:is_auto_lemma)
    in
    let own = Set.union (Graph.succs deps q) (Graph.succs auto q) in
    let covered = Set.remove (cover (Set.add (reachable own) q) lemmas) q in
    digest
      (String.concat ~sep:"\n"
         (run_key
         :: digest (symbol_text (symbol q))
         :: List.map (Set.to_list covered) ~f:(fun q ->
             QualIdent.to_string q ^ " " ^ used_digest q)))
  in
  List.concat_map placed ~f:(fun (i, path, scc) ->
      List.filter_map scc ~f:(fun q ->
          match symbol q with
          | CallDef { call_def = ProcDef { proc_body = Some _ }; call_decl }
            when not (is_free call_decl.call_decl_status) ->
              Some (q, fingerprint ~i ~path q)
          | _ -> None))
