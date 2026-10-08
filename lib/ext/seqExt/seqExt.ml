open Base
open Ast
open ExtApi
open Util

(** Operators on the sequences of the standard library's `Library.Seq`, after Viper's: `s
    ++ t` appends, `s[i]` is the entry at index `i`, `s[i := e]` replaces it, and `e in s`
    says whether `e` is an entry. The parser produces the core's set union, map lookup and
    update, and membership for these, which the core rejects on a sequence and offers to
    [claim_expr]. This extension claims them and type-checks them as calls of `append`,
    `index`, `update` and `contains` of the sequence's instance of `Library.Seq`, so none
    of its constructs remains after type checking. As a sequence is a value, `s[i]` is an
    expression, unlike an array entry, and `s[i] := e` assigns `s[i := e]` to the variable
    `s`. The literal `[|e1, ..., en|]` is typed as the sequence built from `singleton` and
    `append`, and `[||]` as `empty`, of the instance of the expected type, or else of the
    instance inferred from the entries. The slices `s[..n]` and `s[n..]` are `take` and
    `drop`, and `s[m..n]` is `s[..n][m..]`. *)
module SeqExt (Cont : Ext) = struct
  include Cont

  let lib_source = None

  type Expr.expr_ext +=
    | SeqOp of Expr.constr  (** a core operator, applied to a sequence *)
    | SeqLit  (** a literal, its entries the operands *)
    | SeqTake  (** `s[..n]`, the operands `s` and `n` *)
    | SeqDrop  (** `s[n..]`, the operands `s` and `n` *)

  let seq_ident = Ident.make Loc.dummy "Seq" 0

  (* [Library.Seq], or [Seq] where the library's own sources are checked as a program
     (`--nostdlib`). *)
  let is_seq_functor (qi : qual_ident) : bool =
    QualIdent.equal qi (QualIdent.from_list [ Predefs.lib_ident; seq_ident ])
    || QualIdent.equal qi (QualIdent.from_ident seq_ident)

  (* [Library.Seq], or [Seq] under `--nostdlib`. *)
  let seq_functor : qual_ident Rewriter.t =
    let open Rewriter.Syntax in
    let in_library = QualIdent.from_list [ Predefs.lib_ident; seq_ident ] in
    let+ found = Rewriter.resolve_and_find_opt in_library in
    if Option.is_some found then in_library else QualIdent.from_ident seq_ident

  (* The instance of `Library.Seq` whose sequences have type [typ], if any. The functor is
     sealed, so an instance may be known only through its sealed view. *)
  let seq_instance (typ : type_expr) : qual_ident option Rewriter.t =
    let open Rewriter.Syntax in
    match typ with
    | Type.App (Var qi, [], _) when not (List.is_empty (QualIdent.path qi)) -> (
        let inst = QualIdent.pop qi in
        let* tbl = Rewriter.get_table in
        match SymbolTbl.find_sealed_view inst tbl with
        | Some view when is_seq_functor view.sealed_functor -> Rewriter.return (Some inst)
        | _ -> (
            let+ resolved = Rewriter.resolve_and_find_opt inst in
            match resolved with
            | Some (_, symbol) when is_seq_functor (Rewriter.Symbol.orig_qid symbol) ->
                Some inst
            | _ -> None))
    | _ -> Rewriter.return None

  (* The function of `Library.Seq` that [constr] stands for, and the position of the
     sequence among the operator's operands. *)
  let function_of (constr : Expr.constr) : (string * int) option =
    match constr with
    | Union -> Some ("append", 0)
    | MapLookUp -> Some ("index", 0)
    | MapUpdate -> Some ("update", 0)
    | Elem -> Some ("contains", 1)
    | _ -> None

  (* The sequence of [entries], built with the members of the module [module_qi]. *)
  let build ~(loc : location) ~(typ : type_expr) (module_qi : qual_ident)
      (entries : expr list) : expr =
    let call name args =
      Expr.mk_app ~loc ~typ
        (Var (QualIdent.append module_qi (Ident.make loc name 0)))
        args
    in
    match entries with
    | [] -> call "empty" []
    | e :: es ->
        List.fold es ~init:(call "singleton" [ e ]) ~f:(fun acc e ->
            call "append" [ acc; call "singleton" [ e ] ])

  (* The entries of [expr], a sequence built by [build] and typed. *)
  let entries (expr : expr) : expr list option =
    let open Expr in
    let rec entries expr acc =
      match expr with
      | App (Var _, [], _) -> Some acc
      | App (Var _, [ e ], _) -> Some (e :: acc)
      | App (Var _, [ prefix; App (Var _, [ e ], _) ], _) -> entries prefix (e :: acc)
      | _ -> None
    in
    entries expr []

  (* AstDef *)

  let expr_ext_to_string (expr_ext : Expr.expr_ext) : string =
    match expr_ext with
    | SeqOp constr -> Expr.constr_to_string constr
    | SeqLit -> "[| |]"
    | SeqTake | SeqDrop -> "[..]"
    | other -> Cont.expr_ext_to_string other

  let expr_ext_is_recognized (expr_ext : Expr.expr_ext) : bool =
    match expr_ext with
    | SeqOp _ | SeqLit | SeqTake | SeqDrop -> true
    | other -> Cont.expr_ext_is_recognized other

  (* Typing *)

  let claim_expr (constr : Expr.constr) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) =
    let open Rewriter.Syntax in
    let is_seq e =
      let+ inst = seq_instance (Expr.to_type e) in
      Option.is_some inst
    in
    let* own =
      match (constr, expr_list) with
      | Union, [ e1; e2 ] ->
          (* Either operand may be a sequence whose instance is not known yet, as `[||]`. *)
          let unknown e =
            match Expr.to_type e with Type.App ((Bot | Any), _, _) -> true | _ -> false
          in
          let+ seq1 = is_seq e1 and+ seq2 = is_seq e2 in
          Option.some_if (seq1 || (seq2 && unknown e1)) (SeqOp constr, expr_list)
      | _ -> (
          match function_of constr with
          | Some (_, position) -> (
              match List.nth expr_list position with
              | Some seq ->
                  let+ seq = is_seq seq in
                  Option.some_if seq (SeqOp constr, expr_list)
              | None -> Rewriter.return None)
          | None -> Rewriter.return None)
    in
    combine_claims expr_attr.expr_loc own (Cont.claim_expr constr expr_list expr_attr)

  let type_check_expr (expr_ext : Expr.expr_ext) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) (expected_typ : type_expr)
      (functs : type_check_expr_functs) =
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in
    match expr_ext with
    | SeqOp constr -> (
        match function_of constr with
        | None -> Error.internal_error loc "SeqExt: not a sequence operator"
        | Some (name, position) -> (
            let* inst = seq_instance (Expr.to_type (List.nth_exn expr_list position)) in
            let* inst =
              match (inst, constr, expr_list) with
              | None, Union, [ _; e2 ] -> seq_instance (Expr.to_type e2)
              | _ -> Rewriter.return inst
            in
            match inst with
            | None -> Error.internal_error loc "SeqExt: not a sequence"
            | Some inst ->
                (* The operands in the order of the function's parameters: the sequence
                   first. *)
                let args =
                  match constr with Elem -> List.rev expr_list | _ -> expr_list
                in
                let fn = QualIdent.append inst (Ident.make loc name 0) in
                functs.process_expr
                  (Expr.mk_app ~loc ~typ:Type.any (Var fn) args)
                  expected_typ))
    | SeqTake | SeqDrop -> (
        let* seq, n =
          match expr_list with
          | [ seq; n ] -> Rewriter.return (seq, n)
          | _ -> Error.internal_error loc "SeqExt: wrong number of operands"
        in
        let* seq = functs.process_expr seq Type.any in
        let* inst = seq_instance (Expr.to_type seq) in
        match inst with
        | None -> Error.type_error (Expr.to_loc seq) "Only a sequence can be sliced"
        | Some inst ->
            let name = match expr_ext with SeqTake -> "take" | _ -> "drop" in
            let fn = QualIdent.append inst (Ident.make loc name 0) in
            functs.process_expr
              (Expr.mk_app ~loc ~typ:Type.any (Var fn) [ seq; n ])
              expected_typ)
    | SeqLit -> (
        (* Typed as the members of the instance of the expected type, if it is a
           sequence type, as instances are generative. Otherwise, as the members of the
           uninstantiated functor, whose instance is inferred from the entries. The
           literal stays until after type checking, which may type it again against
           another expected type. *)
        let* expected_inst = seq_instance expected_typ in
        let* module_qi =
          match expected_inst with
          | Some inst -> Rewriter.return inst
          | None -> seq_functor
        in
        let* typed =
          functs.process_expr (build ~loc ~typ:Type.any module_qi expr_list) expected_typ
        in
        match entries typed with
        | Some entries ->
            let typ = Expr.to_type typed in
            functs.check_and_set
              (App (ExprExt SeqLit, entries, expr_attr))
              typ typ expected_typ
        | None -> Error.internal_error loc "SeqExt: unexpected form of a typed literal")
    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ functs

  (* Rewrites *)

  let rewrite_expr_ext (expr_ext : Expr.expr_ext) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) : expr Rewriter.t =
    let open Rewriter.Syntax in
    match expr_ext with
    | SeqLit -> (
        let loc = expr_attr.expr_loc in
        let* inst = seq_instance expr_attr.expr_type in
        match inst with
        | Some inst ->
            Rewriter.return (build ~loc ~typ:expr_attr.expr_type inst expr_list)
        | None -> Error.internal_error loc "SeqExt: a literal that is not a sequence")
    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr
end
