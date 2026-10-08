open Base
open Ast
open ExtApi
open Util

(** The set operators `++`, `**`, `--`, `subseteq` and `choose` as the operations of the
    standard library's [Library.Sets]. The core gives them no meaning: it offers them to
    [claim_expr] with their operands typed, and this extension claims them on sets. It
    types them, including whether a result is a finite set (`FinSet`), and lowers them to
    calls of the functions of the instance of [Library.Sets] for the sets' element type.
    They are lowered only after type checking, which may type them again: a call is typed
    by its function's signature, which does not say when a result is finite. *)
module SetExt (Cont : Ext) = struct
  include Cont

  let lib_source = None

  type Expr.expr_ext +=
    | SetOp of Expr.constr  (** a set operator, operands as for the core's *)

  let sets_ident = Ident.make Loc.dummy "Sets" 0

  (* [Library.Sets], or [Sets] where the library's own sources are checked as a program
     (`--nostdlib`). *)
  let sets_qual_ident : qual_ident Rewriter.t =
    let open Rewriter.Syntax in
    let in_library = QualIdent.from_list [ Predefs.lib_ident; sets_ident ] in
    let+ found = Rewriter.resolve_and_find_opt in_library in
    if Option.is_some found then in_library else QualIdent.from_ident sets_ident

  (* The function of [Library.Sets] that [constr] stands for. *)
  let function_name (constr : Expr.constr) : string =
    match constr with
    | Union -> "union"
    | Inter -> "inter"
    | Diff -> "diff"
    | Subseteq -> "subset"
    | _ -> "choose"

  (* AstDef *)

  let expr_ext_to_string (expr_ext : Expr.expr_ext) : string =
    match expr_ext with
    | SetOp constr -> Expr.constr_to_string constr
    | other -> Cont.expr_ext_to_string other

  let expr_ext_is_recognized (expr_ext : Expr.expr_ext) : bool =
    match expr_ext with SetOp _ -> true | other -> Cont.expr_ext_is_recognized other

  (* Typing *)

  let claim_expr (constr : Expr.constr) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) =
    (* A set, or an operand whose type is not known yet. *)
    let may_be_set e =
      match Expr.to_type e with
      | Type.App ((Bot | Any), _, _) -> true
      | typ -> Type.is_set typ
    in
    let is_set e = Type.is_set (Expr.to_type e) in
    let own =
      match (constr, expr_list) with
      | (Union | Inter | Diff | Subseteq), [ e1; e2 ]
        when may_be_set e1 && may_be_set e2 && (is_set e1 || is_set e2) ->
          Some (SetOp constr, expr_list)
      | Choose, [ e ] when is_set e -> Some (SetOp constr, expr_list)
      | _ -> None
    in
    combine_claims expr_attr.expr_loc own (Cont.claim_expr constr expr_list expr_attr)

  (* The element type of the sets [args] of a set operator. *)
  let element_type (args : expr list) : type_expr =
    Type.set_elem (List.reduce_exn (List.map args ~f:Expr.to_type) ~f:Type.join)

  (* The call of [name] of the instance of [Library.Sets] for [elem], of type [typ]. *)
  let call ~(loc : location) (elem : type_expr) (name : string) (args : expr list)
      (typ : type_expr) : expr Rewriter.t =
    let open Rewriter.Syntax in
    if Type.contains_bot elem || Type.is_any elem then
      Error.type_error loc "Cannot determine the element type of this set"
    else
      let* sets_qual_ident = sets_qual_ident in
      let* sets = Rewriter.find_and_reify_module sets_qual_ident in
      let+ instance =
        ProgUtils.instantiate_type_functor ~loc ~f:!Rewriter.check_symbol_ref
          ~functor_qual_ident:sets_qual_ident ~functor_mod_decl:sets.mod_decl
          [ Type.set_ghost false elem ]
      in
      Expr.mk_app ~loc ~typ (Var (QualIdent.append instance (Ident.make loc name 0))) args

  let type_check_expr (expr_ext : Expr.expr_ext) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) (expected_typ : type_expr)
      (functs : type_check_expr_functs) =
    let open Rewriter.Syntax in
    let loc = expr_attr.expr_loc in
    let ghost ty = Type.set_ghost_to expected_typ ty in
    (* An operand whose element type is still unknown, such as `{||}`, is typed again
       against the sets of [elem]. Others keep their type, which may be finite. *)
    let settle elem (e : expr) =
      if Type.contains_bot (Expr.to_type e) then
        functs.process_expr e (ghost (Type.set_typed elem))
      else Rewriter.return e
    in
    match (expr_ext, expr_list) with
    | SetOp constr, [ e1; e2 ] ->
        let elem =
          let joined = Type.join (Expr.to_type e1) (Expr.to_type e2) in
          if Type.contains_bot joined && Type.is_set expected_typ then
            Type.set_elem expected_typ
          else Type.set_elem joined
        in
        let* e1 = settle elem e1 and* e2 = settle elem e2 in
        let typ1 = Expr.to_type e1 and typ2 = Expr.to_type e2 in
        let result =
          match constr with
          | Union -> Type.join typ1 typ2
          | Inter -> Type.meet typ1 typ2
          | Diff ->
              (* A difference is no larger than its first operand. *)
              (if Type.is_finset typ1 then Type.finset_typed else Type.set_typed)
                (Type.set_elem typ1)
          | _ -> Type.bool
        in
        let result = ghost result in
        functs.check_and_set
          (App (ExprExt expr_ext, [ e1; e2 ], expr_attr))
          result result expected_typ
    | SetOp _, [ e ] ->
        let* e = settle (Type.set_elem (Expr.to_type e)) e in
        let elem = ghost (Type.set_elem (Expr.to_type e)) in
        functs.check_and_set
          (App (ExprExt expr_ext, [ e ], expr_attr))
          elem elem expected_typ
    | SetOp _, _ -> Error.internal_error loc "SetExt: wrong number of operands"
    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ functs

  (* Rewrites *)

  (* A finite result is computed by the function whose signature says so; an intersection
     whose first operand is not finite has its operands swapped for that. *)
  let rewrite_expr_ext (expr_ext : Expr.expr_ext) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) : expr Rewriter.t =
    match expr_ext with
    | SetOp constr ->
        let name, args =
          match (constr, expr_list) with
          | (Union | Inter | Diff), [ e1; e2 ] when Type.is_finset expr_attr.expr_type ->
              let args =
                if Type.is_finset (Expr.to_type e1) then [ e1; e2 ] else [ e2; e1 ]
              in
              ("fin_" ^ function_name constr, args)
          | _ -> (function_name constr, expr_list)
        in
        call ~loc:expr_attr.expr_loc (element_type expr_list) name args
          expr_attr.expr_type
    | _ -> Cont.rewrite_expr_ext expr_ext expr_list expr_attr
end
