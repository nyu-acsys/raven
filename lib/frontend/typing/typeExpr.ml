(** Type checking of type expressions. *)

open Base
open Ast
open Util
open TypingMonad
open TypingErrors

let rec check (tp_expr : type_expr) : type_expr t =
  let open Type in
  let open Rewriter.Syntax in
  match tp_expr with
  | App (Var qual_ident, [], tp_attr) -> (
      let* fully_qualified_qual_ident, symbol = Rewriter.resolve_and_find qual_ident in
      match Rewriter.Symbol.orig_symbol symbol with
      | TypeDef _tp_alias ->
          Rewriter.return (App (Var fully_qualified_qual_ident, [], tp_attr))
      | ModDef m -> (
          match m.mod_decl.mod_decl_rep with
          | None ->
              Error.type_error tp_attr.type_loc
                ("Module "
                ^ QualIdent.to_string qual_ident
                ^ " does not have a rep type. It cannot be used in a context expecting a \
                   type")
          | Some rep_ident -> (
              let rep_fully_qualified_qual_ident =
                QualIdent.append fully_qualified_qual_ident rep_ident
              in
              (* A functor `M` used bare as a type: its rep type resolves only inside
                 `M`, so report the misuse here rather than an unknown `M.T` inside
                 `M`'s body. *)
              let* rep_resolves =
                Rewriter.resolve_and_find_opt rep_fully_qualified_qual_ident
              in
              match rep_resolves with
              | Some _ ->
                  Rewriter.return (App (Var rep_fully_qualified_qual_ident, [], tp_attr))
              | None -> (
                  let* generic_functor =
                    lift (ProgUtils.resolve_generic_functor qual_ident)
                  in
                  match generic_functor with
                  | Some (_, gm) ->
                      arg_mismatch_error "Module" tp_attr.type_loc (Type.Var qual_ident)
                        (List.length gm.mod_decl.mod_decl_formals)
                  | None ->
                      Rewriter.return
                        (App (Var rep_fully_qualified_qual_ident, [], tp_attr)))))
      | ModInst _ -> unexpected_functor_error tp_attr.type_loc
      | _ -> Error.type_error tp_attr.type_loc "Expected type identifier")
  | App (Var qual_ident, (_ :: _ as tp_args), tp_attr) -> (
      (* `M[T1,...,Tn]`: if `M` is a functor with rep-typed formals, instantiate it
         implicitly (see [ProgUtils.instantiate_type_functor]) and resolve to the
         instance's rep type. *)
      let* generic_functor = lift (ProgUtils.resolve_generic_functor qual_ident) in
      match generic_functor with
      | None ->
          (* [resolve_generic_functor] also returns [None] if [qual_ident] does not
             resolve; report that as an unknown identifier rather than as a misuse of a
             functor. *)
          let* _ = Rewriter.resolve_and_find qual_ident in
          unexpected_functor_error tp_attr.type_loc
      | Some (fully_qualified_qual_ident, m) -> (
          if
            not
              (Int.equal (List.length tp_args) (List.length m.mod_decl.mod_decl_formals))
          then
            arg_mismatch_error "Module" tp_attr.type_loc (Type.Var qual_ident)
              (List.length m.mod_decl.mod_decl_formals)
          else
            let* tp_args = Rewriter.List.map tp_args ~f:check in
            let* inst_qual_ident =
              lift
                (ProgUtils.instantiate_type_functor ~loc:tp_attr.type_loc
                   ~f:!Rewriter.check_symbol_ref
                   ~functor_qual_ident:fully_qualified_qual_ident
                   ~functor_mod_decl:m.mod_decl tp_args)
            in
            match m.mod_decl.mod_decl_rep with
            | None ->
                Error.type_error tp_attr.type_loc
                  ("Module "
                  ^ QualIdent.to_string qual_ident
                  ^ " does not have a rep type. It cannot be used in a context expecting \
                     a type")
            | Some rep_ident ->
                Rewriter.return
                  (App (Var (QualIdent.append inst_qual_ident rep_ident), [], tp_attr))))
  | App ((Fld as constr), tp_list, tp_attr) -> (
      match tp_list with
      | [ tp_arg ] ->
          let+ tp_arg' = check tp_arg in
          App (constr, [ tp_arg' ], tp_attr)
      | _ -> arg_mismatch_error "Constructor" (Type.to_loc tp_expr) constr 1)
  | App (Map, tp_list, tp_attr) -> (
      match tp_list with
      | [ tp1; tp2 ] ->
          let+ tp1 = check tp1 and+ tp2 = check tp2 in
          App (Map, [ tp1; tp2 ], tp_attr)
      | _ -> arg_mismatch_error "Type" (Type.to_loc tp_expr) Map 2)
  | App ((FinSet as constr), tp_list, tp_attr) -> (
      match tp_list with
      | [ tp_arg ] ->
          let+ tp_arg' = check tp_arg in
          App (constr, [ tp_arg' ], tp_attr)
      | _ -> arg_mismatch_error "Type" (Type.to_loc tp_expr) FinSet 1)
  | App (Data _, _tp_list, _tp_attr) ->
      (* The parser should prevent this from happening. *)
      Error.internal_error (Type.to_loc tp_expr)
        "Data types can only be defined as new types, not used inline"
  | App (Prod, tp_list, tp_attr) ->
      let+ tp_list = Rewriter.List.map tp_list ~f:check in
      App (Prod, tp_list, tp_attr)
  | App (AtomicToken qid, [], tp_attr) ->
      let+ qid = Rewriter.resolve qid in
      App (AtomicToken qid, [], tp_attr)
  | App (TypeExt type_ext, tp_args, tp_attr) ->
      let* ext_hooks = Rewriter.current_ext_hooks in
      (* Extensions work in [Rewriter.t], so pass them a wrapper of [check]
         and lift the result. *)
      lift
        (ext_hooks.type_check_type_expr type_ext tp_args tp_attr
           { process_type_expr = (fun tp -> run_typing (check tp)) })
  | App (constr, [], tp_attr) -> Rewriter.return @@ App (constr, [], tp_attr)
  | App (constr, _tp_list, _tp_attr) ->
      (* The parser should prevent this from happening. *)
      Error.internal_error (Type.to_loc tp_expr)
        (Type.to_name constr ^ " types don't take arguments")

let rec expand_type_expr (tp_expr : type_expr) : Type.t t =
  expand_type_expr_visiting (Set.empty (module QualIdent)) tp_expr

(* [visiting] holds the aliases being expanded, to reject cyclic ones. *)
and expand_type_expr_visiting (visiting : QualIdentSet.t) (tp_expr : type_expr) : Type.t t
    =
  let open Rewriter.Syntax in
  let expand_type_expr = expand_type_expr_visiting visiting in
  match tp_expr with
  | App (constr, tp_expr_list, tp_attr) -> (
      match (constr, tp_expr_list) with
      | Var qual_iden, [] -> (
          (* Var types with args not supported. Polymorphic types need to be instantiated as separate modules before using. *)
          let* qual_ident, symbol = Rewriter.resolve_and_find qual_iden in
          let* qual_ident_def =
            Rewriter.Symbol.reify_type_def (Type.to_loc tp_expr) symbol
          in
          match qual_ident_def with
          | None ->
              Rewriter.return
              @@ (Type.App (Var qual_ident, tp_expr_list, tp_attr)
                 |> Type.set_ghost_to tp_expr)
          | Some (App (Data _, _, _)) ->
              Rewriter.return
              @@ (Type.App (Var qual_ident, tp_expr_list, tp_attr)
                 |> Type.set_ghost_to tp_expr)
          | Some tp_expr1 ->
              if Set.mem visiting qual_ident then
                let loc =
                  match symbol with
                  | _, Module.TypeDef type_def, _ -> Ident.to_loc type_def.type_def_name
                  | _ -> Type.to_loc tp_expr
                in
                Error.type_error loc
                  (Printf.sprintf
                     !"The definition of type %{Ident} refers to itself. Only data types \
                       can be recursive"
                     (QualIdent.unqualify qual_ident))
              else
                let+ exp_typ =
                  expand_type_expr_visiting (Set.add visiting qual_ident) tp_expr1
                in
                exp_typ |> Type.set_ghost_to tp_expr)
      | Var _, _ :: _ ->
          (* `M[T1,...,Tn]` can reach here unnormalized through a self-referential lookup,
             so process it first. *)
          let* tp_expr = check tp_expr in
          expand_type_expr tp_expr
      | AtomicToken callable_qid, [] ->
          let+ callable_qid = Rewriter.resolve callable_qid in
          Type.App (AtomicToken callable_qid, [], tp_attr) |> Type.set_ghost_to tp_expr
      | AtomicToken _, _ -> unexpected_functor_error tp_attr.type_loc
      | _ ->
          let+ expanded_tp_expr_list =
            Rewriter.List.map tp_expr_list ~f:expand_type_expr
          in
          Type.App (constr, expanded_tp_expr_list, tp_attr) |> Type.set_ghost_to tp_expr)

let check_var_decl (var_decl : var_decl) : var_decl t =
  let open Rewriter.Syntax in
  let* var_type = check var_decl.var_type in
  let+ var_type = expand_type_expr var_type in
  { var_decl with var_type }
