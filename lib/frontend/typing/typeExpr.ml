(** Type checking of type expressions. *)

open Base
open Ast
open Util
open TypingMonad
open TypingErrors

let rec process_type_expr (tp_expr : type_expr) : type_expr t =
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
              Logs.debug (fun mm -> mm "%a" Ident.pr m.mod_decl.mod_decl_name);
              Error.type_error tp_attr.type_loc
                ("Module "
                ^ QualIdent.to_string qual_ident
                ^ " does not have a rep type. It cannot be used in a context expecting a \
                   type")
          | Some rep_ident -> (
              let rep_fully_qualified_qual_ident =
                QualIdent.append fully_qualified_qual_ident rep_ident
              in
              (* `M` used bare, with no `[...]` at all, where `M` is really a
                   functor: the rep type's own definition is only reachable
                   from inside `M` (or one of its instances), so resolving it
                   from here fails. Left as-is, that failure surfaces as
                   "Unknown identifier M.T" pointed at T's declaration inside
                   M's body -- confusing, and for a library functor, pointed
                   into a file the user never opened. Diagnose it here
                   instead, at the actual use site, when that's indeed what's
                   going on (this can't fire for a legitimate self-reference
                   from inside M's own body, since the rep type resolves fine
                   from there). *)
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
      (* `M[T1,...,Tn]`: if `M` is a functor with rep-typed formals, implicitly
           instantiate it (see `ProgUtils.instantiate_type_functor`) and resolve to the
           instantiation's rep type. Anything else is still rejected, as before. *)
      let* generic_functor = lift (ProgUtils.resolve_generic_functor qual_ident) in
      match generic_functor with
      | None ->
          (* `resolve_generic_functor` also returns `None` when `qual_ident` fails to
               resolve at all, which is a different problem from "resolves, but isn't
               eligible for `M[T1,...,Tn]` sugar" -- surface that as the usual unknown-
               identifier error instead of the functor-usage restriction below, which
               would otherwise misleadingly suggest `qual_ident` is a functor. *)
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
            let* tp_args = Rewriter.List.map tp_args ~f:process_type_expr in
            let* inst_qual_ident =
              lift
                (ProgUtils.instantiate_type_functor ~loc:tp_attr.type_loc
                   ~f:!Rewriter.process_symbol_ref
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
          let+ tp_arg' = process_type_expr tp_arg in
          App (constr, [ tp_arg' ], tp_attr)
      | _ -> arg_mismatch_error "Constructor" (Type.to_loc tp_expr) constr 1)
  | App (Map, tp_list, tp_attr) -> (
      match tp_list with
      | [ tp1; tp2 ] ->
          let+ tp1 = process_type_expr tp1 and+ tp2 = process_type_expr tp2 in
          App (Map, [ tp1; tp2 ], tp_attr)
      | _ -> arg_mismatch_error "Type" (Type.to_loc tp_expr) Map 2)
  | App ((FinSet as constr), tp_list, tp_attr) -> (
      match tp_list with
      | [ tp_arg ] ->
          let+ tp_arg' = process_type_expr tp_arg in
          App (constr, [ tp_arg' ], tp_attr)
      | _ -> arg_mismatch_error "Type" (Type.to_loc tp_expr) FinSet 1)
  | App (Data _, _tp_list, _tp_attr) ->
      (* The parser should prevent this from happening. *)
      Error.internal_error (Type.to_loc tp_expr)
        "Data types can only be defined as new types, not used inline"
  | App (Prod, tp_list, tp_attr) ->
      let+ tp_list = Rewriter.List.map tp_list ~f:process_type_expr in
      App (Prod, tp_list, tp_attr)
  | App (AtomicToken qid, [], tp_attr) ->
      let+ qid = Rewriter.resolve qid in
      App (AtomicToken qid, [], tp_attr)
  | App (TypeExt type_ext, tp_args, tp_attr) ->
      let* ext_hooks = Rewriter.current_ext_hooks in
      (* ext_hooks is a fixed, unit-state interface extensions are written against --
         see [Typing.t]'s doc comment -- so bridge both directions here: hand it a
         unit-state wrapper of our own (recursive) [process_type_expr], and [lift] its
         unit-state result back into [t]. *)
      lift
        (ext_hooks.type_check_type_expr type_ext tp_args tp_attr
           { process_type_expr = (fun tp -> run_typing (process_type_expr tp)) })
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
          (* `M[T1,...,Tn]` can reach here un-normalized via a self-referential
               lookup (e.g. a recursive call reading back its own declared type).
               Route through process_type_expr first, then keep expanding. *)
          let* tp_expr = process_type_expr tp_expr in
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

let process_var_decl (var_decl : var_decl) : var_decl t =
  let open Rewriter.Syntax in
  let* var_type = process_type_expr var_decl.var_type in
  let+ var_type = expand_type_expr var_type in
  { var_decl with var_type }
