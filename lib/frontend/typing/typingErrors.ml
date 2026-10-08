(** Errors reported by type checking. *)

open Base
open Ast
open Util

let type_mismatch_error loc exp_ty fnd_ty =
  Error.type_error loc
    (Printf.sprintf
       !"Expected an expression of type\n\
        \  %{Type}\n\
         but found an expression of type\n\
        \  %{Type}"
       exp_ty fnd_ty)

(** Best-effort diagnostic for the common case behind a confusing "expected X but found Y"
    where X and Y turn out to be two different names for the same underlying module: their
    canonical declaration site ([SymbolTbl.resolve_and_find]'s first, alias-independent
    component) and instantiation-argument substitution agree, even though the identifiers
    used to reach them differ. Purely read-only -- never changes what type-checks, only
    what the error, if any, explains. *)
let explain_module_identity_mismatch (tbl : SymbolTbl.t) (exp_ty : type_expr)
    (fnd_ty : type_expr) : string option =
  match (exp_ty, fnd_ty) with
  | App (Var exp_qi, [], _), App (Var fnd_qi, [], _) when QualIdent.(exp_qi <> fnd_qi)
    -> (
      match
        (SymbolTbl.resolve_and_find exp_qi tbl, SymbolTbl.resolve_and_find fnd_qi tbl)
      with
      | ( Some (exp_alias, _, _, (_, _, exp_subst)),
          Some (fnd_alias, _, _, (_, _, fnd_subst)) )
        when QualIdent.(exp_alias = fnd_alias) -> (
          (* [exp_alias]/[fnd_alias] name the physical declaration site both types
             trace back to (e.g. a rep type's own qualified name). Its owning
             module tells us whether any *real* type arguments could be
             involved: if it has no formals, every difference between
             [exp_subst] and [fnd_subst] is a structural rename picked up while
             chasing through aliases, not a semantic one, and the two types are
             genuinely the same. If it does have formals, we only know that for
             sure when both sides bind every formal to the same argument. *)
          let owning_module = QualIdent.pop exp_alias in
          match Map.find tbl.tbl_symbols owning_module with
          | Some (Module.ModDef { mod_decl = { mod_decl_formals = []; _ }; _ }) ->
              Some
                (Printf.sprintf
                   !"%{QualIdent} and %{QualIdent} are two different names for the same \
                     module (%{QualIdent}). Raven does not currently recognize their \
                     members as the same type -- use one name consistently wherever this \
                     type must match"
                   exp_qi fnd_qi owning_module)
          | Some (Module.ModDef { mod_decl = { mod_decl_formals; _ }; _ })
            when not (List.is_empty mod_decl_formals) ->
              let binding subst (formal : Module.module_inst) =
                let key = QualIdent.append owning_module formal.mod_inst_name in
                List.Assoc.find subst key ~equal:QualIdent.equal
              in
              let same_args =
                List.for_all mod_decl_formals ~f:(fun formal ->
                    match (binding exp_subst formal, binding fnd_subst formal) with
                    | Some a, Some b -> List.equal Ident.equal a b
                    | None, None -> true
                    | _ -> false)
              in
              if same_args then
                Some
                  (Printf.sprintf
                     !"%{QualIdent} and %{QualIdent} come from two separate \
                       instantiations of %{QualIdent} with the same arguments. Module \
                       instantiation is generative: each instantiation site produces its \
                       own distinct type, even when the arguments are identical. Bind a \
                       single instantiation explicitly and reuse it from both places, \
                       e.g. `module Shared = %{QualIdent}[...]`"
                     exp_qi fnd_qi owning_module owning_module)
              else None
          | _ -> None)
      | _ -> None)
  | _ -> None

(** Like [type_mismatch_error], but first tries [explain_module_identity_mismatch] and
    appends its explanation, if any. *)
let type_mismatch_error_diagnosed tbl loc exp_ty fnd_ty =
  match explain_module_identity_mismatch tbl exp_ty fnd_ty with
  | None -> type_mismatch_error loc exp_ty fnd_ty
  | Some explanation ->
      Error.type_error loc
        (Printf.sprintf
           !"Expected an expression of type\n\
            \  %{Type}\n\
             but found an expression of type\n\
            \  %{Type}.\n\n\
             %s"
           exp_ty fnd_ty explanation)

let number_to_string kind d =
  if d = 1 then Printf.sprintf "one %s" kind else Printf.sprintf "%d %ss" d kind

let tuple_arg_mismatch_error loc expected =
  Error.type_error loc
    (Printf.sprintf "Expected tuple with %s" (number_to_string "component" expected))

let arg_mismatch_error kind loc typ_constr expected =
  Error.type_error loc
    (Printf.sprintf "%s %s expects %s" kind (Type.to_name typ_constr)
       (number_to_string "argument" expected))

let param_mismatch_error kind loc id expected =
  Error.type_error loc
    (Printf.sprintf "%s %s expects %s" kind id (number_to_string "parameter" expected))

let unexpected_functor_error loc =
  Error.type_error loc
    "A functor can only be instantiated as the definition of a module (e.g. 'module M = \
     F[...]'), not used as a type or value here"
