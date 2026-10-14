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

(** Explains a mismatch between two types that are different names for the same module, if
    they are. It changes only the error message. *)
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
          (* Both types trace back to the declaration [exp_alias]. If its module has no
             formals, the substitutions differ only by renamings along aliases;
             otherwise, the types are the same only if both bind every formal to the
             same argument. *)
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

(* Callables *)

let opens_on_pure_callable_error loc name =
  Error.type_error loc
    (Printf.sprintf
       !"%{Ident} may not have an opens clause; only procedures and lemmas can"
       name)

let opens_not_invariant_error loc kind qual_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Expected an invariant in this opens clause, but found %s %{QualIdent}"
       kind qual_ident)

let opens_arity_error loc inv_name ~expected ~given =
  Error.type_error loc
    (Printf.sprintf
       !"Invariant %{Ident} takes %d argument(s), but %d are given here; write `_` for \
         an argument left unspecified"
       inv_name expected given)

let opens_non_formal_error loc ident ~is_atomic =
  Error.type_error loc
    (Printf.sprintf
       !"%{String} cannot be used in an opens clause; arguments may only mention the \
         callable's formals%s"
       (Ident.name ident)
       (if is_atomic then ", other than implicit ones" else ""))

let mixfix_not_function_error loc =
  Error.type_error loc "A mixfix operator must be declared as a function"

let mixfix_parameters_error loc name holes =
  Error.type_error loc
    (Printf.sprintf
       "Mixfix operator %s requires %d explicit parameters, followed only by implicit \
        ghost parameters"
       (Ident.name name) holes)

let implicit_pred_input_error loc =
  Error.type_error loc "Implicit predicate parameters must follow the ';' delimiter"

let loc_param_not_field_error loc callable_name kind field =
  Error.type_error loc
    (Printf.sprintf
       !"Expected a field in the location parameter of %{Ident}, but found %s \
         %{QualIdent}"
       callable_name kind field)

let update_operator_type_error loc =
  Error.type_error loc
    "An update operator must return the same type as its container parameter"

let trigger_outside_auto_lemma_error loc =
  Error.type_error loc "Only the postcondition of an auto lemma can have triggers"

let return_var_in_requires_error loc var_name =
  Error.type_error loc
    (Printf.sprintf
       !"Return variable %{String} cannot be used in a requires clause; it is only in \
         scope in ensures clauses"
       var_name)

let requires_on_pure_callable_error loc name =
  Error.type_error loc
    (Printf.sprintf
       !"%{Ident} may not have a requires clause; func/pred/invariant contracts must be \
         total"
       name)

let return_var_in_func_body_error loc var_name func_name =
  Error.type_error loc
    (Printf.sprintf
       !"Return variable %{String} cannot be used in the body of %{String}; it is only \
         in scope in ensures clauses"
       var_name func_name)
