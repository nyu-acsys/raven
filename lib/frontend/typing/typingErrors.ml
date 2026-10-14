(** Errors reported by type checking. *)

open Base
open Ast
open Util

(* General *)

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

(* Types *)

let no_rep_type_error loc qual_ident =
  Error.type_error loc
    ("Module "
    ^ QualIdent.to_string qual_ident
    ^ " does not have a rep type. It cannot be used in a context expecting a type")

let expected_type_ident_error loc = Error.type_error loc "Expected type identifier"

let recursive_type_alias_error loc ident =
  Error.type_error loc
    (Printf.sprintf
       !"The definition of type %{Ident} refers to itself. Only data types can be \
         recursive"
       ident)

(* Expressions *)

let finset_arity_error loc = Error.type_error loc "finset takes zero or one argument"

let constr_arity_error loc constr expected =
  Error.type_error loc (Expr.constr_to_string constr ^ " takes " ^ expected)

let proc_call_in_expression_error loc kind_name name =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{Ident} can only be called as the right-hand side of an assignment \
         statement, e.g. `x := %{Ident}(...)`. Assign its result to a variable first if \
         you need to use it in an expression"
       kind_name name name)

let expected_identifier_error loc qual_ident =
  Error.type_error loc
    ("Expected a variable, field, or callable identifier, but found "
    ^ QualIdent.to_string qual_ident)

let constructor_arity_error loc constr_ident =
  Error.type_error loc
    ("data constructor "
    ^ QualIdent.to_string constr_ident
    ^ " called with incorrect number of arguments")

let missing_explicit_argument_error loc var_name callable_name =
  Error.type_error loc
  @@ Printf.sprintf
       !"Explicit argument %s is missing in this call to %{Ident}"
       (Ident.name var_name) callable_name

let too_many_arguments_error loc callable_name =
  Error.type_error loc
  @@ Printf.sprintf "Too many arguments passed to %s" (Ident.to_string callable_name)

let return_count_error loc callable_name ~expected ~found =
  Error.type_error loc
  @@ Printf.sprintf
       !"%s has %d return parameter(s), but found %d return variable(s)"
       (callable_name |> Ident.to_string)
       expected found

let too_many_returns_error loc callable_name =
  Error.type_error loc
  @@ Printf.sprintf "Too many values returned for %s" (Ident.to_string callable_name)

let expected_atomic_procedure_error loc =
  Error.type_error loc "Expected procedure with atomic specification"

let expected_data_constructor_error loc = Error.type_error loc "Expected data constructor"

let tuple_index_error loc idx typ components =
  Error.type_error loc
    (Printf.sprintf
       !"Tuple index %d is out of bounds; %{Type} has %d component(s)"
       idx typ components)

let location_field_mismatch_error loc callable declared_field field =
  Error.type_error loc
    (Printf.sprintf
       !"%{Ident} operates on field %{QualIdent} here, but this argument names \
         %{QualIdent}"
       callable declared_field field)

let trigger_missing_variable_error loc kind var_name =
  Error.type_error loc
    (Printf.sprintf "This trigger does not mention the %s %s" kind var_name)

let expected_destructor_error loc kind ident =
  Error.type_error loc
    (Printf.sprintf
       !"Expected destructor identifier, but found %s %{QualIdent}"
       kind ident)

let impure_auto_lemma_spec_error loc name =
  Error.type_error loc
    (Printf.sprintf !"This specification of auto lemma %{Ident} is not pure" name)

let not_callable_error loc ident =
  Error.type_error loc (Printf.sprintf !"Identifier %{QualIdent} cannot be called" ident)

let expected_product_type_error loc typ =
  Error.type_error loc (Printf.sprintf !"Expected product type, but found %{Type}" typ)

let field_read_context_error loc field =
  Error.type_error loc
    (Printf.sprintf !"Cannot read field %{QualIdent} in this context" field)

let to_real_arity_error loc = Error.type_error loc "to_real takes exactly one argument"

let au_pred_commit_arity_error loc =
  Error.type_error loc
    "auCommit<proc>() called with incorrect number of arguments. Expected: first \
     argument: AtomicToken<proc>; second argument: tuple of prog args (or unit); third \
     argument: tuple of proc ret vals (or unit)"

let au_pred_arity_error loc =
  Error.type_error loc
    "au<proc>() called with incorrect number of arguments. Expected: first argument: \
     AtomicToken<proc>; second argument: tuple of proc args (or unit)"

let ghost_read_error loc =
  Error.type_error loc
    "This expression reads ghost state, so it can only be used inside a ghost block, \
     spec, or ghost-typed field"

let comprehension_variables_error loc =
  Error.type_error loc "Map/set comprehensions can only quantify over one variable"

let expected_procedure_error loc = Error.type_error loc "Expected procedure identifier"
let expected_data_destructor_error loc = Error.type_error loc "Expected data destructor"
let expected_callable_error loc = Error.type_error loc "Expected callable identifier"

let ghost_procedure_call_error loc =
  Error.type_error loc "Cannot call procedure in ghost context"

let own_arity_error loc =
  Error.type_error loc "Too many arguments supplied to predicate 'own'"

let own_ra_fraction_error loc =
  Error.type_error loc
    "'own(...)' for a field whose value is a resource algebra (RA) element does not take \
     an extra fraction argument"

(* Statements *)

let expected_predicate_error loc name =
  Error.type_error loc
    ("Expected predicate or invariant identifier, but found " ^ QualIdent.to_string name)

let not_a_field_error loc = Error.type_error loc "Expected field"
let expected_field_identifier_error loc = Error.type_error loc "Expected field identifier"

let field_identifier_mismatch_error loc kind field =
  Error.type_error loc
    (Printf.sprintf !"Expected field identifier but found %s %{QualIdent}" kind field)

let expected_field_location_error loc = Error.type_error loc "Expected field location"
let expected_local_identifier_error loc = Error.type_error loc "Expected local identifier"

let unknown_existential_error loc ident kind name =
  Error.type_error loc
    (Printf.sprintf
       !"Could not find existential variable %{Ident} in %s %{QualIdent}"
       ident kind name)

let cannot_assign_error loc kind ident =
  Error.type_error loc (Printf.sprintf !"Cannot assign to %s %{QualIdent}" kind ident)

let implicit_lhs_count_error loc proc =
  Error.type_error loc
    (Printf.sprintf
       !"Incorrect number of implicit arguments supplied on LHS for %{QualIdent}"
       proc)

let field_read_not_destructor_error loc kind =
  Error.type_error loc
    (Printf.sprintf
       "Expected a data destructor on the right-hand side of this field read, but found \
        %s"
       kind)

let duplicate_bind_error loc ident =
  Error.type_error loc (Printf.sprintf !"Duplicate bind destination %{QualIdent}" ident)

let ghost_assign_var_error loc ident =
  Error.type_error loc
    (Printf.sprintf !"Cannot assign to non-ghost var %{QualIdent} in ghost context" ident)

let ghost_assign_field_error loc field =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot assign to non-ghost field %{QualIdent} in ghost context"
       field)

let missing_arguments_error loc ident =
  Error.type_error loc
    (Printf.sprintf !"%{QualIdent} expects at least one argument" ident)

let ra_field_assign_error loc field =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot assign directly to field %{QualIdent}, whose value is a resource algebra \
         (RA) element; use a frame-preserving update ('fpu') instead"
       field)

let unknown_au_action_error loc ident =
  Error.type_error loc
    (Printf.sprintf
       !"'%{QualIdent}' is not a recognized atomic-update (AU) action (expected one of \
         bindAU, openAU, commitAU, abortAU, ...)"
       ident)

let fpu_arity_error loc =
  Error.type_error loc
    "fpu expects a field location followed by one or two values, or a reference and \
     field followed by one or two values"

let bind_au_arity_error loc = Error.type_error loc "bindAU takes no arguments"

let au_operator_arity_error loc =
  Error.type_error loc "Incorrect number of arguments supplied to AU operator."

let ghost_command_assign_error loc =
  Error.type_error loc "Ghost command cannot assign to non-ghost variable"

let fpu_non_ghost_error loc =
  Error.type_error loc "Frame-preserving updates are only allowed on ghost fields"

let field_read_lhs_error loc =
  Error.type_error loc "Expected exactly one variable on left-hand side of field read"

let fpu_location_error loc = Error.type_error loc "Could not find field location in fpu"
let ghost_return_error loc = Error.type_error loc "Cannot return in a ghost block"

let au_operator_foreign_token_error loc =
  Error.type_error loc
    "Incorrect number of arguments supplied to AU operator; expected in-args (as a \
     single tuple) since another procedure's atomicToken is being manipulated."

let fpu_field_error loc =
  Error.type_error loc
    "Frame-preserving updates ('fpu') can only be applied to ghost fields whose value is \
     a resource algebra (RA) element"

(* Overloading *)

let overload_type_normalization_error loc qual_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot normalize type %{QualIdent} while resolving overloads"
       qual_ident)

let no_applicable_overload_error loc name =
  Error.type_error loc (Printf.sprintf !"No applicable overload of %{QualIdent}" name)

let literal_argument_type_error loc =
  Error.type_error loc "This argument does not match the contextual literal type"

let ambiguous_overload_error loc name candidates =
  Error.type_error loc
    (Printf.sprintf
       !"Ambiguous function name %{Ident} (%d candidates); add a type annotation or \
         qualify the call"
       name candidates)

(* Implicit instantiation *)

let conflicting_inferred_types_error loc formal_ident functor_qual_ident prior t2 =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot infer a single type for parameter %{Ident} of %{QualIdent}: found both \
         %{Type} and %{Type}"
       formal_ident functor_qual_ident prior t2)

let unify_types_error loc t1 t2 =
  Error.type_error loc
    (Printf.sprintf !"Cannot unify type %{Type} with type %{Type}" t1 t2)

let field_argument_from_arg_error loc formal_ident functor_qual_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot infer the field argument for parameter %{Ident} of %{QualIdent} from \
         this argument; pass a location, `x.f`, or write an explicit instantiation, e.g. \
         `module M_X = %{QualIdent}[...]`"
       formal_ident functor_qual_ident functor_qual_ident)

let field_argument_error loc formal_ident functor_qual_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot infer a field argument for parameter %{Ident} of %{QualIdent}"
       formal_ident functor_qual_ident)

let field_argument_without_location_error loc formal_ident functor_qual_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot infer a field argument for parameter %{Ident} of %{QualIdent}, since \
         this call takes no location; write an explicit instantiation, e.g. `module M_X \
         = %{QualIdent}[...]`"
       formal_ident functor_qual_ident functor_qual_ident)

let type_argument_inference_error loc formal_ident functor_qual_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot infer a type argument for parameter %{Ident} of %{QualIdent}; write an \
         explicit instantiation, e.g. `module M_X = %{QualIdent}[...]`"
       formal_ident functor_qual_ident functor_qual_ident)

let module_member_inference_error loc member interface_qi field_qi =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot infer module member %{Ident} of %{QualIdent} from field %{QualIdent}; \
         write an explicit instantiation instead"
       member interface_qi field_qi)

let ambiguous_member_error loc member candidates =
  Error.type_error loc
    (Printf.sprintf !"Ambiguous function name %{Ident} (%d candidates)" member candidates)

let expected_field_error loc qual_ident =
  Error.type_error loc
    (Printf.sprintf !"Expected a field, but found %{QualIdent}" qual_ident)

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

(* Modules *)

let data_type_without_constructors_error loc =
  Error.error loc "data types must have at least one constructor"

let duplicate_constructor_error loc tp_expr =
  Error.error loc
  @@ Printf.sprintf "Duplicate constructor found in data type %s" (Type.to_string tp_expr)

let data_type_arguments_error loc = Error.error loc "Data types don't take arguments"

let manifest_field_target_error loc field_name kind target =
  Error.type_error loc
    (Printf.sprintf
       !"Expected a field on the right-hand side of 'field %{Ident} = ...', but found %s \
         %{QualIdent}"
       field_name kind target)

let manifest_field_ghost_error loc field_name ~ghost target ~target_ghost =
  Error.type_error loc
    (Printf.sprintf
       !"Field %{Ident} is declared %s, but %{QualIdent} is %s"
       field_name
       (if ghost then "ghost" else "non-ghost")
       target
       (if target_ghost then "ghost" else "non-ghost"))

let var_member_error loc =
  Error.type_error loc "Modules and interfaces cannot have var members"

let missing_type_annotation_error loc var_name =
  Error.error loc
  @@ Printf.sprintf "Type annotation missing for variable %s" (Ident.to_string var_name)

let abstract_in_program_error loc kind name =
  Error.type_error loc
    (Printf.sprintf
       !"The %s %{Ident} cannot be abstract here. An abstract member can only be \
         declared in an interface"
       kind name)

let still_abstract_error loc module_name kind name =
  Error.type_error loc
    (Printf.sprintf
       !"Module %{Ident} must be declared as an interface. The %s %{Ident} is still \
         abstract"
       module_name kind name)

let must_be_interface_error loc module_name =
  Error.type_error loc
    (Printf.sprintf !"Module %{Ident} must be declared as an interface" module_name)

let not_word_sized_error loc rep_type word_sized =
  Error.type_error loc
    (Printf.sprintf
       !"`%s` is not word-sized, so it cannot implement %{QualIdent}. An atomic \
         primitive operates on a single machine word: Int, Bool, Ref, or a data type \
         with at most four constructors each taking at most one of those"
       rep_type word_sized)

let duplicate_overload_error loc name =
  Error.redeclaration_error loc (Ident.to_string name)

let sealed_interface_error loc name =
  Error.type_error loc
    (Printf.sprintf !"Interface %{Ident} cannot be sealed with ':>'" name)

let multiple_rep_types_error loc module_name =
  Error.syntax_error loc
    (Printf.sprintf !"Found more than one rep type in module %{Ident}" module_name)

let parameter_mismatch_error loc param kind module_name oparam interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Parameter %{Ident} of %s %{Ident} does not match declaration of parameter \
         %{Ident} of interface %{QualIdent}"
       param kind module_name oparam interface_ident)

let type_argument_without_rep_error loc formal interface_qi =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot pass a type as argument for parameter %{Ident}: interface %{QualIdent} \
         does not declare a rep type"
       formal interface_qi)

(* Interfaces *)

let inherited_member_msg kind ident parent_kind parent_ident =
  Printf.sprintf
    !"%s %{Ident} inherited from %s %{QualIdent}.%{Ident}"
    (String.capitalize kind) ident parent_kind parent_ident ident

let contract_mismatch_error loc ~clause kind ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{Ident} does not have the same %s as %{Ident} in interface %{QualIdent}. \
         Repeat its contract exactly, or omit it to inherit it"
       kind ident clause ident interface_ident)

let redeclared_as_ghost_error loc kind ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot redeclare %s %{Ident} from interface %{QualIdent} as ghost"
       kind ident interface_ident)

let redeclared_as_non_ghost_error loc kind ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot redeclare ghost %s %{Ident} from interface %{QualIdent} as non-ghost"
       kind ident interface_ident)

let interface_type_mismatch_error loc kind ident typ interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{Ident} must have type %{Type} according to interface %{QualIdent}"
       (String.capitalize kind) ident typ interface_ident)

let redefined_error loc kind ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{Ident} was already defined in interface %{QualIdent}. It cannot be \
         redefined"
       (String.capitalize kind) ident interface_ident)

let redeclared_abstract_error loc kind ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{Ident} cannot be redeclared as abstract. It was already defined in \
         interface %{QualIdent}"
       (String.capitalize kind) ident interface_ident)

let formal_parameter_mismatch_error loc param kind ident orig_param orig_ident
    interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Formal parameter %{Ident} of %s %{Ident} does not match parameter %{Ident} of \
         %{Ident} in interface %{QualIdent}"
       param kind ident orig_param orig_ident interface_ident)

let parameter_count_mismatch_error loc kind ident orig_ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{Ident} does not have the same number of parameters as %{Ident} in \
         interface %{QualIdent}"
       kind ident orig_ident interface_ident)

let redeclared_as_other_kind_error loc orig_kind ident interface_ident kind =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot redeclare %s %{Ident} from %{QualIdent} as %s"
       orig_kind ident interface_ident kind)

let redeclared_from_interface_as_other_kind_error loc orig_kind ident interface_ident kind
    =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot redeclare %s %{Ident} from interface %{QualIdent} as %s"
       orig_kind ident interface_ident kind)

let redeclared_module_as_interface_error loc ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot redeclare module %{Ident} from interface %{QualIdent} as interface"
       ident interface_ident)

let redeclared_interface_as_module_error loc ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot redeclare interface %{Ident} from interface %{QualIdent} as module"
       ident interface_ident)

let must_implement_error loc kind ident module_type interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{Ident} must implement interface %{QualIdent} according to interface \
         %{QualIdent}"
       (String.capitalize kind) ident module_type interface_ident)

let module_parameters_error loc kind ident =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{Ident} cannot have module parameters"
       (String.capitalize kind) ident)

let manifest_field_type_error loc ident target target_type interface_ident orig_type =
  Error.type_error loc
    (Printf.sprintf
       !"Field %{Ident} stands for %{QualIdent}, of type %{Type}, but interface \
         %{QualIdent} declares it with type %{Type}"
       ident target target_type interface_ident orig_type)

let interface_field_ghost_error loc ident ~ghost interface_ident ~orig_ghost =
  Error.type_error loc
    (Printf.sprintf
       !"Field %{Ident} is declared %s, but interface %{QualIdent} declares it %s"
       ident
       (if ghost then "ghost" else "non-ghost")
       interface_ident
       (if orig_ghost then "ghost" else "non-ghost"))

let rep_type_change_error loc ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot change rep type annotation for type %{Ident} inherited from interface \
         %{QualIdent}"
       ident interface_ident)

let type_redeclared_abstract_error loc ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Type %{Ident} cannot be redeclared as abstract. It was already defined in \
         interface %{QualIdent}"
       ident interface_ident)

let type_redefined_error loc ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"Type %{Ident} was already defined in interface %{QualIdent}"
       ident interface_ident)

let does_not_implement_error loc kind module_ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{QualIdent} does not implement interface %{QualIdent}"
       (String.capitalize kind) module_ident interface_ident)

let needs_instantiation_error loc kind module_ident interface_ident =
  Error.type_error loc
    (Printf.sprintf
       !"%s %{QualIdent} first needs to be instantiated to obtain a module with \
         interface %{QualIdent}"
       (String.capitalize kind) module_ident interface_ident)

let shared_ancestor_error loc first second ancestor =
  Error.type_error loc
    (Printf.sprintf
       !"Interfaces %{QualIdent} and %{QualIdent} cannot both be implemented here: they \
         share the ancestor %{QualIdent}"
       first second ancestor)

let overloaded_interface_type_error loc typ =
  Error.type_error loc
    (Printf.sprintf
       !"Cannot determine type %{Type} while matching overloaded interface function"
       typ)

let no_overload_implementation_error loc source parent =
  Error.type_error loc
    (Printf.sprintf "No implementation matches overload %s in interface %s" source parent)

let multiple_overload_implementations_error loc source parent =
  Error.type_error loc
    (Printf.sprintf "Multiple implementations match overload %s in interface %s" source
       parent)

let parent_not_module_error loc kind parent =
  Error.type_error loc
    (Printf.sprintf
       !"Expected a module or interface in the parent clause, but found %s %{QualIdent}"
       kind parent)

let type_as_interface_argument_error loc =
  Error.type_error loc
    "An inherited interface must be applied to modules, not to bare types; name a module \
     implementing the parameter's interface instead"

let inherited_twice_error loc member module_name =
  Error.type_error loc
    (Printf.sprintf
       !"Member %{Ident} is declared by more than one of the interfaces %s implements; a \
         module cannot inherit two declarations of the same name"
       member module_name)
