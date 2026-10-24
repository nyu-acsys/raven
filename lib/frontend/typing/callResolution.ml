open Base
open Ast
open Util
open TypingMonad
open TypingErrors

type generic = {
  functor_name : QualIdent.t;
  module_ : Module.t;
  signature : ImplicitInstantiation.functor_signature;
  declaration : Callable.t;
  field_reps : (QualIdent.t * Ident.t * Ident.t) list;
}

type primitive = Core of Expr.constr | Finset

type target = {
  name : QualIdent.t;
  symbol : Rewriter.Symbol.t option;
  generic : generic option;
  candidate : OverloadResolution.candidate;
  primitive : primitive option;
}

type resolved =
  | Symbol of QualIdent.t * Rewriter.Symbol.t * Type.t option
  | Primitive of primitive * (Type.t list * Type.t) option

let primitive_operator name =
  if QualIdent.is_local name then
    match Ident.name (QualIdent.unqualify name) with
    | "<" -> Some (Core Expr.Lt)
    | "<=" -> Some (Core Expr.Leq)
    | "_[_:=_]" -> Some (Core Expr.MapUpdate)
    | "_[_]" -> Some (Core Expr.MapLookUp)
    | "finset" -> Some Finset
    | _ -> None
  else None

let primitive_signature identity constr ~arity =
  let parameter type_ = { OverloadResolution.type_; ghost = false; implicit = false } in
  let parameters, returns, generic_parameters =
    match constr with
    | Finset ->
        let element = QualIdent.append identity (Ident.make Loc.dummy "$element" 0) in
        let type_ = Type.var element in
        (List.init arity ~f:(fun _ -> type_), Type.mk_finset Loc.dummy type_, [ element ])
    | Core ((Expr.MapUpdate | Expr.MapLookUp) as constr) ->
        let domain = QualIdent.append identity (Ident.make Loc.dummy "$domain" 0) in
        let range = QualIdent.append identity (Ident.make Loc.dummy "$range" 0) in
        let key = Type.var domain and value = Type.var range in
        let map = Type.map key value in
        ( (match constr with Expr.MapUpdate -> [ map; key; value ] | _ -> [ map; key ]),
          (match constr with Expr.MapUpdate -> map | _ -> value),
          [ domain; range ] )
    | Core _ -> ([ Type.num; Type.num ], Type.bool, [])
  in
  {
    OverloadResolution.identity;
    kind = Func;
    ghost = false;
    parameters = List.map parameters ~f:parameter;
    returns;
    generic_parameters;
  }

(* A known map supplies the signature; index and value arguments need only subtype it. *)
let specialize_map_operator constr (candidate : OverloadResolution.candidate) arguments =
  let base =
    match List.hd arguments with
    | Some { OverloadResolution.type_ = Known tp | Literal tp; _ } -> Some tp
    | _ -> None
  in
  match base with
  | Some (Type.App (Map, [ domain; range ], _) as map)
    when not (OverloadResolution.uncertain domain || OverloadResolution.uncertain range)
    ->
      {
        candidate with
        parameters =
          List.map
            (match constr with
            | Expr.MapUpdate -> [ map; domain; range ]
            | _ -> [ map; domain ])
            ~f:(fun type_ ->
              { OverloadResolution.type_; ghost = false; implicit = false });
        returns = (match constr with Expr.MapUpdate -> map | _ -> range);
        generic_parameters = [];
      }
  | Some (Type.App (FinSet, [ domain ], _) as set) when Poly.equal constr Expr.MapLookUp
    ->
      let key, generics =
        if OverloadResolution.uncertain domain then
          match candidate.generic_parameters with
          | key :: _ -> (Type.var key, [ key ])
          | [] -> (domain, [])
        else (domain, [])
      in
      let set =
        if List.is_empty generics then set else Type.mk_finset (Type.to_loc set) key
      in
      {
        candidate with
        parameters =
          List.map [ set; key ] ~f:(fun type_ ->
              { OverloadResolution.type_; ghost = false; implicit = false });
        returns = Type.bool;
        generic_parameters = generics;
      }
  | _ -> candidate

let normalized ?scope ?(fallback = false) ~loc tp =
  let open Rewriter.Syntax in
  let lookup qi =
    match scope with
    | None -> CandidateTypes.lookup qi
    | Some scope ->
        let* found = Rewriter.in_scope_of scope (CandidateTypes.lookup qi) in
        if fallback && Option.is_none found then CandidateTypes.lookup qi
        else Rewriter.return found
  in
  let+ normalized = CandidateTypes.normalize ~lookup tp in
  match normalized with
  | Ok tp -> tp
  | Error (Unknown_type qi | Not_type qi | Cyclic_alias qi | Needs_instantiation qi) ->
      overload_type_normalization_error loc qi

let exported_declarations functor_name module_ =
  let open Rewriter.Syntax in
  match module_.Module.mod_decl with
  | { mod_decl_is_sealed = true; mod_decl_returns = [ (interface, args) ]; _ } ->
      let+ _, symbol = Rewriter.resolve_and_find interface in
      Rewriter.Symbol.extract symbol ~f:(fun _ requalify -> function
        | Module.ModDef public ->
            let formal_substitutions =
              List.filter_map (List.zip_exn public.mod_decl.mod_decl_formals args)
                ~f:(fun (formal, arg) ->
                  match arg with
                  | Module.ModArg arg ->
                      Some
                        ( QualIdent.append interface formal.mod_inst_name,
                          QualIdent.to_list arg )
                  | Module.TypeArg _ -> None)
            in
            let requalify qi =
              QualIdent.requalify
                (formal_substitutions @ [ (interface, QualIdent.to_list functor_name) ])
                (requalify qi)
            in
            let parameter p =
              {
                p with
                Type.var_type = CandidateTypes.rewrite_type ~f:requalify p.Type.var_type;
              }
            in
            List.map public.mod_def ~f:(function
              | Module.SymbolDef (CallDef call) ->
                  let decl = call.call_decl in
                  Module.SymbolDef
                    (CallDef
                       {
                         call with
                         call_decl =
                           {
                             decl with
                             call_decl_formals =
                               List.map decl.call_decl_formals ~f:parameter;
                             call_decl_returns =
                               List.map decl.call_decl_returns ~f:parameter;
                             call_decl_loc_params =
                               List.map decl.call_decl_loc_params ~f:requalify;
                           };
                       })
              | instr -> instr)
        | _ -> module_.mod_def)
  | _ -> Rewriter.return module_.mod_def

let discover_generics names =
  let open Rewriter.Syntax in
  let+ targets =
    Rewriter.List.map names ~f:(fun name ->
        let* prefix = ImplicitInstantiation.resolve_generic_functor_prefix name in
        match prefix with
        | None -> Rewriter.return []
        | Some (functor_name, module_, member) ->
            let* declarations = exported_declarations functor_name module_ in
            let* signature =
              ImplicitInstantiation.discover_functor_signature
                ~functor_qual_ident:functor_name module_
            in
            let* field_reps =
              Rewriter.List.map signature.field_formals
                ~f:(fun (formal, (_, _, members)) ->
                  ImplicitInstantiation.rep_vars_of_insts
                    ~scope_qi:(QualIdent.append functor_name formal)
                    members)
            in
            Rewriter.return
              (List.filter_map declarations ~f:(function
                | Module.SymbolDef (CallDef declaration)
                  when Poly.(Callable.kind declaration = Func)
                       && (Ident.equal (Callable.source_ident declaration) member
                          || Ident.equal declaration.call_decl.call_decl_name member) ->
                    Some
                      {
                        functor_name;
                        module_;
                        signature;
                        declaration;
                        field_reps = List.concat field_reps;
                      }
                | _ -> None)))
  in
  List.concat targets

let is_literal hooks = function
  | Expr.App ((Empty | Enumeration _ | Tuple | Int _ | Real _ | Bool _ | Null), _, _) ->
      true
  | Expr.App (ExprExt extension, _, _) -> hooks.Rewriter.expr_ext_is_literal extension
  | _ -> false

let reads_ghost expr =
  let open Rewriter.Syntax in
  (* Speculative types reflect the ghost context, rather than a value's origin. *)
  let rec go bound = function
    | Expr.App (Var qi, args, _) ->
        let arguments () = Rewriter.List.exists args ~f:(go bound) in
        let* found = CandidateTypes.lookup qi in
        begin match found with
        | Some (_, (_, Module.VarDef var, _)) ->
            let+ arguments = arguments () in
            arguments
            || (not (Set.mem bound qi))
               && (var.var_decl.var_ghost || Type.is_ghost var.var_decl.var_type)
        | Some (_, (_, Module.FieldDef field, _)) ->
            let+ arguments = arguments () in
            arguments || field.field_is_ghost
        | Some (_, (_, Module.CallDef call, _)) ->
            if Type.is_ghost (Callable.return_type call.call_decl) then
              Rewriter.return true
            else
              Rewriter.List.exists
                (List.mapi args ~f:(fun index arg -> (index, arg)))
                ~f:(fun (index, arg) ->
                  let erased =
                    Option.value_map (List.nth call.call_decl.call_decl_formals index)
                      ~default:false ~f:(fun formal ->
                        formal.var_ghost || Type.is_ghost formal.var_type)
                  in
                  if erased then Rewriter.return false else go bound arg)
        | _ -> arguments ()
        end
    | Expr.App (_, args, _) -> Rewriter.List.exists args ~f:(go bound)
    | Expr.Binder (_, vars, triggers, body, _) ->
        let bound =
          List.fold vars ~init:bound ~f:(fun bound var ->
              Set.add bound (QualIdent.from_ident var.Type.var_name))
        in
        let* body = go bound body in
        if body then Rewriter.return true
        else
          Rewriter.List.exists triggers ~f:(fun trigger ->
              Rewriter.List.exists trigger ~f:(go bound))
  in
  go (Set.empty (module QualIdent)) expr

let evidence ~check_expr ~claimed_location ~location_indices args =
  let open Rewriter.Syntax in
  let+ prepared =
    Rewriter.List.map
      (List.mapi args ~f:(fun i arg -> (i, arg)))
      ~f:(fun (index, original) ->
        let* claimed =
          if List.mem location_indices index ~equal:Int.equal then
            claimed_location original
          else Rewriter.return original
        in
        let* expr, location =
          match claimed with
          | Expr.App (Read, [ ref_expr; App (Var field, [], _) ], _)
            when List.mem location_indices index ~equal:Int.equal ->
              let+ found = CandidateTypes.lookup field in
              begin match found with
              | Some (_, (_, Module.FieldDef _, _)) -> (ref_expr, Some (index, field))
              | _ -> (original, None)
              end
          | _ -> Rewriter.return (original, None)
        in
        let* typed = speculatively (check_expr expr (Type.any |> Type.set_ghost true)) in
        let* hooks = Rewriter.current_ext_hooks in
        let+ ghost = reads_ghost typed in
        let tp = Expr.to_type typed |> Type.set_ghost false in
        let type_ =
          if is_literal hooks expr then OverloadResolution.Literal tp
          else if Type.contains_bot tp then
            (* Preserve container shape while empty entries await a type context. *)
            match tp with
            | Type.App ((Map | FinSet | Prod), _, _) -> Literal tp
            | _ -> Unknown
          else Known tp
        in
        ({ OverloadResolution.type_; ghost }, location))
  in
  (List.map prepared ~f:fst, List.filter_map prepared ~f:snd)

let location_parameters target =
  match (target.generic, target.symbol) with
  | Some generic, _ -> generic.declaration.call_decl.call_decl_loc_params
  | _, Some symbol ->
      Rewriter.Symbol.extract symbol ~f:(fun _ requalify -> function
        | Module.CallDef call -> List.map call.call_decl.call_decl_loc_params ~f:requalify
        | _ -> [])
  | _ -> []

let field_constraints target locations =
  let open Rewriter.Syntax in
  let parameters = location_parameters target in
  (* Whether [declared] names the field [actual]. *)
  let same_field declared actual rest bindings solve =
    let* expected = CandidateTypes.lookup declared in
    match expected with
    | Some (expected, _) when QualIdent.equal expected actual -> solve bindings rest
    | _ -> Rewriter.return (Error OverloadResolution.Argument)
  in
  let rec solve bindings = function
    | [] -> Rewriter.return (Ok bindings)
    | (index, field) :: rest ->
        let* found = CandidateTypes.lookup field in
        begin match (List.nth parameters index, found) with
        | Some declared, Some (actual, ((_, Module.FieldDef _, _) as symbol)) ->
            let definition =
              Rewriter.Symbol.extract symbol ~f:(fun _ requalify -> function
                | Module.FieldDef field ->
                    {
                      field with
                      field_type =
                        CandidateTypes.rewrite_type ~f:requalify field.field_type;
                    }
                | _ -> Error.internal_error (QualIdent.to_loc field) "Expected field")
            in
            begin match target.generic with
            | None -> same_field declared actual rest bindings solve
            | Some generic ->
                let formal = QualIdent.unqualify (QualIdent.pop declared) in
                begin match
                  List.Assoc.find generic.signature.field_formals formal
                    ~equal:Ident.equal
                with
                | None -> same_field declared actual rest bindings solve
                | Some (interface, expected, _) -> (
                    let* expected_type =
                      CandidateTypes.rewrite_type
                        ~f:
                          (QualIdent.requalify
                             [
                               ( interface,
                                 QualIdent.to_list
                                   (QualIdent.append generic.functor_name formal) );
                             ])
                        expected.field_type
                      |> normalized ~scope:target.name ~loc:(QualIdent.to_loc field)
                    in
                    let* actual_type =
                      normalized ~loc:(QualIdent.to_loc field) definition.field_type
                    in
                    if Bool.(expected.field_is_ghost <> definition.field_is_ghost) then
                      Rewriter.return (Error OverloadResolution.Ghost)
                    else
                      match
                        OverloadResolution.infer target.candidate ~only_unbound:false
                          bindings expected_type actual_type
                      with
                      | Error reason -> Rewriter.return (Error reason)
                      | Ok bindings ->
                          let expected_type =
                            OverloadResolution.substitute bindings expected_type
                          in
                          if
                            OverloadResolution.partial_subtype target.candidate
                              actual_type expected_type
                          then solve bindings rest
                          else Rewriter.return (Error OverloadResolution.Argument))
                end
            end
        | _ -> Rewriter.return (Error OverloadResolution.Argument)
        end
  in
  solve [] locations

(* Represent generic reps structurally during trials; no instance is created. *)
let virtual_formals generic tp =
  let prefix = QualIdent.to_list generic.functor_name in
  let head =
    QualIdent.append generic.functor_name
      (Option.value generic.module_.mod_decl.mod_decl_rep
         ~default:(Ident.make Loc.dummy "$rep" 0))
  in
  let variables =
    List.map generic.signature.formal_reps ~f:(fun (qi, _, _) -> Type.var qi)
  in
  let rec virtualize (Type.App (constr, args, attr)) =
    match (constr, args) with
    | Type.Var qi, []
      when List.exists generic.signature.rep_suffixes ~f:(fun suffix ->
               List.equal Ident.equal (QualIdent.to_list qi) (prefix @ suffix)) ->
        Type.App (Var head, variables, attr)
    | _ -> Type.App (constr, List.map args ~f:virtualize, attr)
  in
  virtualize tp

let rec virtual_applications (Type.App (head, args, attr) as tp) =
  let open Rewriter.Syntax in
  match (head, args) with
  | Type.Var qi, [] ->
      let* application = ImplicitInstantiation.generated_application qi in
      begin match application with
      | None -> Rewriter.return tp
      | Some { head; arguments; _ } ->
          let+ arguments = Rewriter.List.map arguments ~f:virtual_applications in
          Type.App (Var head, arguments, attr)
      end
  | _ ->
      let+ args = Rewriter.List.map args ~f:virtual_applications in
      Type.App (head, args, attr)

let virtual_arguments ?generic ~templates evidence =
  let open Rewriter.Syntax in
  let head =
    Option.map generic ~f:(fun generic ->
        QualIdent.append generic.functor_name
          (Option.value generic.module_.mod_decl.mod_decl_rep
             ~default:(Ident.make Loc.dummy "$rep" 0)))
  in
  let rec virtualize template (Type.App (constr, args, attr) as tp) =
    match (template, constr, args) with
    | Type.App (Var template_head, _ :: _, _), Type.Var qi, []
      when Option.value_map head ~default:false ~f:(QualIdent.equal template_head) ->
        let generic = Option.value_exn generic in
        let* found =
          ImplicitInstantiation.instance_of_rep ~functor_qual_ident:generic.functor_name
            ~rep_suffixes:generic.signature.rep_suffixes qi
        in
        begin match found with
        | None -> Rewriter.return (tp, [])
        | Some (instance, modules) ->
            let+ args =
              Rewriter.List.map generic.signature.formal_reps ~f:(fun (_, formal, rep) ->
                  normalized ~loc:(Type.to_loc tp)
                    (Type.var (QualIdent.append (modules formal) rep)))
            in
            (Type.App (Var template_head, args, attr), [ instance ])
        end
    | Type.App (Var template_head, templates, _), Type.Var qi, []
      when not (List.is_empty templates) ->
        let* application = ImplicitInstantiation.generated_application qi in
        begin match application with
        | Some { head; arguments; _ } when QualIdent.equal head template_head ->
            begin match List.zip templates arguments with
            | Ok pairs ->
                let+ expanded =
                  Rewriter.List.map pairs ~f:(fun (template, argument) ->
                      virtualize template argument)
                in
                ( Type.App (Var head, List.map expanded ~f:fst, attr),
                  List.concat_map expanded ~f:snd )
            | Unequal_lengths -> Rewriter.return (tp, [])
            end
        | _ -> Rewriter.return (tp, [])
        end
    | Type.App (Map, [ domain; _ ], _), Type.FinSet, [ element ] ->
        let+ element, instances = virtualize domain element in
        (Type.App (constr, [ element ], attr), instances)
    | Type.App (_, formal_args, _), _, _ ->
        begin match List.zip formal_args args with
        | Ok pairs ->
            let+ expanded =
              Rewriter.List.map pairs ~f:(fun (formal, actual) ->
                  virtualize formal actual)
            in
            ( Type.App (constr, List.map expanded ~f:fst, attr),
              List.concat_map expanded ~f:snd )
        | Unequal_lengths -> Rewriter.return (tp, [])
        end
  in
  let+ expanded =
    Rewriter.List.map
      (List.mapi evidence ~f:(fun index argument -> (index, argument)))
      ~f:(fun (index, argument) ->
        let template = Option.value (List.nth templates index) ~default:Type.any in
        match argument.OverloadResolution.type_ with
        | Unknown -> Rewriter.return (argument, [])
        | Known tp ->
            let+ tp, instances = virtualize template tp in
            ({ argument with type_ = Known tp }, instances)
        | Literal tp ->
            let+ tp, _ = virtualize template tp in
            ({ argument with type_ = Literal tp }, []))
  in
  ( List.map expanded ~f:fst,
    List.concat_map expanded ~f:snd |> List.dedup_and_sort ~compare:QualIdent.compare )

let normalize_candidate_type ?generic ~scope ~loc tp =
  let open Rewriter.Syntax in
  let virtualize tp =
    let tp = Option.value_map generic ~default:tp ~f:(fun g -> virtual_formals g tp) in
    virtual_applications tp
  in
  let rec expand tp =
    let* (Type.App (head, args, attr) as tp) = virtualize tp in
    match (head, args) with
    | Type.Var _, _ :: _ -> Rewriter.return tp
    | _ when List.is_empty args ->
        let* expanded = normalized ~scope ~fallback:true ~loc tp in
        virtualize expanded
    | _ ->
        let+ args = Rewriter.List.map args ~f:expand in
        Type.App (head, args, attr)
  in
  expand tp

(** The names under which to look for generic functions: [name] if it resolves to nothing,
    or else the [imported] names that resolve to nothing. *)
let generic_names ~ordinary ~imported name =
  let open Rewriter.Syntax in
  if List.is_empty imported then
    Rewriter.return (if List.is_empty ordinary then [ name ] else [])
  else
    Rewriter.List.fold_right imported ~init:[] ~f:(fun imported names ->
        let+ candidates = Rewriter.probe_candidates imported in
        if List.is_empty candidates then imported :: names else names)

(* Test literal result shapes without creating generic instances. *)
let enumeration_accepts_type opener singleton expected =
  let open Rewriter.Syntax in
  let name =
    QualIdent.from_ident
      (Ident.make (Type.to_loc expected) (Expr.enumeration_name opener ~singleton) 0)
  in
  let* ordinary = Rewriter.resolve_and_find_candidates name in
  let* imported = Rewriter.find_import_targets name in
  let* generic_names = generic_names ~ordinary ~imported name in
  let* generics = discover_generics generic_names in
  let accepts candidate expected =
    match
      OverloadResolution.infer candidate ~only_unbound:true [] candidate.returns expected
    with
    | Error _ -> false
    | Ok bindings ->
        OverloadResolution.partial_subtype candidate
          (OverloadResolution.substitute bindings candidate.returns)
          expected
  in
  let ordinary_accepts (identity, symbol) =
    match OverloadResolution.of_symbol ~identity ~generic_parameters:[] symbol with
    | None -> Rewriter.return false
    | Some candidate ->
        let+ returns =
          normalized
            ~scope:(Rewriter.Symbol.orig_qid symbol)
            ~fallback:true ~loc:(Type.to_loc expected) candidate.returns
        in
        accepts { candidate with returns } expected
  in
  let generic_accepts generic =
    let parameters = List.map generic.signature.formal_reps ~f:(fun (qi, _, _) -> qi) in
    let identity =
      QualIdent.append generic.functor_name generic.declaration.call_decl.call_decl_name
    in
    let candidate =
      {
        OverloadResolution.identity;
        kind = Func;
        ghost = false;
        parameters = [];
        returns = Callable.return_type generic.declaration.call_decl;
        generic_parameters = parameters;
      }
    in
    let* returns =
      normalized ~scope:identity ~fallback:true ~loc:(Type.to_loc expected)
        candidate.returns
    in
    let returns = virtual_formals generic returns in
    let candidate = { candidate with returns } in
    let+ expected, _ =
      virtual_arguments ~generic ~templates:[ returns ]
        [ { OverloadResolution.type_ = Known expected; ghost = false } ]
    in
    match expected with
    | [ { type_ = Known expected; _ } ] -> accepts candidate expected
    | _ -> false
  in
  let* ordinary_accepts = Rewriter.List.exists ordinary ~f:ordinary_accepts in
  if ordinary_accepts then Rewriter.return true
  else Rewriter.List.exists generics ~f:generic_accepts

(** [candidate] with [f] applied to the types of its parameters and result. *)
let map_candidate_types (candidate : OverloadResolution.candidate) ~f =
  let open Rewriter.Syntax in
  let* parameters =
    Rewriter.List.map candidate.parameters ~f:(fun p ->
        let+ type_ = f p.OverloadResolution.type_ in
        { p with type_ })
  in
  let+ returns = f candidate.returns in
  { candidate with parameters; returns }

(** The target of the ordinary function [name], with its types normalized in its scope. *)
let ordinary_target ~loc (name, symbol) =
  let open Rewriter.Syntax in
  match OverloadResolution.of_symbol ~identity:name ~generic_parameters:[] symbol with
  | None -> Rewriter.return None
  | Some candidate ->
      let+ candidate =
        map_candidate_types candidate
          ~f:(normalize_candidate_type ~scope:(Rewriter.Symbol.orig_qid symbol) ~loc)
      in
      Some { name; symbol = Some symbol; generic = None; candidate; primitive = None }

(** The target of the function of the functor [generic], with its rep types as generic
    parameters. *)
let generic_target ~loc generic =
  let open Rewriter.Syntax in
  let name =
    QualIdent.append generic.functor_name generic.declaration.call_decl.call_decl_name
  in
  let parameters =
    List.map (generic.signature.formal_reps @ generic.field_reps) ~f:(fun (qi, _, _) ->
        qi)
  in
  let symbol = (name, Module.CallDef generic.declaration, (false, false, [])) in
  let candidate =
    Option.value_exn
      (OverloadResolution.of_symbol ~identity:name ~generic_parameters:parameters symbol)
  in
  let* _, functor_symbol = Rewriter.resolve_and_find generic.functor_name in
  let scope =
    QualIdent.append
      (Rewriter.Symbol.orig_qid functor_symbol)
      generic.declaration.call_decl.call_decl_name
  in
  let+ candidate =
    Rewriter.in_scope_of scope
      (map_candidate_types candidate ~f:(normalize_candidate_type ~generic ~scope ~loc))
  in
  { name; symbol = None; generic = Some generic; candidate; primitive = None }

(** The target of the primitive operator [constr], applied to [arity] arguments. *)
let primitive_target ~loc ~arity constr =
  let identity =
    QualIdent.from_ident
      (Ident.make loc
         ("$primitive_"
         ^
         match constr with
         | Core constr -> Expr.constr_to_string constr
         | Finset -> "finset")
         0)
  in
  {
    name = identity;
    symbol = None;
    generic = None;
    primitive = Some constr;
    candidate = primitive_signature identity constr ~arity;
  }

(** The expected type in terms of the virtual formals of [generic], with the instances
    that its result type selects. *)
let virtual_expected generic target expected =
  let open Rewriter.Syntax in
  let+ result, instances =
    virtual_arguments ~generic ~templates:[ target.candidate.returns ]
      [ { OverloadResolution.type_ = Known expected; ghost = false } ]
  in
  let expected = match result with [ { type_ = Known tp; _ } ] -> tp | _ -> expected in
  (expected, instances)

(** Tries [target] on [arguments]: the outcome of matching it, with the existing instance
    that a generic target selects, if any. *)
let try_target ~expected arguments locations target =
  let open Rewriter.Syntax in
  let target =
    match target.primitive with
    | Some (Core ((MapUpdate | MapLookUp) as constr)) ->
        {
          target with
          candidate = specialize_map_operator constr target.candidate arguments;
        }
    | _ -> target
  in
  let* arguments, instances =
    virtual_arguments ?generic:target.generic
      ~templates:(List.map target.candidate.parameters ~f:(fun p -> p.type_))
      arguments
  in
  let* result, result_instances =
    virtual_arguments ?generic:target.generic ~templates:[ target.candidate.returns ]
      [ { OverloadResolution.type_ = Known expected; ghost = false } ]
  in
  let expected = match result with [ { type_ = Known tp; _ } ] -> tp | _ -> expected in
  let instances = if List.is_empty instances then result_instances else instances in
  let+ outcome =
    if List.length instances > 1 then
      Rewriter.return (OverloadResolution.Mismatch Argument)
    else
      let+ constraints = field_constraints target locations in
      match constraints with
      | Error reason -> OverloadResolution.Mismatch reason
      | Ok bindings ->
          let candidate =
            {
              target.candidate with
              generic_parameters =
                List.filter target.candidate.generic_parameters ~f:(fun qi ->
                    not (List.Assoc.mem bindings qi ~equal:QualIdent.equal));
              parameters =
                List.map target.candidate.parameters ~f:(fun p ->
                    { p with type_ = OverloadResolution.substitute bindings p.type_ });
              returns = OverloadResolution.substitute bindings target.candidate.returns;
            }
          in
          OverloadResolution.match_candidate ~expected
            ~ghost_context:(Type.is_ghost expected) candidate arguments
  in
  (target, List.hd instances, outcome)

(** [trials] without the generic targets whose instance is one of the [ordinary] targets:
    a concrete import and a generic import can select the same existing instance. *)
let without_duplicate_instances ordinary trials =
  let open Rewriter.Syntax in
  Rewriter.List.fold_right trials ~init:[]
    ~f:(fun ((target, instance, _) as trial) kept ->
      match (target.generic, instance) with
      | Some generic, Some instance ->
          let+ resolved =
            Rewriter.probe_candidates
              (QualIdent.append instance generic.declaration.call_decl.call_decl_name)
          in
          let duplicate =
            List.exists ordinary ~f:(fun concrete ->
                match resolved with
                | [ name ] -> QualIdent.equal concrete.name name
                | _ -> false)
          in
          if duplicate then kept else trial :: kept
      | _ -> Rewriter.return (trial :: kept))

(** Rejects the trials whose solution gives an empty or singleton literal among [args] a
    type that the literal cannot have. *)
let check_literal_arguments ~args arguments trials =
  let open Rewriter.Syntax in
  let* hooks = Rewriter.current_ext_hooks in
  Rewriter.List.map trials ~f:(fun (target, instance, outcome) ->
      match outcome with
      | OverloadResolution.Mismatch _ -> Rewriter.return (target, instance, outcome)
      | Applicable solution | Underdetermined solution ->
          let checks =
            List.filter_mapi args ~f:(fun index arg ->
                match
                  (arg, List.nth arguments index, List.nth solution.parameter_types index)
                with
                | ( Expr.App (Enumeration opener, (([] | [ _ ]) as entries), _),
                    Some { OverloadResolution.type_ = Literal (Type.App (Bot, [], _)); _ },
                    Some formal ) ->
                    Some
                      (enumeration_accepts_type opener
                         (not (List.is_empty entries))
                         formal)
                | ( Expr.App (ExprExt extension, _, _),
                    Some { OverloadResolution.type_ = Literal (Type.App (Bot, [], _)); _ },
                    Some formal ) ->
                    let formal =
                      if OverloadResolution.contains_generic target.candidate formal then
                        Type.any
                      else formal
                    in
                    Some (lift (hooks.expr_ext_literal_accepts_type extension formal))
                | _ -> None)
          in
          let+ accepted = Rewriter.List.map checks ~f:Fn.id in
          let outcome =
            if List.for_all accepted ~f:Fn.id then outcome
            else OverloadResolution.Mismatch Argument
          in
          (target, instance, outcome))

(** The most specific applicable trials, and the underdetermined ones. *)
let select trials =
  let applicable, deferred =
    List.fold trials ~init:([], [])
      ~f:(fun (applicable, deferred) (target, instance, outcome) ->
        match outcome with
        | OverloadResolution.Applicable solution ->
            ((target, instance, solution) :: applicable, deferred)
        | Underdetermined solution ->
            (applicable, (target, instance, solution) :: deferred)
        | Mismatch _ -> (applicable, deferred))
  in
  let winners =
    List.filter applicable ~f:(fun (_, _, solution) ->
        not
          (List.exists applicable ~f:(fun (_, _, other) ->
               OverloadResolution.more_specific other solution)))
  in
  (winners, deferred)

(** Resolves the generic function [name] by implicit instantiation from its arguments. *)
let resolve_implicitly ~check_expr ~claimed_location ~loc ~args ~expected ~return_type
    name =
  let open Rewriter.Syntax in
  let* selected =
    ImplicitInstantiation.try_resolve_implicit_instantiation ~check_expr ~claimed_location
      ~loc ~qual_ident:name ~arg_exprs:args ~expected_typ:expected ()
  in
  match selected with
  | Some name ->
      let+ symbol = Rewriter.resolve_and_find_opt name in
      Option.map symbol ~f:(fun (name, symbol) -> Symbol (name, symbol, return_type))
  | None -> Rewriter.return None

(** Resolves the selected function of the functor [generic] to its instance: the existing
    [instance], or a new one with the bindings of [solution], refined by context if the
    call is [contextual]. *)
let resolve_generic_winner ~loc ~args ~expected ~contextual arguments generic target
    instance (solution : OverloadResolution.solution) =
  let open Rewriter.Syntax in
  let* bindings =
    if contextual && Option.is_none instance then
      let+ context, _ = virtual_expected generic target expected in
      (* Context refines this selected target; it never chooses another overload. *)
      match
        OverloadResolution.infer target.candidate ~only_unbound:true []
          target.candidate.returns context
      with
      | Error _ -> solution.bindings
      | Ok context ->
          List.fold context ~init:solution.bindings ~f:(fun bindings (qi, tp) ->
              List.Assoc.add bindings qi tp ~equal:QualIdent.equal)
    else Rewriter.return solution.bindings
  in
  let* checked_arguments, _ =
    virtual_arguments ~generic
      ~templates:(List.map target.candidate.parameters ~f:(fun p -> p.type_))
      arguments
  in
  let () =
    if contextual && Option.is_none instance then
      List.iteri checked_arguments ~f:(fun index argument ->
          match
            (argument.OverloadResolution.type_, List.nth target.candidate.parameters index)
          with
          | Known actual, Some formal ->
              let expected = OverloadResolution.substitute bindings formal.type_ in
              if not (OverloadResolution.partial_subtype target.candidate actual expected)
              then literal_argument_type_error (Expr.to_loc (List.nth_exn args index))
          | _ -> ())
  in
  let* instance =
    match instance with
    | Some instance -> Rewriter.return instance
    | None ->
        let bindings =
          List.map generic.signature.formal_reps ~f:(fun (qi, formal, _) ->
              (formal, List.Assoc.find_exn bindings qi ~equal:QualIdent.equal))
        in
        ImplicitInstantiation.instantiate_solution ~loc
          ~functor_qual_ident:generic.functor_name generic.module_
          ~signature:generic.signature
          { bindings; field_bindings = [] }
  in
  let+ symbol =
    Rewriter.resolve_and_find_opt
      (QualIdent.append instance generic.declaration.call_decl.call_decl_name)
  in
  Option.map symbol ~f:(fun (name, symbol) ->
      Symbol
        ( name,
          symbol,
          Some (OverloadResolution.substitute bindings target.candidate.returns) ))

let resolve_overloaded ~check_expr ~claimed_location ~loc ~name ~args ~expected
    ~contextual ordinary generics primitive =
  let open Rewriter.Syntax in
  let* expected = TypeExpr.expand_type_expr expected in
  let* ordinary = Rewriter.List.map ordinary ~f:(ordinary_target ~loc) in
  let ordinary = List.filter_opt ordinary in
  let* generics = Rewriter.List.map generics ~f:(generic_target ~loc) in
  let primitives =
    Option.to_list
      (Option.map primitive ~f:(primitive_target ~loc ~arity:(List.length args)))
  in
  let targets =
    ordinary @ generics @ primitives
    |> List.dedup_and_sort ~compare:(fun a b -> QualIdent.compare a.name b.name)
  in
  let location_indices =
    List.concat_map targets ~f:(fun target ->
        List.range 0 (List.length (location_parameters target)))
    |> List.dedup_and_sort ~compare:Int.compare
  in
  let* arguments, locations =
    evidence ~check_expr ~claimed_location ~location_indices args
  in
  let* trials = Rewriter.List.map targets ~f:(try_target ~expected arguments locations) in
  let* trials = without_duplicate_instances ordinary trials in
  let* trials = check_literal_arguments ~args arguments trials in
  let winners, deferred = select trials in
  let resolve_implicitly =
    resolve_implicitly ~check_expr ~claimed_location ~loc ~args ~expected
  in
  let resolve_single_generic () =
    match targets with
    | [ { generic = Some _; name; _ } ] -> resolve_implicitly ~return_type:None name
    | _ -> no_applicable_overload_error loc name
  in
  match (deferred, winners) with
  | [], [ (target, instance, solution) ] ->
      begin match (target.symbol, target.generic, target.primitive) with
      | _, _, Some constr ->
          Rewriter.return
            (Some
               (Primitive (constr, Some (solution.parameter_types, solution.return_type))))
      | Some symbol, _, _ ->
          Rewriter.return (Some (Symbol (target.name, symbol, Some solution.return_type)))
      | _, Some generic, _ when not (List.is_empty generic.signature.field_formals) ->
          resolve_implicitly ~return_type:(Some solution.return_type) target.name
      | _, Some generic, _ ->
          resolve_generic_winner ~loc ~args ~expected ~contextual arguments generic target
            instance solution
      | _ -> Error.internal_error loc "Missing overload target"
      end
  | [], [] -> resolve_single_generic ()
  | _ ->
      let* speculative = is_speculative in
      if speculative && not (List.is_empty deferred) then Rewriter.return None
      else if List.length targets = 1 then resolve_single_generic ()
      else
        ambiguous_overload_error loc (QualIdent.unqualify name)
          (List.length deferred + List.length winners)

let resolve_opt ~check_expr ~claimed_location ~loc ~name ~args ~expected
    ?(only_calls = false) ?(contextual = false) () =
  let open Rewriter.Syntax in
  let* ordinary = Rewriter.resolve_and_find_candidates name in
  let* imported = Rewriter.find_import_targets name in
  let primitive =
    match primitive_operator name with
    | Some Finset when List.length args > 1 ->
        if List.is_empty ordinary && List.is_empty imported then finset_arity_error loc;
        None
    | primitive -> primitive
  in
  if List.is_empty ordinary && List.is_empty imported && Option.is_some primitive then
    Rewriter.return (Option.map primitive ~f:(fun constr -> Primitive (constr, None)))
  else
    let* generic_names = generic_names ~ordinary ~imported name in
    let* generics = discover_generics generic_names in
    if
      List.length ordinary > 1
      || (not (List.is_empty generics))
      || Option.is_some primitive
    then
      resolve_overloaded ~check_expr ~claimed_location ~loc ~name ~args ~expected
        ~contextual ordinary generics primitive
    else
      match ordinary with
      | [ (name, symbol) ] -> Rewriter.return (Some (Symbol (name, symbol, None)))
      | _ ->
          let+ symbol =
            ImplicitInstantiation.resolve_or_implicit_opt name ~on_miss:(fun () ->
                let candidate =
                  match imported with [ candidate ] -> candidate | _ -> name
                in
                ImplicitInstantiation.try_resolve_implicit_instantiation ~check_expr
                  ~claimed_location ~loc ~qual_ident:candidate ~arg_exprs:args ~only_calls
                  ~expected_typ:expected ())
          in
          Option.map symbol ~f:(fun (name, symbol) -> Symbol (name, symbol, None))
