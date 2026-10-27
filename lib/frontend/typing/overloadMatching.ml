(** Pairs the overloaded functions of an interface with the functions of a module that
    implement them, by their parameter types, and renames the interface's members to the
    module's, together with the instances that the interface created implicitly. *)

open Base
open Ast
open TypingMonad
open TypingErrors

type context = {
  mod_qual_ident : qual_ident;
  own_instrs : Module.module_instr list;
  own_symbols : Module.symbol Map.M(Ident).t;
  parent_instrs : Module.module_instr list;
}
(** What names are resolved against besides the symbol table: the members of the module
    [mod_qual_ident], with its formals, and of the interface it implements. *)

(** The members [instrs] of the module [prefix], each with its qualified name. *)
let qualify_members prefix instrs =
  List.filter_map instrs ~f:(function
    | Module.SymbolDef symbol ->
        let name = Symbol.to_name symbol in
        Some (QualIdent.from_ident name, QualIdent.to_list (QualIdent.append prefix name))
    | Import _ -> None)

(** The module that the instance [mi] stands for, with its name. *)
let instance_module (mi : Module.module_inst) =
  let open Rewriter.Syntax in
  let target =
    match mi.mod_inst_def with
    | Some (Module.Alias target) -> target
    | Some (Apply _ | CanonicalApply _ | ApplyUnit _) | None -> mi.mod_inst_type
  in
  let+ found = CandidateTypes.lookup target in
  Option.bind found ~f:(fun (target_qi, target_symbol) ->
      Rewriter.Symbol.extract target_symbol ~f:(fun _ subst -> function
        | Module.ModDef md -> Some (target_qi, subst, md)
        | _ -> None))

(** The member at [path] among [instrs], the members of the module [prefix], looking
    through module instances to their modules. *)
let rec local_lookup prefix instrs path =
  let open Rewriter.Syntax in
  match path with
  | [] -> Rewriter.return None
  | name :: rest ->
      let symbol =
        List.find_map instrs ~f:(function
          | Module.SymbolDef symbol when Ident.equal (Symbol.to_name symbol) name ->
              Some symbol
          | _ -> None)
      in
      begin match symbol with
      | None -> Rewriter.return None
      | Some symbol ->
          let resolved = QualIdent.append prefix name in
          let symbol =
            match symbol with
            | Module.ModDef md when Option.is_none md.mod_decl.mod_decl_rep ->
                let rep =
                  List.find_map md.mod_def ~f:(function
                    | Module.SymbolDef (TypeDef td) when td.type_def_rep ->
                        Some td.type_def_name
                    | _ -> None)
                in
                Module.ModDef
                  { md with mod_decl = { md.mod_decl with mod_decl_rep = rep } }
            | symbol -> symbol
          in
          begin match (symbol, rest) with
          | Module.ModInst mi, [] ->
              let+ target = instance_module mi in
              Option.map target ~f:(fun (target_qi, _, md) ->
                  ( resolved,
                    ( resolved,
                      Module.ModDef md,
                      (false, true, [ (target_qi, QualIdent.to_list resolved) ]) ) ))
          | _, [] ->
              Rewriter.return
                (Some
                   ( resolved,
                     (resolved, symbol, (false, false, qualify_members prefix instrs)) ))
          | Module.ModDef md, _ -> local_lookup resolved md.mod_def rest
          | Module.ModInst mi, _ ->
              let* target = instance_module mi in
              begin match target with
              | None -> Rewriter.return None
              | Some (target_qi, subst, md) ->
                  let+ found = local_lookup resolved md.mod_def rest in
                  Option.map found ~f:(fun (qi, (name, symbol, (_, _, substitutions))) ->
                      ( qi,
                        ( name,
                          symbol,
                          ( false,
                            true,
                            (target_qi, QualIdent.to_list resolved)
                            :: List.map substitutions ~f:(fun (from, dest) ->
                                (subst from, dest)) ) ) ))
              end
          | _ -> Rewriter.return None
          end
      end

(** Resolves [qi] against the module's members, the symbol table, and the interface's
    members. *)
let lookup ctx qi =
  let open Rewriter.Syntax in
  let path = QualIdent.to_list qi in
  let prefix = QualIdent.to_list ctx.mod_qual_ident in
  let is_qualified = List.is_prefix path ~prefix ~equal:Ident.equal in
  let path = if is_qualified then List.drop path (List.length prefix) else path in
  match path with
  | name :: _ when Map.mem ctx.own_symbols name ->
      local_lookup ctx.mod_qual_ident ctx.own_instrs path
  | _ ->
      let* found = CandidateTypes.lookup qi in
      begin match found with
      | Some _ -> Rewriter.return found
      | None ->
          local_lookup ctx.mod_qual_ident
            (List.filter ctx.parent_instrs ~f:(function
              | Module.SymbolDef (ModInst _) -> false
              | _ -> true))
            path
      end

let normalize ctx typ =
  let open Rewriter.Syntax in
  let+ normalized = CandidateTypes.normalize ~lookup:(lookup ctx) typ in
  match normalized with
  | Ok typ -> typ
  | Error _ -> overloaded_interface_type_error (Type.to_loc typ) typ

(** [qi] with the instance it lies in renamed by [instances]. *)
let rename_instance instances qi =
  let replacement =
    Map.to_alist instances
    |> List.find ~f:(fun (source, _) ->
        List.is_prefix (QualIdent.to_list qi) ~prefix:(QualIdent.to_list source)
          ~equal:Ident.equal)
  in
  match replacement with
  | None -> qi
  | Some (source, target) -> QualIdent.requalify [ (source, QualIdent.to_list target) ] qi

(** Whether [functor_qi] names a module with a rep type, which its applications stand for.
*)
let has_rep_type ctx functor_qi =
  let open Rewriter.Syntax in
  let+ found = lookup ctx functor_qi in
  match found with
  | Some (_, symbol) ->
      Rewriter.Symbol.extract symbol ~f:(fun _ _ -> function
        | Module.ModDef { mod_decl = { mod_decl_rep = Some _; _ }; _ } -> true
        | _ -> false)
  | None -> false

let formal_accepts_type_argument (formal : Module.module_inst) =
  let open Rewriter.Syntax in
  let* rep = lift (ProgUtils.resolve_rep_ident formal.mod_inst_type) in
  match rep with
  | None -> Rewriter.return false
  | Some (interface_qual_ident, rep_ident) ->
      let+ members =
        lift (ProgUtils.non_rep_abstract_members ~interface_qual_ident ~rep_ident)
      in
      List.is_empty members

let can_wrap_functor_arguments ctx functor_qi =
  let open Rewriter.Syntax in
  let* found = lookup ctx functor_qi in
  match found with
  | Some (_, symbol) ->
      begin match Rewriter.Symbol.orig_symbol symbol with
      | Module.ModDef module_ ->
          Rewriter.List.for_all
            (Module.formals module_.mod_decl)
            ~f:formal_accepts_type_argument
      | _ -> Rewriter.return false
      end
  | None -> Rewriter.return false

let is_nominal_rep_definition rep = function
  | Module.SymbolDef (TypeDef { type_def_name; type_def_expr; _ })
    when Ident.equal type_def_name rep ->
      begin match type_def_expr with
      | None | Some (Type.App (Data _, _, _)) -> true
      | Some _ -> false
      end
  | _ -> false

let module_has_nominal_rep symbol =
  Rewriter.Symbol.extract symbol ~f:(fun _ _ -> function
    | Module.ModDef { mod_decl = { mod_decl_rep = Some rep; _ }; mod_def } ->
        List.exists mod_def ~f:(is_nominal_rep_definition rep)
    | _ -> false)

let inherited_module_argument ctx instances module_qi =
  let open Rewriter.Syntax in
  let module_qi = rename_instance instances module_qi in
  let lookup_renamed qi = lookup ctx (rename_instance instances qi) in
  let* normalized =
    CandidateTypes.normalize ~lookup:lookup_renamed (Type.var module_qi)
  in
  let* nominal_rep =
    let+ found = lookup ctx module_qi in
    Option.value_map found ~default:false ~f:(fun (_, symbol) ->
        module_has_nominal_rep symbol)
  in
  let adapter =
    String.is_prefix
      (Ident.name (QualIdent.unqualify module_qi))
      ~prefix:ProgUtils.tp_mod_ident_prefix
  in
  let+ table = Rewriter.get_table in
  let identity qi = SymbolTbl.identity ~preserve_abstract_owners:true qi table in
  match normalized with
  | Ok (Type.App (Var rep, [], _))
    when QualIdent.is_qualified rep
         && QualIdent.equal (identity (QualIdent.pop rep)) (identity module_qi) ->
      normalized
  | _ when adapter || nominal_rep -> normalized
  | _ -> Error (CandidateTypes.Not_type module_qi)

let inherited_argument_type ctx instances = function
  | Module.TypeArg typ ->
      Rewriter.return
        (Ok (CandidateTypes.rewrite_type ~f:(rename_instance instances) typ))
  | Module.ModArg module_qi -> inherited_module_argument ctx instances module_qi

(** The type application that [mi], a member of the interface, stands for, if the
    interface created it implicitly, with the instances in its arguments renamed by
    [instances]. *)
let inherited_application ctx instances (mi : Module.module_inst) =
  let open Rewriter.Syntax in
  match mi.mod_inst_def with
  | Some (Module.CanonicalApply (functor_qi, args))
    when String.is_prefix (Ident.name mi.mod_inst_name)
           ~prefix:ProgUtils.inst_mod_ident_prefix ->
      let* has_rep_type = has_rep_type ctx functor_qi in
      let* can_wrap_arguments = can_wrap_functor_arguments ctx functor_qi in
      if not (has_rep_type && can_wrap_arguments) then Rewriter.return None
      else
        let+ argument_types =
          Rewriter.List.map args ~f:(inherited_argument_type ctx instances)
        in
        begin match Result.all argument_types with
        | Error _ -> None
        | Ok args ->
            Some
              (Type.App
                 (Type.Var functor_qi, args, Type.mk_attr (Ident.to_loc mi.mod_inst_name)))
        end
  | _ -> Rewriter.return None

(** Normalizes [typ], instantiating types that need it. *)
let rec prepare_type ctx visiting (Type.App (head, args, attr) as typ) =
  let open Rewriter.Syntax in
  let* normalized = CandidateTypes.normalize ~lookup:(lookup ctx) typ in
  match normalized with
  | Ok typ -> Rewriter.return typ
  | Error (CandidateTypes.Needs_instantiation _) ->
      begin match (head, args) with
      | Type.Var _, _ :: _ ->
          let* args = Rewriter.List.map args ~f:(prepare_type ctx visiting) in
          TypeExpr.check (Type.App (head, args, attr))
      | Type.Var qi, [] when not (Set.mem visiting qi) ->
          let* found = lookup ctx qi in
          begin match found with
          | Some (_, symbol) ->
              Rewriter.Symbol.extract symbol ~f:(fun _ requalify -> function
                | Module.TypeDef { type_def_expr = Some definition; _ } ->
                    prepare_type ctx (Set.add visiting qi)
                      (CandidateTypes.rewrite_type ~f:requalify definition)
                | _ -> normalize ctx typ)
          | None -> normalize ctx typ
          end
      | _ ->
          let+ args = Rewriter.List.map args ~f:(prepare_type ctx visiting) in
          Type.App (head, args, attr)
      end
  | Error _ -> normalize ctx typ

(** The normalized parameter types of [call]. *)
let signature ctx call =
  let open Rewriter.Syntax in
  (* Prefers the symbol table, which now has the instances that [prepare_type] created. *)
  let lookup_table_first qi =
    let* found = CandidateTypes.lookup qi in
    match found with Some _ -> Rewriter.return found | None -> lookup ctx qi
  in
  Rewriter.List.map call.Callable.call_decl.call_decl_formals ~f:(fun formal ->
      let* typ = prepare_type ctx (Set.empty (module QualIdent)) formal.var_type in
      let* normalized = CandidateTypes.normalize ~lookup:lookup_table_first typ in
      match normalized with Ok typ -> Rewriter.return typ | Error _ -> normalize ctx typ)

let own_functions mod_def source =
  List.filter_map mod_def ~f:(function
    | Module.SymbolDef (CallDef call)
      when Poly.(Callable.kind call = Func)
           && Ident.equal (Callable.source_ident call) source ->
        Some call
    | _ -> None)

let parent_functions parent_mod_def source =
  List.count parent_mod_def ~f:(function
    | Module.SymbolDef (CallDef call) ->
        Poly.(Callable.kind call = Func)
        && Ident.equal (Callable.source_ident call) source
    | _ -> false)

(** The signatures of the module's functions that implement an overloaded function of the
    interface. *)
let own_signatures ctx mod_def parent_mod_def =
  let open Rewriter.Syntax in
  Rewriter.List.fold_left mod_def
    ~init:(Map.empty (module Ident))
    ~f:(fun signatures -> function
      | Module.SymbolDef (CallDef call) when Poly.(Callable.kind call = Func) ->
          let source = Callable.source_ident call in
          if
            parent_functions parent_mod_def source > 1
            || parent_functions parent_mod_def source = 1
               && List.length (own_functions mod_def source) > 1
          then
            let+ types = signature ctx call in
            Map.set signatures ~key:(Callable.to_ident call) ~data:types
          else Rewriter.return signatures
      | _ -> Rewriter.return signatures)

(** Pairs each overloaded function of the interface [parent_ident] with the module's
    function of the same signature, by name and by qualified name. *)
let match_functions ~(m : Module.t) ~parent_ident ctx mod_def parent_mod_def
    own_signatures =
  let open Rewriter.Syntax in
  Rewriter.List.fold_left parent_mod_def
    ~init:(Map.empty (module Ident), Map.empty (module QualIdent))
    ~f:(fun (matches, remapping) -> function
      | Module.SymbolDef (CallDef parent) when Poly.(Callable.kind parent = Func) ->
          let source = Callable.source_ident parent in
          let candidates = own_functions mod_def source in
          if
            List.is_empty candidates
            || (List.length candidates = 1 && parent_functions parent_mod_def source = 1)
          then Rewriter.return (matches, remapping)
          else begin
            let* parent_signature = signature ctx parent in
            let compatible =
              List.filter candidates ~f:(fun own ->
                  List.equal Type.equal
                    (Map.find_exn own_signatures (Callable.to_ident own))
                    parent_signature)
            in
            let own =
              match compatible with
              | [ own ] -> own
              | [] ->
                  no_overload_implementation_error m.mod_decl.mod_decl_loc source
                    parent_ident
              | _ ->
                  multiple_overload_implementations_error m.mod_decl.mod_decl_loc source
                    parent_ident
            in
            let parent_name = Callable.to_ident parent in
            let own_name = Callable.to_ident own in
            Rewriter.return
              ( Map.set matches ~key:parent_name ~data:own_name,
                Map.set remapping
                  ~key:(QualIdent.append ctx.mod_qual_ident parent_name)
                  ~data:(QualIdent.append ctx.mod_qual_ident own_name) )
          end
      | _ -> Rewriter.return (matches, remapping))

(** Maps the instances that the interface created implicitly to the module's instances of
    the same functor applications. *)
let match_instances ctx =
  let open Rewriter.Syntax in
  Rewriter.List.fold_left ctx.parent_instrs
    ~init:(Map.empty (module QualIdent))
    ~f:(fun instances -> function
      | Module.SymbolDef (ModInst mi) ->
          let* application = inherited_application ctx instances mi in
          begin match application with
          | None -> Rewriter.return instances
          | Some application ->
              let+ prepared =
                prepare_type ctx (Set.empty (module QualIdent)) application
              in
              begin match prepared with
              | Type.App (Var target, [], _) ->
                  Map.set instances
                    ~key:(QualIdent.append ctx.mod_qual_ident mi.mod_inst_name)
                    ~data:(QualIdent.pop target)
              | _ -> instances
              end
          end
      | _ -> Rewriter.return instances)

(** The member [instr] of the interface with its names rewritten by [f]. *)
let rec rewrite_member ~f =
  let open Rewriter.Syntax in
  function
  | Module.SymbolDef (CallDef call) ->
      let+ call = lift (Rewriter.Callable.rewrite_qual_idents ~f call) in
      Module.SymbolDef (CallDef call)
  | Module.SymbolDef (ModDef md) ->
      let+ mod_def = Rewriter.List.map md.mod_def ~f:(rewrite_member ~f) in
      Module.SymbolDef (ModDef { md with mod_def })
  | Module.SymbolDef symbol ->
      let+ symbol = lift (Rewriter.Module.rewrite_qual_idents_in_symbol ~f symbol) in
      Module.SymbolDef symbol
  | instr -> Rewriter.return instr

(** Pairs the overloaded functions of the interface [parent_ident], whose members are
    [parent_mod_def], with the functions of [m] that implement them. Returns the pairing,
    by name, and the interface's members renamed to [m]'s functions and to [m]'s instances
    of the functor applications that the interface instantiated implicitly. *)
let match_overloads ~(m : Module.t) ~(mod_qual_ident : qual_ident)
    ~(mod_def_formals : Module.module_instr list) ~(mod_def : Module.module_instr list)
    ~(parent_ident : qual_ident) (parent_mod_def : Module.module_instr list) =
  let open Rewriter.Syntax in
  let own_instrs = mod_def_formals @ mod_def in
  let own_symbols =
    List.filter_map own_instrs ~f:(function
      | Module.SymbolDef symbol -> Some (Symbol.to_name symbol, symbol)
      | Import _ -> None)
    |> Map.of_alist_reduce (module Ident) ~f:(fun first _ -> first)
  in
  let ctx = { mod_qual_ident; own_instrs; own_symbols; parent_instrs = parent_mod_def } in
  let* instances = match_instances ctx in
  let* parent_mod_def =
    Rewriter.List.map parent_mod_def ~f:(rewrite_member ~f:(rename_instance instances))
  in
  let ctx = { ctx with parent_instrs = parent_mod_def } in
  let* own_signatures = own_signatures ctx mod_def parent_mod_def in
  let* matches, remapping =
    match_functions ~m ~parent_ident ctx mod_def parent_mod_def own_signatures
  in
  let rename_function qi = Map.find remapping qi |> Option.value ~default:qi in
  let+ parent_mod_def =
    Rewriter.List.map parent_mod_def ~f:(rewrite_member ~f:rename_function)
  in
  let instance_subst =
    Map.to_alist instances
    |> List.map ~f:(fun (source, target) -> (source, QualIdent.to_list target))
  in
  (matches, parent_mod_def, instance_subst)
