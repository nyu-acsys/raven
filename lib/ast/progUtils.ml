open Base
open AstDef
open Util

(* Captured before [open Rewriter] below, which brings [Rewriter.Logs] into scope
   unqualified and would otherwise shadow the real logging library here. *)
module Stdlib_logs = Logs

open Rewriter


(* DisambiguationTbl is used in disambiguating local idents in Typing.ProcessCallable.
   Its definition lives in disambiguationTbl.ml, below Rewriter -- see the comment
   there for why. This re-export keeps ProgUtils.DisambiguationTbl working as before. *)
module DisambiguationTbl = DisambiguationTbl

let serialize (s : string) : string =
  let s =
    String.map s ~f:(function
      | '.' -> '_'
      | '[' -> '\''
      | ']' -> '\''
      | '(' -> '*'
      | ')' -> '*'
      | ' ' -> '_'
      (* | '\'' -> '#' *)
      | c -> c)
  in
  s

let frac_field_to_frac_mod_ident ~loc field_name field_tp =
  Ident.make loc (serialize ("Frac$" ^ Ident.to_string field_name)) 0

let frac_field_to_frac_mod_qual_ident ~loc field_name_qi field_tp =
  let frac_mod_ident =
    frac_field_to_frac_mod_ident ~loc
      (QualIdent.unqualify field_name_qi)
      field_tp
  in
  let frac_mod_path = QualIdent.from_list (QualIdent.path field_name_qi) in

  QualIdent.append frac_mod_path frac_mod_ident

let is_field_def_real_heap ~(printers : Rewriter.printers) (fld : AstDef.Module.field_def) : bool =
  Stdlib_logs.debug (fun m ->
      m "ProgUtils.is_field_def_real_heap: fld.field_type: %a" printers.pr_type
        fld.field_type);

  match fld.field_type with
  | App (Fld, [ App (Var qi, [], _) ], _) ->
      let second_last_qi = QualIdent.unqualify (QualIdent.pop qi) in
      Ident.(
        second_last_qi
        = frac_field_to_frac_mod_ident ~loc:Loc.dummy fld.field_name
            fld.field_type)
  | _ -> false

let pred_to_ra_mod_ident ~loc pred_ident =
  Ident.make loc (serialize ("PredHeapRA$" ^ Ident.to_string pred_ident)) 0

let au_to_ra_mod_ident ~loc call_ident =
  Ident.make loc
    (serialize ("AtomicProcHeapRA$" ^ Ident.to_string call_ident))
    0

let callable_au_token_ident ~loc callable_ident =
  Ident.make loc (serialize ("au_token$" ^ Ident.to_string callable_ident)) 0

let find_highest_valid_scope_qi loc (qi : qual_ident) : qual_ident t =
  let open Syntax in
  (*Logs.debug (fun m ->
      m "ProgUtils.find_highest_valid_scope_qi: qi = %a"
        AstDef.QualIdent.pr qi);*)
  let rec find_highest_valid_scope_qi' (qi : qual_ident) : qual_ident t =
    (* starting from the current scope, keeps going up till it reaches an abstract scope. Not ideal, since it does not take into account the actual qual_ident `qi` being looked up. *)
    match qi.qual_path with
    | [] -> return (QualIdent.from_ident AstDef.Predefs.prog_ident)
    | _ ->
        let* current_scope = current_scope in
        if current_scope.scope_is_abstract then return current_scope.scope_id
        else find_highest_valid_scope_qi' (QualIdent.pop current_scope.scope_id)
    (* let* tbl = get_table in
       let scope = SymbolTbl.get_scope_exn (QualIdent.pop qi) tbl in

       if scope.scope_is_abstract then
         return (QualIdent.pop qi)
       else
         find_highest_valid_scope_qi' (QualIdent.pop qi) *)

    (* let* symbol = find_and_reify loc (QualIdent.pop qi) in
       match symbol with
       | ModDef m ->
         (* Logs.debug (fun mm -> mm "ProgUtils.find_highest_valid_scope_qi: Found module definition = %a" AstDef.Module.pr m);
         if m.mod_decl.mod_decl_is_interface || not (Base.List.is_empty m.mod_decl.mod_decl_formals) then
           return (QualIdent.pop qi)
         else
           find_highest_valid_scope_qi' (QualIdent.pop qi) *)

         let qual_base_is_a_formal = Base.List.fold m.mod_decl.mod_decl_formals ~init:false ~f:(fun acc formal -> acc || Ident.equal formal.mod_inst_name qi.qual_base) in
         (* replace with List.exists *)

         if qual_base_is_a_formal then
           return (QualIdent.pop qi)
         else
           find_highest_valid_scope_qi' (QualIdent.pop qi)

       | _ -> Error.error loc "Rewriter.find_highest_valid_scope_qi: Expected module definition." *)
  in

  let* highest_valid_scope = find_highest_valid_scope_qi' qi in

  (*Logs.debug (fun m ->
      m "ProgUtils.find_highest_valid_scope_qi: Found scope = %a"
        AstDef.QualIdent.pr highest_valid_scope);*)
  return highest_valid_scope

let find_highest_valid_scope_type_expr loc (tp : type_expr) :
    qual_ident option t =
  let open Syntax in
  (* Logs.debug (fun m -> m "ProgUtils.find_highest_valid_scope_type_expr: tp = %a" AstDef.Type.pr tp); *)
  let rec find_highest_valid_scope_type_expr' (tp : type_expr) :
      qual_ident list t =
    match tp with
    | App (constr, tp_expr_list, _) ->
        let* valid_scopes_list =
          List.fold_left tp_expr_list ~init:[] ~f:(fun acc tp_expr ->
              let* scopes = find_highest_valid_scope_type_expr' tp_expr in
              return (scopes @ acc))
        in

        let+ valid_scopes_list =
          match constr with
          | Var qi ->
              let+ qi_scope = find_highest_valid_scope_qi loc qi in
              qi_scope :: valid_scopes_list
          | _ -> return valid_scopes_list
        in

        valid_scopes_list
  in

  let+ valid_scopes_list = find_highest_valid_scope_type_expr' tp in

  (* Logs.debug (fun m -> m "ProgUtils.find_highest_valid_scope_type_expr: valid_scopes_list = %a" (Print.pr_list_comma AstDef.QualIdent.pr) valid_scopes_list); *)
  Base.List.fold valid_scopes_list ~init:(Some AstDef.Predefs.prog_qual_ident)
    ~f:(fun qi scope ->
      let open Util.Option.Syntax in
      let rec compute_longer_qi q1 q2 =
        match (q1, q2) with
        | [], _ -> Some q2
        | _, [] -> Some q1
        | x :: xs, y :: ys ->
            if not (Ident.equal x y) then None
            else
              let+ longer_qi = compute_longer_qi xs ys in
              x :: longer_qi
      in

      let* qi_unwrapped = qi in
      let+ new_qi =
        compute_longer_qi
          (QualIdent.to_list qi_unwrapped)
          (QualIdent.to_list scope)
      in

      (* Logs.debug (fun m -> m "ProgUtils.find_highest_valid_scope_type_expr: scope_found = %a" AstDef.QualIdent.pr (QualIdent.from_list new_qi)); *)
      QualIdent.from_list new_qi)

let tp_mod_ident_prefix = "TypeMod$$"

(** Takes a type expression `tp` and introduces a module that implements Library.Type whose rep type T is `tp`. ~f here is expected to be Typing.process_symbol, but it's not hardcoded to prevent recursive dependencies  *)
let intros_type_module ~(loc : location) ?scope
    ~(f : AstDef.Module.symbol -> AstDef.Module.symbol t)
    (tp : AstDef.type_expr) : qual_ident t =
    let open Rewriter.Syntax in
  let mod_decl =
    let mod_name =
      let mod_name_string = tp_mod_ident_prefix ^ AstDef.Type.to_string tp in
      Ident.fresh loc (serialize mod_name_string)
    in

    {
      AstDef.Module.mod_decl_name = mod_name;
      mod_decl_formals = [];
      mod_decl_returns = [ (Predefs.lib_type_mod_qual_ident, []) ];
      mod_decl_interfaces = Set.empty (module QualIdent);
      mod_decl_rep = Some Predefs.lib_type_rep_type_ident;
      mod_decl_is_ra = false;
      mod_decl_is_interface = false;
      mod_decl_status = MachineFree;
      mod_decl_loc = loc;
    }
  in

  let (mod_def : AstDef.Module.module_instr list) =
    [
      SymbolDef (
        TypeDef
          {
            type_def_name = Predefs.lib_type_rep_type_ident;
            type_def_expr = Some tp;
            type_def_rep = true;
            type_def_loc = loc;
            type_def_is_free = false;
          }
      )
    ]
  in

  let symbol = AstDef.Module.ModDef { mod_decl; mod_def } in

  (*Logs.debug (fun m ->
      m "ProgUtils.intros_type_module: symbol = %a" AstDef.Symbol.pr
        symbol);*)

  match scope with
  | None ->
    let+ typ_module_qi = introduce_typecheck_symbol ~loc ~f symbol in
    Stdlib_logs.debug (fun m -> m "ProgUtils.intros_type_module: qi = %a" QualIdent.pr typ_module_qi);
    typ_module_qi
  | Some scope_qi ->
    Stdlib_logs.debug (fun m -> m "ProgUtils.intros_type_module: scope_qual_iden = %a; symbol = %a" QualIdent.pr scope_qi Ident.pr (AstDef.Symbol.to_name symbol));
    let+ typ_module_qi = introduce_typecheck_symbol_at_scope' ~loc symbol scope_qi in

    Stdlib_logs.debug (fun m -> m "ProgUtils.intros_type_module: qi = %a" QualIdent.pr typ_module_qi);
    typ_module_qi

let is_ra_type (tp : AstDef.type_expr) : bool t =
  let open Syntax in
  let rec does_ident_implement_ra module_qident type_ident =
    let* symbol = find module_qident in
    Symbol.extract symbol ~f:(fun _ subst -> function
        | AstDef.Module.ModDef m ->
          return
            (m.mod_decl.mod_decl_is_ra &&
             match m.mod_decl.mod_decl_rep with
             | None -> false
             | Some id -> Ident.(id = type_ident))
        | ModInst mod_inst -> 
          let* is_ra = does_ident_implement_ra mod_inst.mod_inst_type type_ident in
          if is_ra then return true
          else
            (match mod_inst.mod_inst_def with
            | None -> return false
            | Some (mod_inst_def_funct, mod_inst_def_args) ->
                does_ident_implement_ra mod_inst_def_funct type_ident)
        | _ -> return false)
  in
  match tp with
  | App (Var qi, [], _) ->
    does_ident_implement_ra (QualIdent.pop qi) (QualIdent.unqualify qi)
  | _ -> return false

let field_get_ra_qual_iden (field : AstDef.Module.field_def) =
  let field_type =
    match field.field_type with
    | App (Fld, [ tp_expr ], _) -> tp_expr
    | _ ->
        Error.internal_error field.field_loc
          "expected a field definition"
  in
  match field_type with
  | App (Var qual_iden, [], _) -> QualIdent.pop qual_iden
  | _ ->
      Error.internal_error field.field_loc
        "expected the field type to be a type identifier"

let pred_get_ra_qual_iden pred_qual_iden =
  let open Syntax in
  let+ pred_fully_qual_iden =
    resolve pred_qual_iden
  in

  QualIdent.append
    (QualIdent.pop pred_fully_qual_iden)
    (pred_to_ra_mod_ident
       ~loc:(QualIdent.to_loc pred_qual_iden)
       (QualIdent.unqualify pred_fully_qual_iden))

let au_get_ra_qual_iden call_qual_iden =
  let open Syntax in
  let+ call_fully_qual_iden =
    resolve call_qual_iden
  in

  QualIdent.append
    (QualIdent.pop call_fully_qual_iden)
    (au_to_ra_mod_ident
       ~loc:(QualIdent.to_loc call_qual_iden)
       (QualIdent.unqualify call_fully_qual_iden))

let get_ra_rep_type (ra_qual_iden : qual_ident) : type_expr =
  AstDef.Type.mk_var
    (QualIdent.append ra_qual_iden
       (Ident.make (QualIdent.to_loc ra_qual_iden) "T" 0))

let get_ra_id (ra_qual_iden : qual_ident) : qual_ident =
  QualIdent.append ra_qual_iden
    (Ident.make (QualIdent.to_loc ra_qual_iden) "id" 0)

let get_ra_valid_fn_qual_ident (ra_qual_iden : qual_ident) : qual_ident =
  QualIdent.append ra_qual_iden
    (Ident.make (QualIdent.to_loc ra_qual_iden) "valid" 0)

let get_ra_comp_fn_qual_ident (ra_qual_iden : qual_ident) : qual_ident =
  QualIdent.append ra_qual_iden
    (Ident.make (QualIdent.to_loc ra_qual_iden) "comp" 0)

let get_ra_frame_fn_qual_ident (ra_qual_iden : qual_ident) : qual_ident =
  QualIdent.append ra_qual_iden
    (Ident.make (QualIdent.to_loc ra_qual_iden) "frame" 0)

let get_ra_fpu_allowed_qual_ident (ra_qual_iden : qual_ident) : qual_ident =
  QualIdent.append ra_qual_iden
    (Ident.make (QualIdent.to_loc ra_qual_iden) "fpuAllowed" 0)

(* ======================== *)

let field_utils_module_ident field_ident : ident =
  Ident.make (Ident.to_loc field_ident) (serialize ("FieldUtils$" ^ Ident.to_string field_ident)) 0

let pred_utils_module_ident pred_ident : ident =
  Ident.make (Ident.to_loc pred_ident) (serialize ("PredUtils$" ^ Ident.to_string pred_ident)) 0

let au_utils_module_ident callable_ident : ident =
  Ident.make (Ident.to_loc callable_ident) (serialize ("AUUtils$" ^ Ident.to_string callable_ident)) 0

(* ======================== *)

let get_field_utils_module field_name : qual_ident t =
  let open Syntax in
  let+ field_fully_qual_name = resolve field_name in

  QualIdent.make field_fully_qual_name.qual_path
    (field_utils_module_ident field_fully_qual_name.qual_base)

let get_pred_utils_module pred_name : qual_ident t =
  let open Syntax in
  let+ pred_fully_qual_name = resolve pred_name in

  QualIdent.make pred_fully_qual_name.qual_path
    (pred_utils_module_ident pred_fully_qual_name.qual_base)

let get_au_utils_module call_name : qual_ident t =
  let open Syntax in
  let+ call_fully_qual_name = resolve call_name in

  QualIdent.make call_fully_qual_name.qual_path
    (au_utils_module_ident call_fully_qual_name.qual_base)

(* ======================== *)

let heap_utils_rep_type_ident loc = Ident.make loc "T" 0

let get_field_utils_rep_type field_name : qual_ident t =
  let open Syntax in
  let+ field_utils_module = get_field_utils_module field_name in
  QualIdent.append field_utils_module (heap_utils_rep_type_ident (QualIdent.to_loc field_name))

let get_pred_utils_rep_type pred_name : qual_ident t =
  let open Syntax in
  let+ pred_utils_module = get_pred_utils_module pred_name in
  QualIdent.append pred_utils_module (heap_utils_rep_type_ident (QualIdent.to_loc pred_name))

let get_au_utils_rep_type call_name : qual_ident t =
  let open Syntax in
  let+ call_utils_module = get_au_utils_module call_name in
  QualIdent.append call_utils_module (heap_utils_rep_type_ident (QualIdent.to_loc call_name))

(* ======================== *)

let heap_utils_comp_chunk_ident loc = Ident.make loc "heapChunkComp" 0

let get_field_utils_comp field_name : qual_ident t =
  let open Syntax in
  let+ field_utils_module = get_field_utils_module field_name in
  QualIdent.append field_utils_module (heap_utils_comp_chunk_ident (QualIdent.to_loc field_name))

let get_pred_utils_comp pred_name : qual_ident t =
  let open Syntax in
  let+ pred_utils_module = get_pred_utils_module pred_name in
  QualIdent.append pred_utils_module (heap_utils_comp_chunk_ident (QualIdent.to_loc pred_name))

let get_au_utils_comp loc call_name : qual_ident t =
  let open Syntax in
  let+ call_utils_module = get_au_utils_module call_name in
  QualIdent.append call_utils_module (heap_utils_comp_chunk_ident (QualIdent.to_loc call_name))
(* ======================== *)

let heap_utils_frame_chunk_ident loc = Ident.make loc "heapChunkFrame" 0

let get_field_utils_frame field_name : qual_ident t =
  let open Syntax in
  let+ field_utils_module = get_field_utils_module field_name in
  QualIdent.append field_utils_module (heap_utils_frame_chunk_ident (QualIdent.to_loc field_name))

let get_pred_utils_frame pred_name : qual_ident t =
  let open Syntax in
  let+ pred_utils_module = get_pred_utils_module pred_name in
  QualIdent.append pred_utils_module (heap_utils_frame_chunk_ident (QualIdent.to_loc pred_name))

let get_au_utils_frame call_name : qual_ident t =
  let open Syntax in
  let+ call_utils_module = get_au_utils_module call_name in
  QualIdent.append call_utils_module (heap_utils_frame_chunk_ident (QualIdent.to_loc call_name))

(* ======================== *)

let heap_utils_valid_ident loc = Ident.make loc "valid" 0

let get_field_utils_valid field_name : qual_ident t =
  let open Syntax in
  let+ field_utils_module = get_field_utils_module field_name in
  QualIdent.append field_utils_module (heap_utils_valid_ident (QualIdent.to_loc field_name))

let get_pred_utils_valid pred_name : qual_ident t =
  let open Syntax in
  let+ pred_utils_module = get_pred_utils_module pred_name in
  QualIdent.append pred_utils_module (heap_utils_valid_ident (QualIdent.to_loc pred_name))

let get_au_utils_valid call_name : qual_ident t =
  let open Syntax in
  let+ call_utils_module = get_au_utils_module call_name in
  QualIdent.append call_utils_module (heap_utils_valid_ident (QualIdent.to_loc call_name))

(* ======================== *)

let heap_utils_valid_inhale_ident loc = Ident.make loc "validInhale" 0

let get_field_utils_valid_inhale field_name : qual_ident t =
  let open Syntax in
  let+ field_utils_module = get_field_utils_module field_name in
  QualIdent.append field_utils_module (heap_utils_valid_inhale_ident (QualIdent.to_loc field_name))

let get_pred_utils_valid_inhale loc pred_name : qual_ident t =
  let open Syntax in
  let+ pred_utils_module = get_pred_utils_module pred_name in
  QualIdent.append pred_utils_module (heap_utils_valid_inhale_ident (QualIdent.to_loc pred_name))

let get_au_utils_valid_inhale call_name : qual_ident t =
  let open Syntax in
  let+ call_utils_module = get_au_utils_module call_name in
  QualIdent.append call_utils_module (heap_utils_valid_inhale_ident (QualIdent.to_loc call_name))

(* ======================== *)

let heap_utils_heapchunk_compare_ident loc = Ident.make loc "heapChunkCompare" 0

let get_field_utils_heapchunk_compare field_name : qual_ident t =
  let open Syntax in
  let+ field_utils_module = get_field_utils_module field_name in
  QualIdent.append field_utils_module (heap_utils_heapchunk_compare_ident (QualIdent.to_loc field_name))

let get_pred_utils_heapchunk_compare pred_name : qual_ident t =
  let open Syntax in
  let+ pred_utils_module = get_pred_utils_module pred_name in
  QualIdent.append pred_utils_module (heap_utils_heapchunk_compare_ident (QualIdent.to_loc pred_name))

let get_au_utils_heapchunk_compare call_name : qual_ident t =
  let open Syntax in
  let+ call_utils_module = get_au_utils_module call_name in
  QualIdent.append call_utils_module (heap_utils_heapchunk_compare_ident (QualIdent.to_loc call_name))

(* ======================== *)

let heap_utils_id_ident loc = Ident.make loc "id" 0

let get_field_utils_id field_name : expr t =
  let open Syntax in
  let loc = (QualIdent.to_loc field_name) in
  let* field_utils_module = get_field_utils_module field_name in

  let* field = find_and_reify field_name in
  let field_type =
    match field with
    | AstDef.Module.FieldDef { field_type; _ } -> field_type
    | _ ->
        Error.internal_error loc
          "expected a field definition"
  in

  let field_elem_type =
    match field_type with
    | App (Fld, [ tp ], _) -> tp
    | _ -> Error.internal_error loc "expected a field type"
  in

  let id_qual_ident =
    QualIdent.append field_utils_module (heap_utils_id_ident loc)
  in

  return @@ AstDef.Expr.mk_var id_qual_ident ~typ:field_elem_type

let get_pred_utils_id loc pred_name : expr t =
  let open Syntax in
  let loc = QualIdent.to_loc pred_name in
  let* pred_utils_module = get_pred_utils_module pred_name in

  let* pred = find_and_reify pred_name in

  let* pred_elem_type_name = get_pred_utils_rep_type pred_name in

  let pred_elem_type = AstDef.Type.mk_var pred_elem_type_name in

  let id_qual_ident =
    QualIdent.append pred_utils_module (heap_utils_id_ident loc)
  in

  return @@ AstDef.Expr.mk_var id_qual_ident ~typ:pred_elem_type

let get_au_utils_id loc call_name : expr t =
  let open Syntax in
  let loc = (QualIdent.to_loc call_name) in
  let* call_utils_module = get_au_utils_module call_name in

  let* call = find_and_reify call_name in

  let* call_elem_type_name = get_au_utils_rep_type call_name in

  let call_elem_type = AstDef.Type.mk_var call_elem_type_name in

  let id_qual_ident =
    QualIdent.append call_utils_module (heap_utils_id_ident loc)
  in

  return @@ AstDef.Expr.mk_var id_qual_ident ~typ:call_elem_type

(* ======================== *)

let pred_ra_constr_qual_ident loc pred_name =
  let open Syntax in
  let* pred_ra_qual_iden = pred_get_ra_qual_iden pred_name in
  let loc = (QualIdent.to_loc pred_name) in
  let+ pred = find_and_reify pred_name in
  match pred with
  | AstDef.Module.CallDef c -> (
      match c.call_decl.call_decl_kind with
      | Pred ->
          QualIdent.append pred_ra_qual_iden
            AstDef.Predefs.lib_countAgreeRA_constr_ident
      | Invariant ->
          QualIdent.append pred_ra_qual_iden
            AstDef.Predefs.lib_agree_constr_ident
      | _ ->
          Error.internal_error loc
            "expected a predicate definition")
  | _ ->
      Error.internal_error loc
        "expected a predicate definition"

let au_ra_uncommitted_constr_qual_ident loc call_name =
  let open Syntax in
  let+ call_ra_qual_iden = au_get_ra_qual_iden call_name in

  QualIdent.append call_ra_qual_iden
    AstDef.Predefs.lib_atomic_token_uncommitted_constr_ident

let au_ra_committed_constr_qual_ident loc call_name =
  let open Syntax in
  let+ call_ra_qual_iden = au_get_ra_qual_iden call_name in

  QualIdent.append call_ra_qual_iden
    AstDef.Predefs.lib_atomic_token_committed_constr_ident

let pred_ra_count_destr_qual_ident loc pred_name =
  let open Syntax in
  let+ pred_ra_qual_iden = pred_get_ra_qual_iden pred_name in
  QualIdent.append pred_ra_qual_iden
    AstDef.Predefs.lib_countAgreeRA_destr1_ident

let pred_ra_val_destr_qual_ident loc pred_name =
  let open Syntax in
  let* pred_ra_qual_iden = pred_get_ra_qual_iden pred_name in
  let loc = (QualIdent.to_loc pred_name) in
  let+ pred = find_and_reify pred_name in
  match pred with
  | AstDef.Module.CallDef c -> (
      match c.call_decl.call_decl_kind with
      | Pred ->
          QualIdent.append pred_ra_qual_iden
            AstDef.Predefs.lib_countAgreeRA_destr2_ident
      | Invariant ->
          QualIdent.append pred_ra_qual_iden
            AstDef.Predefs.lib_agree_destr1_ident
      | _ ->
          Error.internal_error loc
            "expected a predicate definition")
  | _ ->
      Error.internal_error loc
        "expected a predicate definition"

let pred_in_types pred_name =
  let open Syntax in
  let+ pred = find_and_reify pred_name in

  match pred with
  | AstDef.Module.CallDef c
    when Poly.(
           c.call_decl.call_decl_kind = Pred
           || c.call_decl.call_decl_kind = Invariant) ->
      Base.List.map c.call_decl.call_decl_formals ~f:(fun var_decl ->
          var_decl.var_type)
  | _ ->
      Error.internal_error
        (AstDef.QualIdent.to_loc pred_name)
        "expected a predicate definition"

let pred_out_types pred_name =
  let open Syntax in
  let+ pred = find_and_reify pred_name in

  match pred with
  | AstDef.Module.CallDef c
    when Poly.(
           c.call_decl.call_decl_kind = Pred
           || c.call_decl.call_decl_kind = Invariant) ->
      Base.List.map c.call_decl.call_decl_returns ~f:(fun var_decl ->
          var_decl.var_type)
  | _ ->
      Error.internal_error
        (AstDef.QualIdent.to_loc pred_name)
        "expected a predicate definition"

let pred_heap_type pred_name =
  let open Syntax in
  let* pred_in_types = pred_in_types pred_name in

  let+ pred_rep_type =
    get_pred_utils_rep_type pred_name
  in

  AstDef.Type.mk_map
    (QualIdent.to_loc pred_name)
    (AstDef.Type.mk_prod (QualIdent.to_loc pred_name) pred_in_types)
    (AstDef.Type.mk_var pred_rep_type)

let rec is_expr_pure (expr : expr) : (bool, 'a) t_ext =
  let open Syntax in
  match expr with
  | App (constr, expr_list, _) ->
      let* b1 =
        match constr with
        | Own | AUPred _ | AUPredCommit _ -> return false
        | Var qual_ident -> (
            if AstDef.QualIdent.is_local qual_ident then return true
            else
              let* _, symbol, _ = find qual_ident in
              match symbol with
              | CallDef c -> (
                  match c.call_decl.call_decl_kind with
                  | Func -> return true
                  | _ -> return false)
              | FieldDef _ -> return false
              | VarDef _ | ConstrDef _ | DestrDef _ -> return true
              | _ ->
                  Error.internal_error (AstDef.Expr.to_loc expr)
                    "expected a function or a variable")
        | _ -> return true
      in

      let* expr_list_pure = List.map expr_list ~f:is_expr_pure in
      let b2 = Base.List.fold_left ~init:true expr_list_pure ~f:( && ) in

      return (b1 && b2)
  | Binder (_binder, _var_decls, _trgs, expr, _) -> is_expr_pure expr

let get_data_destrs_from_constr (qual_ident : qual_ident) : qual_ident list t =
  let open Syntax in
  let* symbol =
    find_and_reify qual_ident
  in
  match symbol with
  | AstDef.Module.ConstrDef constr_def -> (
      let tp_name =
        match constr_def.constr_return_type with
        | App (Var qi, _, _) -> qi
        | _ ->
            Error.internal_error
              (AstDef.QualIdent.to_loc qual_ident)
              "expected a variable"
      in

      let* symbol = find_and_reify tp_name in
      match symbol with
      | AstDef.Module.TypeDef { type_def_expr = Some tp_expr; _ } -> (
          match tp_expr with
          | App (Data (_, variant_decls), [], _) -> (
              let variant_decl =
                Base.List.find variant_decls ~f:(fun variant_decl ->
                    Ident.equal variant_decl.variant_name qual_ident.qual_base)
              in

              match variant_decl with
              | None ->
                  Error.internal_error
                    (AstDef.QualIdent.to_loc qual_ident)
                    "expected a variant declaration"
              | Some variant_decl ->
                  return
                    (Base.List.map variant_decl.variant_args ~f:(fun var_decl ->
                         QualIdent.append (QualIdent.pop qual_ident)
                           var_decl.var_name)))
          | _ ->
              Error.internal_error
                (AstDef.QualIdent.to_loc qual_ident)
                "expected a data type")
      | _ ->
          Error.internal_error
            (AstDef.QualIdent.to_loc qual_ident)
            "expected a type definition")
  | _ ->
      Error.internal_error
        (AstDef.QualIdent.to_loc qual_ident)
        "expected a constructor definition"

let rec expr_preds_mentioned (expr : AstDef.Expr.t) :
    (QualIdent.t list, 'a) t_ext =
  let open Syntax in
  match expr with
  | App (Var qual_ident, _, _) -> (
      let+ _, (_, symbol, _) =
        resolve_and_find qual_ident
      in

      match symbol with
      | CallDef c -> (
          match c.call_decl.call_decl_kind with
          | Pred | Invariant -> [ qual_ident ]
          | _ -> [])
      | _ -> [])
  | App (_, expr_list, _) ->
      List.fold_right expr_list ~init:[] ~f:(fun expr acc ->
          let+ expr_predicates = expr_preds_mentioned expr in
          expr_predicates @ acc)
  | Binder (_, _, _, expr, _) -> expr_preds_mentioned expr

let stmt_preds_mentioned (s : AstDef.Stmt.t) : (QualIdent.t list, 'a) t_ext =
  let open Syntax in
  let rec stmt_preds_mentioned (s : AstDef.Stmt.t) : QualIdent.t list t =
    match s.stmt_desc with
    | Block b ->
        let* block_preds = List.map b.block_body ~f:stmt_preds_mentioned in

        return (Base.List.concat block_preds)
    | Loop l ->
        let* prebody_preds = stmt_preds_mentioned l.loop_prebody in
        (* let* test_preds = expr_preds_mentioned l.loop_test in *)
        let* postbody_preds = stmt_preds_mentioned l.loop_postbody in

        (* return (prebody_preds @ test_preds @ postbody_preds) *)
        return (prebody_preds @ postbody_preds)
    | Cond c ->
        (* let* test_preds = expr_preds_mentioned c.cond_test in *)
        let* then_preds = stmt_preds_mentioned c.cond_then in
        let* else_preds = stmt_preds_mentioned c.cond_else in

        (* return (test_preds @ then_preds @ else_preds) *)
        return (then_preds @ else_preds)
    | Basic s -> (
        match s with
        | Spec (_, sp) -> expr_preds_mentioned sp.spec_form
        | Use u -> return [ u.use_name ]
        | _ -> return [])
    | StmtExt _ -> return []
  in

  let* preds_list = stmt_preds_mentioned s in
  let preds_list =
    Base.List.dedup_and_sort preds_list ~compare:QualIdent.compare
  in

  return preds_list

(** If [interface_qi] resolves to a module/interface with a rep type, return its
    qualified name together with the rep type identifier; else [None]. *)
let resolve_rep_ident (interface_qi : qual_ident) : (qual_ident * ident) option t =
  let open Rewriter.Syntax in
  let+ resolved = Rewriter.resolve_and_find_opt interface_qi in
  match resolved with
  | Some (qi, symbol) -> (
      match Rewriter.Symbol.orig_symbol symbol with
      | AstDef.Module.ModDef m -> (
          match m.mod_decl.mod_decl_rep with
          | Some rep_ident -> Some (qi, rep_ident)
          | None -> None)
      | _ -> None)
  | None -> None

(** An interface's abstract members, as far as implicit instantiation is concerned:
    [FieldMember] is the single field it declares, [ModMember] an abstract module
    member. Any other abstract member makes the interface unusable as a field
    parameter's constraint -- a location argument supplies a field and nothing else. *)
type iface_member =
  | FieldMember of AstDef.Module.field_def
  | ModMember of AstDef.Module.module_inst
  | OtherMember of string * ident

let interface_members (interface_qi : qual_ident) : iface_member list t =
  let open Rewriter.Syntax in
  let+ resolved = Rewriter.resolve_and_find_opt interface_qi in
  match resolved with
  | Some (_, symbol) -> (
      match Rewriter.Symbol.orig_symbol symbol with
      | AstDef.Module.ModDef iface ->
          Base.List.filter_map iface.mod_def ~f:(function
            | AstDef.Module.SymbolDef (FieldDef ({ field_alias = None; _ } as fd)) ->
                Some (FieldMember fd)
            | SymbolDef (ModInst ({ mod_inst_def = None; _ } as mi)) ->
                Some (ModMember mi)
            | SymbolDef (FieldDef _ | ModInst _) -> None
            | SymbolDef symbol -> (
                (* Same notion of "must be supplied by an implementer" as
                   [non_rep_abstract_members]; see its comment. *)
                match AstDef.Symbol.free_status symbol with
                | UserFree -> None
                | NotFree | MachineFree -> (
                    match symbol with
                    | TypeDef { type_def_expr = None; _ }
                    | VarDef { var_decl = { var_const = true; _ }; var_init = None; _ }
                    | CallDef
                        {
                          call_def = ProcDef { proc_body = None } | FuncDef { func_body = None };
                          call_decl = { call_decl_kind = Proc | Func | Pred | Invariant; _ };
                          _;
                        } ->
                        Some
                          (OtherMember
                             (AstDef.Symbol.kind symbol, AstDef.Symbol.to_name symbol))
                    | _ -> None))
            | _ -> None)
      | _ -> [])
  | None -> []

(** If [interface_qi] declares exactly one field and no abstract member other than
    module members, return that field together with those module members -- the shape
    a location argument can solve (the field comes from the argument, the module
    members from the field's value type). [None] otherwise. *)
let resolve_field_interface (interface_qi : qual_ident) :
    (AstDef.Module.field_def * AstDef.Module.module_inst list) option t =
  let open Rewriter.Syntax in
  let+ members = interface_members interface_qi in
  let fields =
    Base.List.filter_map members ~f:(function FieldMember fd -> Some fd | _ -> None)
  in
  let others =
    Base.List.filter_map members ~f:(function
      | OtherMember (kind, id) -> Some (kind, id)
      | _ -> None)
  in
  match (fields, others) with
  | [ field ], [] ->
      Some
        ( field,
          Base.List.filter_map members ~f:(function
            | ModMember mi -> Some mi
            | _ -> None) )
  | _ -> None

(** How a functor formal can be solved during implicit instantiation: from the types of
    the arguments, or from a field named by a location argument. *)
type formal_solver =
  | ByRepType of qual_ident * ident
      (** the formal's interface and its rep type *)
  | ByField of qual_ident * AstDef.Module.field_def * AstDef.Module.module_inst list
      (** the formal's interface, its field, and its abstract module members *)

let classify_formal (formal : AstDef.Module.module_inst) : formal_solver option t =
  let open Rewriter.Syntax in
  let* rep = resolve_rep_ident formal.mod_inst_type in
  match rep with
  | Some (interface_qi, rep_ident) -> return (Some (ByRepType (interface_qi, rep_ident)))
  | None ->
      let* resolved = Rewriter.resolve_opt formal.mod_inst_type in
      let interface_qi = Base.Option.value resolved ~default:formal.mod_inst_type in
      let+ field_iface = resolve_field_interface formal.mod_inst_type in
      Base.Option.map field_iface ~f:(fun (field, mod_members) ->
          ByField (interface_qi, field, mod_members))

(** True iff every formal of [mod_decl] can be solved from a use site (see
    [classify_formal]), making the functor eligible for implicit instantiation. *)
let is_generic_functor (mod_decl : AstDef.Module.module_decl) : bool t =
  let open Rewriter.Syntax in
  if Base.List.is_empty mod_decl.mod_decl_formals then Rewriter.return false
  else
    Rewriter.List.for_all mod_decl.mod_decl_formals ~f:(fun formal ->
        let+ solver = classify_formal formal in
        Base.Option.is_some solver)

(** Resolve [qi] and, if it names an uninstantiated generic functor (see
    [is_generic_functor]), return its fully qualified name together with its module
    definition; [None] otherwise -- including when [qi] fails to resolve, doesn't name
    a module, or names an instantiation of such a functor rather than the functor
    itself. *)
let resolve_generic_functor (qi : qual_ident) :
    (qual_ident * AstDef.Module.t) option t =
  let open Rewriter.Syntax in
  let* resolved = Rewriter.resolve_and_find_opt qi in
  match resolved with
  | None -> Rewriter.return None
  | Some (fully_qual_ident, symbol) -> (
      match Rewriter.Symbol.orig_symbol symbol with
      | AstDef.Module.ModDef m when not (Rewriter.Symbol.is_instance symbol) ->
          let+ is_generic = is_generic_functor m.mod_decl in
          if is_generic then Some (fully_qual_ident, m) else None
      | _ -> Rewriter.return None)

let inst_mod_ident_prefix = "GenInst$$"

(** Deterministic name for the module wrapping [tp] as an implementation of
    [interface_qual_ident]. Folds in the interface identity so the same type wrapped
    for two different interfaces doesn't collide/dedup. *)
let rep_module_name_string ~(interface_qual_ident : qual_ident) (tp : AstDef.type_expr) :
    string =
  tp_mod_ident_prefix ^ QualIdent.to_string interface_qual_ident ^ "$$"
  ^ AstDef.Type.to_string tp

(** Like [intros_type_module], generalized to an arbitrary rep-typed interface: wraps
    [tp] in a fresh module implementing [interface_qual_ident] with rep type [tp]. Kept
    separate so [intros_type_module]'s existing [Library.Type]-only callers are
    unaffected. *)
let intros_rep_module ~(loc : location) ?scope
    ~(f : AstDef.Module.symbol -> AstDef.Module.symbol t)
    ~(interface_qual_ident : qual_ident) ~(rep_ident : ident) (tp : AstDef.type_expr) :
    qual_ident t =
  let mod_decl =
    let mod_name =
      Ident.fresh loc (serialize (rep_module_name_string ~interface_qual_ident tp))
    in
    {
      AstDef.Module.mod_decl_name = mod_name;
      mod_decl_formals = [];
      mod_decl_returns = [ (interface_qual_ident, []) ];
      mod_decl_interfaces = Set.empty (module QualIdent);
      mod_decl_rep = Some rep_ident;
      mod_decl_is_ra = false;
      mod_decl_is_interface = false;
      mod_decl_status = MachineFree;
      mod_decl_loc = loc;
    }
  in
  let (mod_def : AstDef.Module.module_instr list) =
    [
      SymbolDef
        (TypeDef
           {
             type_def_name = rep_ident;
             type_def_expr = Some tp;
             type_def_rep = true;
             type_def_loc = loc;
             type_def_is_free = false;
           });
    ]
  in
  let symbol = AstDef.Module.ModDef { mod_decl; mod_def } in
  match scope with
  | None -> introduce_typecheck_symbol ~loc ~f symbol
  | Some scope_qi -> introduce_typecheck_symbol_at_scope' ~loc symbol scope_qi

let largest_common_prefix_qi symbols =
    begin match Set.count ~f:(fun _ -> true) symbols with
        | 0 -> Predefs.prog_qual_ident
        | 1 -> Set.choose symbols |> Base.Option.value_exn |> QualIdent.pop
        | _ -> 
          (* pop the type ident from an arbitrary element; $Prog.M.Typ -> $Prog.M *)
          let initial_qi = QualIdent.pop (Set.choose_exn symbols) in
          
          let largest_common_prefix_qi = 
            Set.fold symbols ~init:initial_qi ~f:(fun accum qi ->
                let rec common_prefix accum (l1: ident list) (l2: ident list) =
                  match l1, l2 with
                  | [], _ | _, [] -> accum
                  | q1 :: l1, q2 :: l2 when Ident.(q1 = q2) ->
                    common_prefix (accum @ [q1]) l1 l2
                  | q1 :: l1, q2 :: l2->
                    accum
                
                in
                QualIdent.from_list (common_prefix [] (QualIdent.to_list accum) (QualIdent.to_list qi))
            )
          in

          largest_common_prefix_qi
        end

(** Compute (insertion_scope, reference_scope) for the modules synthesized when
    instantiating a functor whose arguments mention [symbols]: where to introduce them,
    and how to reference them from here. The two differ when [symbols] are reached
    through an abstract parameter. *)
let find_insertion_scope_for_symbols (symbols : (qual_ident, _) Set.t) :
    (qual_ident * qual_ident) t =
  let open Rewriter.Syntax in
  let largest_prefix = largest_common_prefix_qi symbols in
  (* [qi] may sit behind several nested abstract parameters (e.g. [ForkJoin.R.Result]),
     so keep popping and re-resolving until we land on a concrete scope. *)
  let rec find_concrete_scope (qi : qual_ident) : (qual_ident * qual_ident) t =
    let* result = Rewriter.resolve_and_find_opt qi in
    match result with
    | None ->
        Error.internal_error Loc.dummy
          "could not find a concrete scope for these type arguments"
    | Some (qi, (name, symbol, _)) ->
        let resolves_through_abstract_param =
          match symbol with
          | AstDef.Module.ModDef md ->
              md.mod_decl.mod_decl_is_interface && not (QualIdent.equal name qi)
          | _ -> false
        in
        if resolves_through_abstract_param then find_concrete_scope (QualIdent.pop qi)
        else Rewriter.return (name, qi)
  in
  find_concrete_scope largest_prefix

let type_symbols (tps : AstDef.type_expr list) : (qual_ident, _) Set.t =
  Base.List.fold tps
    ~init:(Set.empty (module QualIdent))
    ~f:(fun acc tp -> Set.union acc (AstDef.Type.symbols tp))

(** [find_insertion_scope_for_symbols] for a functor applied to bare types. *)
let find_insertion_scope_for_types (tps : AstDef.type_expr list) :
    (qual_ident * qual_ident) t =
  find_insertion_scope_for_symbols (type_symbols tps)

(** If [tp] is exactly `<M>.<rep_ident>` for some already-resolved module [M] that
    is fully instantiated and genuinely implements [interface_qual_ident] (not just
    a bare rep type), return [M]'s qualified name. Used by [get_or_intros_rep_module]
    to reuse an existing, fully-implemented module instead of synthesizing a
    rep-type-only stub for it -- synthesizing one would be unsound whenever
    [interface_qual_ident] requires more than a rep type (e.g. a resource algebra's
    [valid]/[comp]/etc.), since the stub is [MachineFree] and leaves every member
    beyond the rep type completely unconstrained. *)
let existing_module_for_rep_type ~(interface_qual_ident : qual_ident)
    ~(rep_ident : ident) (tp : AstDef.type_expr) : qual_ident option t =
  let open Rewriter.Syntax in
  match tp with
  | App (Var qi, [], _)
    when Ident.equal (QualIdent.unqualify qi) rep_ident
         && not (Base.List.is_empty (QualIdent.path qi)) -> (
      let mod_qi = QualIdent.pop qi in
      let* resolved = Rewriter.resolve_and_find_opt mod_qi in
      match resolved with
      | None -> return None
      | Some (mod_qi, mod_symbol) ->
          let interfaces, mod_is_instance =
            Rewriter.Symbol.extract mod_symbol ~f:(fun is_instance _subst -> function
              | AstDef.Module.ModDef mod_def ->
                  ( mod_def.mod_decl.mod_decl_interfaces,
                    Base.List.is_empty mod_def.mod_decl.mod_decl_formals || is_instance )
              | _ -> (Set.empty (module QualIdent), true))
          in
          if
            mod_is_instance
            && (QualIdent.equal mod_qi interface_qual_ident
               || Set.mem interfaces interface_qual_ident)
          then return (Some mod_qi)
          else return None)
  | _ -> return None

(** Names (with their symbol kind, e.g. "value"/"function") of [interface_qual_ident]'s
    abstract members other than its rep type [rep_ident] -- the members a bare type
    argument can never supply. Empty for interfaces that consist of nothing but a rep
    type (e.g. [Type]), which is exactly the case [intros_rep_module] is sound for;
    non-empty for interfaces like [ResourceAlgebra] that also require operations
    ([id]/[valid]/[comp]/...). Used to reject [intros_rep_module]'s stub before it is
    even created, rather than letting it fail later, confusingly, when the stub is
    found to still have those members abstract.

    Looks at the interface's members as originally declared (via
    [Rewriter.Symbol.orig_symbol], not [Rewriter.Symbol.reify]): reifying a symbol
    reached through a non-trivial substitution unconditionally marks every [CallDef] it
    contains as machine-free (see [Rewriter.Symbol.reify]), which would hide exactly the
    operations ([comp], [valid], ...) this check exists to find.

    A member counts as "must be supplied" unless its [free_status] is [UserFree] --
    i.e. unless the source explicitly wrote `free` on it. [NotFree] (never marked free)
    and [MachineFree] both count: the entire standard library is force-marked
    [MachineFree] wholesale so it isn't re-verified per program (see the comment on
    [un_free_inherited] in [Typing.ProcessModule.process_module]), which is
    indistinguishable, per member, from genuine freeness unless [UserFree] is checked
    for specifically. [Lemma]-kind callables (axioms) are excluded unconditionally: an
    interface's axioms never need to be supplied by an implementer, regardless of how
    they're marked. *)
let non_rep_abstract_members ~(interface_qual_ident : qual_ident) ~(rep_ident : ident) :
    (string * ident) list t =
  let open Rewriter.Syntax in
  let+ _, symbol = Rewriter.resolve_and_find interface_qual_ident in
  match Rewriter.Symbol.orig_symbol symbol with
  | AstDef.Module.ModDef iface ->
      Base.List.filter_map iface.mod_def ~f:(function
        | AstDef.Module.SymbolDef symbol
          when (match AstDef.Symbol.free_status symbol with
               | UserFree -> false
               | NotFree | MachineFree -> true)
          -> (
            match symbol with
            | TypeDef { type_def_name; type_def_expr = None; _ }
              when not (Ident.equal type_def_name rep_ident) ->
                Some (AstDef.Symbol.kind symbol, type_def_name)
            | ModInst { mod_inst_name; mod_inst_def = None; _ } ->
                Some (AstDef.Symbol.kind symbol, mod_inst_name)
            | VarDef { var_decl = { var_const = true; var_name; _ }; var_init = None; _ } ->
                Some (AstDef.Symbol.kind symbol, var_name)
            | CallDef
                {
                  call_def = ProcDef { proc_body = None } | FuncDef { func_body = None };
                  call_decl = { call_decl_kind = Proc | Func | Pred | Invariant; _ };
                  _;
                } ->
                Some (AstDef.Symbol.kind symbol, AstDef.Symbol.to_name symbol)
            | _ -> None)
        | _ -> None)
  | _ -> []

(** Get the module wrapping [tp] as an implementation of [interface_qual_ident]
    (with rep type [rep_ident]): reuses an existing module already implementing
    [interface_qual_ident] if [tp] happens to be exactly its rep type (see
    [existing_module_for_rep_type]), else an existing wrapper at the deterministic
    name (see [rep_module_name_string]) already in scope, else creates one via
    [intros_rep_module]. [insert_scope]/[reference_scope] are as computed by
    [find_insertion_scope_for_types]. *)
let get_or_intros_rep_module ~(loc : location)
    ~(f : AstDef.Module.symbol -> AstDef.Module.symbol t)
    ~(insert_scope : qual_ident) ~(reference_scope : qual_ident)
    ~(interface_qual_ident : qual_ident) ~(rep_ident : ident)
    (tp : AstDef.type_expr) : qual_ident t =
  let open Rewriter.Syntax in
  let* existing = existing_module_for_rep_type ~interface_qual_ident ~rep_ident tp in
  match existing with
  | Some mod_qi -> return mod_qi
  | None ->
      let canonical_qi =
        QualIdent.append reference_scope
          (Ident.make loc (serialize (rep_module_name_string ~interface_qual_ident tp)) 0)
      in
      let* resolve_result = Rewriter.resolve_opt canonical_qi in
      match resolve_result with
      | Some _ -> return canonical_qi
      | None ->
          let* missing = non_rep_abstract_members ~interface_qual_ident ~rep_ident in
          let* () =
            match missing with
            | [] -> return ()
            | _ :: _ ->
                let* printers = Rewriter.current_printers in
                let missing_str =
                  Base.List.map missing ~f:(fun (kind, id) ->
                      Printf.sprintf "%s `%s`" kind (Ident.to_string id))
                  |> String.concat ~sep:", "
                in
                Error.type_error loc
                  (Printf.sprintf
                     !"`%s` cannot be used here as a type argument: interface \
                       %{QualIdent} requires more than a representation type -- it also \
                       declares %s, which a bare type does not supply. Pass a module \
                       that implements %{QualIdent} instead of a type here"
                     (Print.string_of_format printers.pr_type tp) interface_qual_ident
                     missing_str interface_qual_ident)
          in
          intros_rep_module ~loc ~scope:insert_scope ~f ~interface_qual_ident ~rep_ident tp

(** Deterministic name for the module standing for [field_qi] as an implementation of
    [interface_qual_ident]. Keyed on (interface, field) rather than on types: two
    fields of the same type are different arguments. *)
let field_module_name_string ~(interface_qual_ident : qual_ident)
    (field_qi : qual_ident) : string =
  "FieldMod$$" ^ QualIdent.to_string interface_qual_ident ^ "$$"
  ^ QualIdent.to_string field_qi

(** The field counterpart of [get_or_intros_rep_module]: get (or create) a module
    implementing [interface_qual_ident] whose field stands for [field_qi]. The manifest
    field is what makes this sound -- the adapter's field *is* the client's, so it keys
    on the same heap rather than getting one of its own. [mod_bindings] supplies the
    interface's abstract module members, solved by the caller from [field_qi]'s type. *)
let get_or_intros_field_module ~(loc : location)
    ~(insert_scope : qual_ident) ~(reference_scope : qual_ident)
    ~(interface_qual_ident : qual_ident) ~(field : AstDef.Module.field_def)
    ~(field_qi : qual_ident) ~(field_type : AstDef.type_expr)
    (mod_bindings : (ident * qual_ident) list) : qual_ident t =
  let open Rewriter.Syntax in
  let mod_ident =
    Ident.make loc
      (serialize (field_module_name_string ~interface_qual_ident field_qi))
      0
  in
  let canonical_qi = QualIdent.append reference_scope mod_ident in
  let* resolve_result = Rewriter.resolve_opt canonical_qi in
  match resolve_result with
  | Some _ -> return canonical_qi
  | None ->
      let mod_decl =
        {
          AstDef.Module.mod_decl_name = mod_ident;
          mod_decl_formals = [];
          mod_decl_returns = [ (interface_qual_ident, []) ];
          mod_decl_interfaces = Set.empty (module QualIdent);
          mod_decl_rep = None;
          mod_decl_is_ra = false;
          mod_decl_is_interface = false;
          mod_decl_status = MachineFree;
          mod_decl_loc = loc;
        }
      in
      let mod_defs =
        Base.List.map mod_bindings ~f:(fun (member_ident, target) ->
            AstDef.Module.SymbolDef
              (ModInst
                 {
                   mod_inst_name = member_ident;
                   mod_inst_type = target;
                   mod_inst_def = Some (target, []);
                   mod_inst_is_interface = false;
                   mod_inst_is_free = false;
                   mod_inst_loc = loc;
                 }))
        @ [
            AstDef.Module.SymbolDef
              (FieldDef
                 {
                   field with
                   field_type;
                   field_alias = Some field_qi;
                   field_loc = loc;
                 });
          ]
      in
      let symbol = AstDef.Module.ModDef { mod_decl; mod_def = mod_defs } in
      let+ _ =
        Rewriter.introduce_typecheck_symbol_at_scope' ~loc symbol insert_scope
      in
      canonical_qi

(** Get or create (and typecheck) the instantiation of [functor_qual_ident] at
    [arg_module_qis]. [inst_key] distinguishes one instantiation from another and is
    what the derived name is built from, so it must determine the arguments: the
    argument types for the type-argument path, the argument fields for the field path.

    Split out from [instantiate_type_functor] because the two paths differ only in how
    they arrive at the argument modules and the key. *)
let instantiate_functor_at_modules ~(loc : location)
    ~(functor_qual_ident : qual_ident)
    ~(functor_mod_decl : AstDef.Module.module_decl) ~(insert_scope : qual_ident)
    ~(reference_scope : qual_ident) ~(inst_key : string)
    (arg_module_qis : qual_ident list) : qual_ident t =
  let open Rewriter.Syntax in
  let inst_mod_ident =
    let mod_name_string =
      inst_mod_ident_prefix
      ^ AstDef.Ident.to_string functor_mod_decl.mod_decl_name
      ^ "$$" ^ inst_key
    in
    Ident.make loc (serialize mod_name_string) 0
  in
  let inst_qi = QualIdent.append reference_scope inst_mod_ident in
  let* resolve_result = Rewriter.resolve_opt inst_qi in
  match resolve_result with
  | Some _ -> return inst_qi
  | None ->
      let functor_inst =
        AstDef.Module.ModInst
          {
            mod_inst_name = inst_mod_ident;
            mod_inst_type = functor_qual_ident;
            mod_inst_def =
              Some
                ( functor_qual_ident,
                  Base.List.map arg_module_qis ~f:(fun qi ->
                      AstDef.Module.ModArg qi) );
            mod_inst_is_interface = false;
            mod_inst_is_free = false;
            mod_inst_loc = loc;
          }
      in
      let+ _ =
        Rewriter.introduce_typecheck_symbol_at_scope' ~loc functor_inst insert_scope
      in
      inst_qi

(** Get or create (and typecheck) the instantiation
    [functor_qual_ident][arg_types...] -- the generalized, functor-agnostic
    primitive behind any surface syntax that instantiates a generic module
    (explicit `module M = F[args]`, `M[args]` written directly in type position,
    or an extension building an instantiation of its own, e.g. `ProphecyExt`'s
    `Library.List[T]`; see its doc comment). Every formal of [functor_mod_decl]
    must be constrained by a rep-typed module/interface. Each argument type is
    wrapped via [intros_rep_module] (deduplicated), then handed to
    [instantiate_functor_at_modules]. Returns the instantiation's qualified name. *)
let instantiate_type_functor ~(loc : location)
    ~(f : AstDef.Module.symbol -> AstDef.Module.symbol t)
    ~(functor_qual_ident : qual_ident)
    ~(functor_mod_decl : AstDef.Module.module_decl)
    (arg_types : AstDef.type_expr list) : qual_ident t =
  let open Rewriter.Syntax in
  if
    Base.List.length arg_types <> Base.List.length functor_mod_decl.mod_decl_formals
  then
    Error.internal_error loc
      "wrong number of type arguments for this functor instantiation"
  else
    (* Canonicalize via [expand_type_expr] before deriving the instantiation's name
       below: callers can reach here with an argument type either written as a type
       alias (e.g. a functor called directly from a type position) or already
       expanded (e.g. inferred from a call's argument, expanded during unification
       against the functor's formals) -- without normalizing both to the same form
       first, the same semantic type argument would name two different, mutually
       incompatible instantiations. *)
    let* arg_types =
      Rewriter.List.map arg_types ~f:(fun tp -> !Rewriter.expand_type_expr_ref tp)
    in
    let* insert_scope, reference_scope = find_insertion_scope_for_types arg_types in
    let* arg_module_qis =
      Rewriter.List.map2_exn functor_mod_decl.mod_decl_formals arg_types
        ~f:(fun formal tp ->
          let* rep = resolve_rep_ident formal.mod_inst_type in
          match rep with
          | None ->
              Error.internal_error loc
                (Printf.sprintf
                   !"formal %{Ident}'s constraint %{QualIdent} has no rep type"
                   formal.mod_inst_name formal.mod_inst_type)
          | Some (interface_qual_ident, rep_ident) ->
              get_or_intros_rep_module ~loc ~f ~insert_scope ~reference_scope
                ~interface_qual_ident ~rep_ident tp)
    in
    let inst_key =
      String.concat ~sep:"," (Base.List.map arg_types ~f:AstDef.Type.to_string)
    in
    instantiate_functor_at_modules ~loc ~functor_qual_ident ~functor_mod_decl
      ~insert_scope ~reference_scope ~inst_key arg_module_qis

(** The converse of [instantiate_type_functor] for a single-type-argument functor:
    recognizes whether [tp] is the rep type of a module instantiated from
    [functor_qual_ident] -- i.e. [tp] has the shape [M.T] where [M] is
    `module M = functor_qual_ident[_]`, however [M] is named or wherever it was
    introduced (by a user, or by [instantiate_type_functor] itself) -- and if so
    returns that instantiation's own argument type. Checked structurally, off the
    instantiation's own recorded [mod_inst_def], rather than by any naming
    convention, so it recognizes any such module uniformly. Only handles a functor
    with exactly one `[T: Type]`-shaped argument; extend the return type to a full
    [module_inst_arg list] if a multi-argument caller ever needs this.

    Type-checking-time use only: [find]/[Symbol.extract] hand back a [ModInst] with
    [mod_inst_def] intact only while the declaration is still live as such. By the
    rewrite phase, name resolution on an instantiation's own qual_ident answers with
    the [ModDef] it was elaborated into instead (needed for ordinary member access,
    but no longer carrying which functor produced it) -- so a rewrite-time caller
    trying to recover a not-yet-known argument type this way will always get [None],
    silently. Recover it from wherever it was already computed and thread it through
    instead of trying to re-derive it at rewrite time in the first place; see
    ProphecyExt.ProphResource's own doc comment for a worked example of exactly this
    trap, and why. *)
let instantiation_arg (functor_qual_ident : qual_ident) (tp : AstDef.type_expr) :
    AstDef.type_expr option t =
  let open Rewriter.Syntax in
  match tp with
  | AstDef.Type.App (Var rep_type_qi, [], _) -> (
      let mod_qi = QualIdent.pop rep_type_qi in
      (* [find], not [find_and_reify]/[find_and_reify_module]: those reify a
         [ModInst] into the [ModDef] it expands to, which is what's wanted almost
         everywhere else but loses exactly the [mod_inst_def] provenance this
         needs. [Symbol.extract] is the primitive that hands back the raw,
         unreified symbol -- the same one [DecreasesExt.does_module_implement_wf_order]
         uses to walk a [ModInst] chain for the same reason. *)
      let* symbol = Rewriter.find mod_qi in
      Rewriter.Symbol.extract symbol ~f:(fun _ _ sym ->
        match sym with
        | AstDef.Module.ModInst
            { mod_inst_def = Some (f_qi, [ AstDef.Module.ModArg arg_qi ]); _ }
          when QualIdent.(f_qi = functor_qual_ident) ->
            return
              (Some
                 (AstDef.Type.mk_var ~loc:(QualIdent.to_loc rep_type_qi)
                    (QualIdent.append arg_qi AstDef.Predefs.lib_type_rep_type_ident)))
        | _ -> return None))
  | _ -> return None
