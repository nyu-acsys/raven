open Base
open AstDef
open Util
open Rewriter

let serialize (s : string) : string =
  let s =
    String.map s ~f:(function
      | '.' -> '_'
      | '[' -> '-'
      | ']' -> '-'
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

let is_field_def_real_heap (fld : AstDef.Module.field_def) : bool =
  Logs.debug (fun m ->
      m "ProgUtils.is_field_def_real_heap: fld.field_type: %a" AstDef.Type.pr
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

(** Takes a type expression `tp` and introduces a module that implements Library.Type whose rep type T is `tp`. ~f here is expected to be Typing.process_symbol, but it's not hardcoded to prevent recursive dependencies  *)
let intros_type_module ~(loc : location)
    ~(f : AstDef.Module.symbol -> AstDef.Module.symbol t)
    (tp : AstDef.type_expr) : qual_ident t =
  let mod_decl =
    let mod_name =
      let mod_name_string = AstDef.Type.to_string tp ^ "$Type_Mod" in
      Ident.fresh loc (serialize mod_name_string)
    in

    {
      AstDef.Module.mod_decl_name = mod_name;
      mod_decl_formals = [];
      mod_decl_returns = Some Predefs.lib_type_mod_qual_ident;
      mod_decl_interfaces = Set.empty (module QualIdent);
      mod_decl_rep = Some Predefs.lib_type_rep_type_ident;
      mod_decl_is_ra = false;
      mod_decl_is_interface = false;
      mod_decl_is_free = true;
      mod_decl_loc = loc;
    }
  in

  let (mod_def : AstDef.Module.module_instr list) =
    [
      SymbolDef
        (TypeDef
           {
             type_def_name = Predefs.lib_type_rep_type_ident;
             type_def_expr = Some tp;
             type_def_rep = true;
             type_def_loc = loc;
           });
    ]
  in

  let symbol = AstDef.Module.ModDef { mod_decl; mod_def } in

  (*Logs.debug (fun m ->
      m "ProgUtils.intros_type_module: symbol = %a" AstDef.Symbol.pr
        symbol);*)

  (* let* topscope_name = find_highest_valid_scope_type_expr loc tp in

     let topscope_name = match topscope_name with
       | Some qi -> qi
       | None -> Error.type_error loc ("Could not find a valid scope to add type definition " ^ (AstDef.Type.to_string tp) ^ " to.")

     in *)
  introduce_typecheck_symbol ~loc ~f symbol

let rec does_symbol_implement_ra (symbol : AstDef.Module.symbol) : bool t =
  (*Logs.debug (fun m ->
      m "ProgUtils.does_symbol_implement_ra: symbol = %a"
        AstDef.Ident.pr
        (AstDef.Symbol.to_name symbol));*)
  let open Syntax in
  match symbol with
  | ModDef mod_def ->
      let mod_decl = mod_def.mod_decl in
      return mod_decl.mod_decl_is_ra
  | ModInst mod_inst -> (
      let* does_type_implement_ra =
        let* mod_inst_type_symbol =
          find_and_reify mod_inst.mod_inst_type
        in
        does_symbol_implement_ra mod_inst_type_symbol
      in

      if does_type_implement_ra then return true
      else
        match mod_inst.mod_inst_def with
        | None -> return false
        | Some (mod_inst_def_funct, mod_inst_def_args) ->
            let* mod_inst_def_funct_is_ra =
              let* mod_inst_def_funct_symbol =
                find_and_reify mod_inst_def_funct
              in
              does_symbol_implement_ra mod_inst_def_funct_symbol
            in

            return mod_inst_def_funct_is_ra)
  | _ -> return false

let rec does_type_implement_ra (tp : AstDef.type_expr) : bool t =
  let open Syntax in
  match tp with
  | App (Var qi, [], _) ->
      let* symbol = find_and_reify (QualIdent.pop qi) in
      does_symbol_implement_ra symbol
  | _ -> return false

let field_get_ra_qual_iden (field : AstDef.Module.field_def) =
  let field_type =
    match field.field_type with
    | App (Fld, [ tp_expr ], _) -> tp_expr
    | _ ->
        Error.error field.field_loc
          "ProgUtils.field_get_ra_module: Expected field definition"
  in

  match field_type with
  | App (Var qual_iden, [], _) -> QualIdent.pop qual_iden
  | _ ->
      Error.error field.field_loc
        "ProgUtils.field_get_ra_module: Expected field type to be a variable"

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
        Error.error loc
          "ProgUtils.get_field_utils_id: Expected field definition"
  in

  let field_elem_type =
    match field_type with
    | App (Fld, [ tp ], _) -> tp
    | _ -> Error.error loc "ProgUtils.get_field_utils_id: Expected field type"
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
          Error.error loc
            "ProgUtils.pred_ra_constr_qual_ident: Expected pred definition")
  | _ ->
      Error.error loc
        "ProgUtils.pred_ra_constr_qual_ident: Expected pred definition"

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
          Error.error loc
            "ProgUtils.pred_ra_constr_qual_ident: Expected pred definition")
  | _ ->
      Error.error loc
        "ProgUtils.pred_ra_constr_qual_ident: Expected pred definition"

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
      Error.error
        (AstDef.QualIdent.to_loc pred_name)
        "ProgUtils.pred_in_types: Expected pred definition"

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
      Error.error
        (AstDef.QualIdent.to_loc pred_name)
        "ProgUtils.pred_in_types: Expected pred definition"

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
        | Own -> return false
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
                  Error.error (AstDef.Expr.to_loc expr)
                    "ProgUtils.is_expr_pure: Expected a function or a variable")
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
            Error.error
              (AstDef.QualIdent.to_loc qual_ident)
              "ProgUtils.get_data_destrs_from_constr: Expected a variable"
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
                  Error.error
                    (AstDef.QualIdent.to_loc qual_ident)
                    "ProgUtils.get_data_destrs_from_constr: Expected a variant \
                     declaration"
              | Some variant_decl ->
                  return
                    (Base.List.map variant_decl.variant_args ~f:(fun var_decl ->
                         QualIdent.append (QualIdent.pop qual_ident)
                           var_decl.var_name)))
          | _ ->
              Error.error
                (AstDef.QualIdent.to_loc qual_ident)
                "ProgUtils.get_data_destrs_from_constr: Expected a data type")
      | _ ->
          Error.error
            (AstDef.QualIdent.to_loc qual_ident)
            "ProgUtils.get_data_destrs_from_constr: Expected a type definition")
  | _ ->
      Error.error
        (AstDef.QualIdent.to_loc qual_ident)
        "ProgUtils.get_data_destrs_from_constr: Expected a constructor \
         definition"

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
          acc @ expr_predicates)
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
  in

  let* preds_list = stmt_preds_mentioned s in
  let preds_list =
    Base.List.dedup_and_sort preds_list ~compare:QualIdent.compare
  in

  return preds_list
