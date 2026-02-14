open Base
open Ast
open Util

open ExtApi


(** Here we implement an extension that adds support for custom hardware-provided atomic primitives. This is a core Raven extension that is enabled by default.

At present this adds the following atomic primitives:
- `cas`: Compare-and-swap
- `faa`: Fetch-and-add
- `xchg`: Exchange
- `cmpxchg`: Compare-and-exchange

The difference between `cas` and `cmpxchg` is that `cas` only returns a bool indicating whether the swap succeeded, whereas `cmpxchg` returns the initial value at the location in addition to whether the swap succeeded or not.
*)
module AtomicExt (Cont : ListApi) = struct
  let lib_source = None
  let local_vars = []

  type atomic_inbuilt_kind =
    | Cas 
    | Faa
    | Xchg
    | CmpXchg

  let atomic_inbuilt_string = function
    | Cas -> "cas"
    | Faa -> "faa"
    | Xchg -> "xchg"
    | CmpXchg -> "cmpxchg"

  (* No new types or expressions, only new statements. *)
  type Stmt.stmt_ext += 
    | AtomicInbuiltInit of atomic_inbuilt_kind
    | AtomicInbuiltNonInit of atomic_inbuilt_kind

  module ListFns = Cont.ListFns

  (* AstDef *)
  let type_ext_to_name = Cont.type_ext_to_name

  let expr_ext_to_string = Cont.expr_ext_to_string
  
  let pr_stmt_ext ppf ext expr_list = 
    let open Stdlib.Format in
    match ext, expr_list with
    | (AtomicInbuiltInit ais | AtomicInbuiltNonInit ais), (lhs_expr :: field_expr :: ref_expr :: args) ->
      fprintf ppf "@[<2>[EXT]%a@ :=@ %s(%a.%a, %a)@]" Expr.pr lhs_expr (atomic_inbuilt_string ais) Expr.pr ref_expr Expr.pr field_expr Expr.pr_list args
    | _ -> Cont.pr_stmt_ext ppf ext expr_list

  let stmt_ext_symbols = Cont.stmt_ext_symbols
  
  let stmt_ext_local_vars_modified stmt_ext exprs =
    match stmt_ext, exprs with
    | (AtomicInbuiltInit ais | AtomicInbuiltNonInit ais), (lhs_expr :: field_expr :: ref_expr :: args) ->
      (* Only the `lhs_expr` is modified; if it is local, it is returned.  *)
      if QualIdent.is_local (Expr.to_qual_ident lhs_expr) then
            [QualIdent.to_ident (Expr.to_qual_ident lhs_expr)]
          else
            []
    | _ -> Cont.stmt_ext_local_vars_modified stmt_ext exprs

  (* These commands pretty explicitly access the `field_expr` field. *)
  let stmt_ext_fields_accessed stmt_ext exprs = 
    match stmt_ext, exprs with
    | (AtomicInbuiltInit ais | AtomicInbuiltNonInit ais), (lhs_expr :: field_expr :: ref_expr :: args) ->
        [(Expr.to_qual_ident field_expr)]

    | _ -> Cont.stmt_ext_fields_accessed stmt_ext exprs


  (* Rewriter *)
  let expr_ext_rewrite_types = Cont.expr_ext_rewrite_types
  let stmt_ext_rewrite_types = Cont.stmt_ext_rewrite_types


  (* Typing *)
  let type_check_type_expr = Cont.type_check_type_expr
  
  let type_check_expr = Cont.type_check_expr 

  (** Here we define a custom logic to decide whether a type is "word-sized" (ie operable in an atomic hardware step), or not.  
  
  At present, we assume 2 bits for storing any tags, and the remaining 62 bits to store the object itself, be it an `Int`, `Ref`, or `Bool`.

  This logic can ready be updated to fit specific domains. That is one advantage of implementing this feature as an extension.
  *)
  let is_type_word_sized (typ: type_expr) : bool Rewriter.t =
    let open Rewriter.Syntax in
    Logs.debug (fun m -> m "[EXT] AtomicExt: is_type_word_sized: input=%a" Type.pr typ);
    let* typ = !Rewriter.expand_type_expr_ref typ in

    match typ with
    (* either type is a base type *)
    | _ when Type.is_base_type typ -> Rewriter.return true

    | App (Var qual_iden, [], _) ->
      let* qual_ident, symbol = 
        Rewriter.resolve_and_find qual_iden 
      in
      let+ qual_ident_def =
        Rewriter.Symbol.reify_type_def (Type.to_loc typ) symbol
      in
      begin match qual_ident_def with
      | None -> false
      (* or an algebraic data type, where... *)
      | Some (App (Data (qi, variant_decls), [], _)) ->
        (* each constructor takes at most a single, base-type argument *)
        let are_constrs_base_types = 
          List.for_all variant_decls ~f:(fun variant_decl ->
            (List.length variant_decl.variant_args = 0) 
            || (List.length variant_decl.variant_args = 1 
                && Type.is_base_type (List.hd_exn variant_decl.variant_args).var_type) 
          ) 
        in

        (* and number of constructors <= 4 (so we can fit the tag in 2 bits) *)
        let can_constr_tag_fit = List.length variant_decls <= 4 in

        can_constr_tag_fit && are_constrs_base_types

      | Some _ -> false
      end
      
    | _ -> Rewriter.return false
  
  (* type-check each statement *)
  let type_check_stmt call_decl (stmt_ext : Stmt.stmt_ext) (expr_list: expr list) (stmt_loc: Loc.t) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (type_check_stmt_functs : ExtApi.type_check_stmt_functs)
  :
      (Stmt.basic_stmt_desc * ProgUtils.DisambiguationTbl.t) Rewriter.t = 
      let open Rewriter.Syntax in
      let* is_ghost_scope = Rewriter.is_ghost_scope in
      match stmt_ext, expr_list with
      | ((AtomicInbuiltInit ais | AtomicInbuiltNonInit ais) as ext), (lhs_expr :: field_expr :: ref_expr :: args) ->
        let is_init =
          match ext with
          | AtomicInbuiltInit _ -> true
          | AtomicInbuiltNonInit _ -> false
          | _ -> assert false
        in
        let _ =
          if is_ghost_scope then
            Error.type_error stmt_loc "Cannot use atomic operations in a ghost context"
        in
        (* use `get_assign_lhs` to get the var_decl for `lhs_expr`. *)
        let* atomic_inbuilt_lhs, var_decl = type_check_stmt_functs.get_assign_lhs (Expr.to_qual_ident lhs_expr) ~is_init:is_init in
            Logs.debug (fun m -> m "[EXT] AtomicExt.type_check_stmt lhs_expr: %a; atomic_inbuilt_lhs: %a" Expr.pr lhs_expr QualIdent.pr atomic_inbuilt_lhs);

        (* Use `Rewriter.resolve_and_find` to find the field. This can very well be replaced by the more compact `Rewriter.find_and_reify_field`; that would be equivalent. *)
        let* atomic_inbuilt_field, symbol =
          Rewriter.resolve_and_find (Expr.to_qual_ident field_expr)
        in
        let* symbol = Rewriter.Symbol.reify symbol in
        let* ais_fld_type, ais_fld_type_full = match symbol with
          | FieldDef { field_type = App (Fld, [ expected_fld_typ ], _) as tp; _ }
            ->
            let* expanded_type =
              type_check_stmt_functs.expand_type_expr expected_fld_typ
            in

            let* is_type_word_sized = is_type_word_sized expanded_type in

            if is_type_word_sized then 
              Rewriter.return (expanded_type, tp)
            else
              Error.type_error (Expr.to_loc field_expr)
                (Printf.sprintf !"%s only allowed over word-sized types (Int, Bool, Ref, or their algebraic sum types) but found %{Type}"
                 (atomic_inbuilt_string ais) expected_fld_typ)
          | _ ->
              Error.type_error (Expr.to_loc field_expr)
              ("Expected field identifier, but found "
               ^ Expr.to_string field_expr)
        in
        (* type-checking `ref_expr` *)
        let* atomic_inbuilt_ref = type_check_stmt_functs.disambiguate_process_expr ref_expr Type.ref disam_tbl in
        let+ args = match ais with
        (* type-checking arguments differently according to each atomic primitive. *)
          | Cas -> begin
            match args with
            | old_val_expr :: new_val_expr :: [] ->
              (* for `cas`, the old_val_expr and new_val_expr have the same type has the field `ais_fld`. *)
            let* cas_old_val = type_check_stmt_functs.disambiguate_process_expr old_val_expr ais_fld_type disam_tbl in
            let* cas_new_val = type_check_stmt_functs.disambiguate_process_expr new_val_expr ais_fld_type disam_tbl in
            let+ _ = type_check_stmt_functs.disambiguate_process_expr (Expr.mk_var ~typ:var_decl.var_type (Expr.to_qual_ident lhs_expr)) (Type.bool |> Type.set_ghost_to var_decl.var_type) disam_tbl in
            [ cas_old_val; cas_new_val ]

            (* type error *)
            | _ -> Error.type_error stmt_loc  "Wrong number of arguments for CAS"
            end

          | Faa -> begin
            match args with
            | faa_val :: [] ->
              (* For `faa`, the underlying field must be an `Int` field, having a type_expr of `Field[Int]`. *)
            let* _ = type_check_stmt_functs.disambiguate_process_expr (Expr.mk_var ~typ:ais_fld_type_full atomic_inbuilt_field)
                (Type.mk_fld (QualIdent.to_loc atomic_inbuilt_field) Type.int) disam_tbl in
            (* make sure `faa_val` is well_typed. *)
            let* faa_val = type_check_stmt_functs.disambiguate_process_expr faa_val ais_fld_type disam_tbl in

            (* make sure `lhs_expr` is of the right type. *)
            let+ _ = type_check_stmt_functs.disambiguate_process_expr (Expr.mk_var ~typ:var_decl.var_type (Expr.to_qual_ident lhs_expr)) (ais_fld_type |> Type.set_ghost_to var_decl.var_type) disam_tbl in
            [ faa_val ]

            (* type error *)
            | _ -> Error.type_error stmt_loc  "Wrong number of arguments for FAA"
            end

          | Xchg -> begin
            match args with
            | xchg_new_val :: [] ->
            (* make sure `xch_new_val` is well-typed *)
            let* xchg_new_val = type_check_stmt_functs.disambiguate_process_expr xchg_new_val ais_fld_type disam_tbl in

            (* make sure `lhs_expr` is well-typed *)
            let+ _ = type_check_stmt_functs.disambiguate_process_expr (Expr.mk_var ~typ:var_decl.var_type (Expr.to_qual_ident lhs_expr)) (ais_fld_type |> Type.set_ghost_to var_decl.var_type) disam_tbl in
            [ xchg_new_val ]

            (* type error *)
            | _ -> Error.type_error stmt_loc  "Wrong number of arguments for XCHG"
            end

          | CmpXchg -> begin 
            match args with
            | old_val_expr :: new_val_expr :: [] ->
            (* make sure `cmxchg_old_val` is well-typed *)
            let* cmpxchg_old_val = type_check_stmt_functs.disambiguate_process_expr old_val_expr ais_fld_type disam_tbl in

            (* make sure `cmxchg_new_val` is well-typed *)
            let* cmpxchg_new_val = type_check_stmt_functs.disambiguate_process_expr new_val_expr ais_fld_type disam_tbl in

            (* make sure `lhs_expr` is well-typed *)
            let+ _ = type_check_stmt_functs.disambiguate_process_expr 
              (Expr.mk_var ~typ:var_decl.var_type (Expr.to_qual_ident lhs_expr)) 
              (Type.mk_prod stmt_loc [ais_fld_type; Type.bool] |> Type.set_ghost_to var_decl.var_type) 
              disam_tbl 
            in

            [ cmpxchg_old_val; cmpxchg_new_val ]

            (* type error *)
            | _ -> Error.type_error stmt_loc  "Wrong number of arguments for cmpxchg"
          end

        in
        
        (* Finally, rebuilt the `Stmt.basic_stmt_desc`. *)
        let ais_desc = (ext, 
            Expr.from_var_decl var_decl :: 
              (Expr.mk_app ~loc:(Expr.to_loc field_expr) ~typ:ais_fld_type_full  (Expr.Var atomic_inbuilt_field) []) ::
            atomic_inbuilt_ref :: args)

        in
        Logs.debug (fun m -> m "AtomicExt.type_check_stmt FINISHES");
        (Stmt.StmtExt ais_desc, disam_tbl)

      (* Type error *)
      | (AtomicInbuiltInit ais | AtomicInbuiltNonInit ais), _ ->
        Error.type_error stmt_loc "Wrong number of arguments for atomic commands"

      | _ -> Cont.type_check_stmt call_decl stmt_ext expr_list stmt_loc disam_tbl type_check_stmt_functs


  (* Rewrites *)
  (* Rewriting these atomic commands in equivalent simpler Raven commands. *)
  let rewrite_type_ext = Cont.rewrite_type_ext
  let rewrite_expr_ext = Cont.rewrite_expr_ext

  let rewrite_stmt_ext (stmt_ext: Stmt.stmt_ext) (expr_list: expr list) loc: Stmt.t Rewriter.t =
    let open Rewriter.Syntax in
    match stmt_ext, expr_list with
    | (AtomicInbuiltInit ais | AtomicInbuiltNonInit ais), (lhs_expr :: field_expr :: ref_expr :: args) ->
      (* define a new local variable to store field value *)
      let new_var_name =
        Ident.fresh loc (QualIdent.to_string (Expr.to_qual_ident lhs_expr) ^ "$" ^ atomic_inbuilt_string ais)
      in
      let new_var_decl_typ = match ais, args with
        | Cas, [old_val; new_val] -> Expr.to_type old_val
        | Faa, [faa_val] -> Type.int
        | Xchg, [xchg_new_val] -> Expr.to_type xchg_new_val
        | CmpXchg, [cmpxchg_old_val; cmpxchg_new_val] -> Expr.to_type cmpxchg_old_val
        | _ -> Error.type_error loc "Incorrect number of arguments in Atomic extension"
      in
      let new_var_decl =
        Type.mk_var_decl ~loc:loc ~ghost:true new_var_name
          new_var_decl_typ
      in
      (* add the new local variable *)
      let+ _ =
        Rewriter.introduce_symbol
          (Module.VarDef { var_decl = new_var_decl; var_init = None; var_is_free = true })
      in
      let new_var_qualident = QualIdent.from_ident new_var_decl.var_name in
      (* ```rd_var := ref.field;``` *)
      let read_stmt =
        Stmt.mk_field_read ~loc:loc new_var_qualident
          (Expr.to_qual_ident field_expr) ref_expr
      in
      let ais_stmts =
        match ais, args with
        (* CAS *)
        | Cas, [old_val; new_val] ->
          let test_ =
            Some
              (Expr.mk_eq ~loc:loc
                 (Expr.from_var_decl new_var_decl)
                 old_val)
          in
          let then1_ =
            Stmt.mk_assign ~loc:loc [ Expr.to_qual_ident lhs_expr ] (Expr.mk_bool true)
          in
          let then2_ =
            Stmt.mk_field_write ~loc:loc ref_expr (Expr.to_qual_ident field_expr) new_val
          in
          let then_ = Stmt.mk_block_stmt ~loc:loc [ then1_; then2_ ] in
          let else_ =
            Stmt.mk_assign ~loc:loc [ Expr.to_qual_ident lhs_expr ] (Expr.mk_bool false)
          in
          (* ```
              if (rd_var == old_val) {
                lhs := true; 
                ref.field := new_val;
                } else {
                  lhs := false;
                }
             ```
          *)
          [Stmt.mk_cond ~loc:loc test_ then_ else_]

        (* FAA *)
        | Faa, [faa_val] ->
          (* ```
              ref.field := rd_var + faa_val;
              lhs_expr := rd_var;
             ```
          *)
          [ Stmt.mk_field_write ~loc:loc ref_expr (Expr.to_qual_ident field_expr)
              (Expr.mk_app ~typ:Type.int Expr.Plus [Expr.from_var_decl new_var_decl; faa_val]);
            Stmt.mk_assign ~loc:loc [ Expr.to_qual_ident lhs_expr ] (Expr.from_var_decl new_var_decl) ]

        (* XCHG *)
        | Xchg, [xchg_new_val] ->
          (* ```
              ref.field := xchg_new_val;
              lhs_expr := rd_var;
             ```
          *)
          [ Stmt.mk_field_write ~loc:loc ref_expr (Expr.to_qual_ident field_expr)
              xchg_new_val;
            Stmt.mk_assign ~loc:loc [ Expr.to_qual_ident lhs_expr ] (Expr.from_var_decl new_var_decl) ]

          (* ```
              if (rd_var == old_val) {
                lhs_expr := (rd_var, true);
                ref.field := new_val;
              } else {
                lhs_expr := (rd_var, false);
              }
             ```
          *)
        | CmpXchg, [cmpxchg_old_val; cmpxchg_new_val] ->
          let test_ =
            Some
              (Expr.mk_eq ~loc
                 (Expr.from_var_decl new_var_decl)
                 cmpxchg_old_val)
          in
          let then1_ =
            Stmt.mk_assign ~loc:loc [ Expr.to_qual_ident lhs_expr ] (Expr.mk_tuple ~loc [
              Expr.from_var_decl new_var_decl; 
              Expr.mk_bool true
            ])
          in
          let then2_ =
            Stmt.mk_field_write ~loc:loc ref_expr (Expr.to_qual_ident field_expr) cmpxchg_new_val
          in
          let then_ = Stmt.mk_block_stmt ~loc:loc [ then1_; then2_ ] in
          let else_ =
            Stmt.mk_assign ~loc:loc [ Expr.to_qual_ident lhs_expr ] (Expr.mk_tuple ~loc [
              Expr.from_var_decl new_var_decl;
              Expr.mk_bool false
            ])
          in
          [Stmt.mk_cond ~loc:loc test_ then_ else_]

        | _ -> assert false
      in
      let new_stmts =
        Stmt.mk_block_stmt ~loc:loc (read_stmt :: ais_stmts)
      in
      new_stmts

    | _ -> Cont.rewrite_stmt_ext stmt_ext expr_list loc


  (* --------------------- *)
  (* --- DO NOT MODIFY --- *)
  let lib_sources = (Option.to_list lib_source) @ Cont.lib_sources
  let ext_local_vars = local_vars @ Cont.ext_local_vars
end
