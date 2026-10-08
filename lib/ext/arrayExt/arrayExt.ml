open Base
open Ast
open ExtApi
open Util

(** Indexing syntax for arrays, the instances of `Library.Array`. The entry at index [i]
    of array [a] is the field `value` of the cell `loc(a, i)`, and like a field it may
    only be read or written by a statement and named as a location in `own`:

    - `x := a[i]` and `var x := a[i]` read it,
    - `a[i] := v` writes it, which the parser turns into `a := a[i := v]`,
    - `own(a[i], v)` owns it, and `faa(a[i], n)` and the other atomic operations of the
      standard library operate on it, as on any location `x.f`.

    Any other use of `a[i]` or `a[i := v]` is an error, as expressions are pure. The core
    type checker rejects these constructs, since `a` is not a map, and offers them to
    [claim_expr]/[claim_basic_stmt], or to [claim_location] where it expects a field
    location. Type-checking a claimed construct produces the corresponding field read or
    field write of the core, and a claimed location is `loc(a, i).value`, so none of this
    extension's constructs remains after type checking, and an array access is one atomic
    step like any other field access. *)
module ArrayExt (Cont : Ext) = struct
  include Cont

  let lib_source = None

  type Expr.expr_ext +=
    | ArrayEntry  (** `a[i]` in an expression *)
    | ArrayUpdate  (** `a[i := v]` in an expression *)

  type Stmt.stmt_ext +=
    | ArrayRead of { lhs : qual_ident list; is_init : bool }
          (** `x := a[i]`, operands `a` and `i` *)
    | ArrayWrite of { lhs : qual_ident list; is_init : bool }
          (** `x := a[i := v]`, operands `a`, `i` and `v` *)
    | ArrayVarDef of Stmt.var_def  (** `var x := a[i]` *)

  let library_array =
    QualIdent.from_list
      [ Ident.make Loc.dummy "Library" 0; Ident.make Loc.dummy "Array" 0 ]

  (* Member [name] of [inst], named at [loc] in the source. *)
  let member ~(loc : location) (inst : qual_ident) (name : string) : qual_ident =
    QualIdent.append inst (Ident.make loc name 0)

  (* The instance of `Library.Array` whose arrays have type [typ], if any. *)
  let array_instance (typ : type_expr) : qual_ident option Rewriter.t =
    let open Rewriter.Syntax in
    match typ with
    | Type.App (Var qi, [], _) when not (List.is_empty (QualIdent.path qi)) -> (
        let inst = QualIdent.pop qi in
        let+ resolved = Rewriter.resolve_and_find_opt inst in
        match resolved with
        | Some (_, symbol)
          when QualIdent.equal (Rewriter.Symbol.orig_qid symbol) library_array ->
            Some inst
        | _ -> None)
    | _ -> Rewriter.return None

  (* The array instance of [base], an operand typed by the core. *)
  let typed_array_instance (base : expr) = array_instance (Expr.to_type base)

  (* The array instance of [base], an operand as parsed. *)
  let parsed_array_instance (base : expr) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (functs : type_check_stmt_functs) =
    let open Rewriter.Syntax in
    let* base =
      functs.disambiguate_and_check_expr base (Type.any |> Type.set_ghost true) disam_tbl
    in
    typed_array_instance base

  (* The cell `loc(a, i)` holding the entry at index [index] of [base]. *)
  let cell ~(loc : location) (inst : qual_ident) (base : expr) (index : expr) : expr =
    Expr.mk_app ~loc ~typ:Type.ref (Var (member ~loc inst "loc")) [ base; index ]

  let value_field ~(loc : location) (inst : qual_ident) : expr =
    Expr.mk_app ~loc ~typ:Type.any (Var (member ~loc inst "value")) []

  (* AstDef *)

  let expr_ext_to_string (expr_ext : Expr.expr_ext) : string =
    match expr_ext with
    | ArrayEntry -> "array entry"
    | ArrayUpdate -> "array update"
    | other -> Cont.expr_ext_to_string other

  let expr_ext_is_recognized (expr_ext : Expr.expr_ext) : bool =
    match expr_ext with
    | ArrayEntry | ArrayUpdate -> true
    | other -> Cont.expr_ext_is_recognized other

  let pr_basic_stmt_ext ppf (stmt_ext : Stmt.stmt_ext) (expr_list : expr list) =
    let open Stdlib.Format in
    let pr_lhs = Util.Print.pr_list_comma QualIdent.pr in
    match (stmt_ext, expr_list) with
    | ArrayRead { lhs; _ }, [ base; index ] ->
        fprintf ppf "@[<2>%a@ :=@ %a[%a]@]" pr_lhs lhs Expr.pr base Expr.pr index
    | ArrayWrite { lhs; _ }, [ base; index; value ] ->
        fprintf ppf "@[<2>%a@ :=@ %a[%a@ :=@ %a]@]" pr_lhs lhs Expr.pr base Expr.pr index
          Expr.pr value
    | ArrayVarDef var_def, [] -> Stmt.pr_basic_stmt ppf (VarDef var_def)
    | (ArrayRead _ | ArrayWrite _ | ArrayVarDef _), _ ->
        Error.internal_error Loc.dummy "ArrayExt: wrong number of operands"
    | _ -> Cont.pr_basic_stmt_ext ppf stmt_ext expr_list

  let stmt_ext_is_recognized (stmt_ext : Stmt.stmt_ext) : bool =
    match stmt_ext with
    | ArrayRead _ | ArrayWrite _ | ArrayVarDef _ -> true
    | other -> Cont.stmt_ext_is_recognized other

  (* Typing *)

  let claim_expr (constr : Expr.constr) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) =
    let open Rewriter.Syntax in
    let claim_if_array base tag =
      let+ inst = typed_array_instance base in
      Option.map inst ~f:(fun _ -> (tag, expr_list))
    in
    let* own =
      match (constr, expr_list) with
      | MapLookUp, [ base; _ ] -> claim_if_array base ArrayEntry
      | MapUpdate, [ base; _; _ ] -> claim_if_array base ArrayUpdate
      | _ -> Rewriter.return None
    in
    combine_claims expr_attr.expr_loc own (Cont.claim_expr constr expr_list expr_attr)

  let claim_location (expr : expr) =
    let open Rewriter.Syntax in
    let loc = Expr.to_loc expr in
    let* own =
      match expr with
      | App (MapLookUp, [ base; index ], _) ->
          let+ inst = typed_array_instance base in
          Option.map inst ~f:(fun inst ->
              (cell ~loc inst base index, member ~loc inst "value"))
      | _ -> Rewriter.return None
    in
    combine_claims loc own (Cont.claim_location expr)

  let claim_basic_stmt (stmt : Stmt.basic_stmt_desc) (loc : location)
      (disam_tbl : ProgUtils.DisambiguationTbl.t) (functs : type_check_stmt_functs) =
    let open Rewriter.Syntax in
    let claim_if_array base claim =
      let+ inst = parsed_array_instance base disam_tbl functs in
      Option.map inst ~f:(fun _ -> claim)
    in
    let* own =
      match stmt with
      | Assign
          {
            assign_lhs = lhs;
            assign_rhs = App (MapLookUp, [ base; index ], _);
            assign_is_init;
          } ->
          claim_if_array base
            (ArrayRead { lhs; is_init = assign_is_init }, [ base; index ])
      | Assign
          {
            assign_lhs = lhs;
            assign_rhs = App (MapUpdate, [ base; index; value ], _);
            assign_is_init;
          } ->
          claim_if_array base
            (ArrayWrite { lhs; is_init = assign_is_init }, [ base; index; value ])
      | VarDef
          ({ var_init = Some (App ((MapLookUp | MapUpdate), base :: _, _)); _ } as var_def)
        ->
          claim_if_array base (ArrayVarDef var_def, [])
      | _ -> Rewriter.return None
    in
    combine_claims loc own (Cont.claim_basic_stmt stmt loc disam_tbl functs)

  let not_pure_error loc =
    Error.type_error loc
      "An array entry can only be read by an assignment `x := a[i]`, or named as a \
       location, as in `own(a[i], v)`"

  let not_a_value_error loc =
    Error.type_error loc
      "An array is not a value. To change an entry, assign to it with `a[i] := v`"

  let type_check_expr (expr_ext : Expr.expr_ext) (expr_list : expr list)
      (expr_attr : Expr.expr_attr) (expected_typ : type_expr)
      (functs : type_check_expr_functs) =
    let loc = expr_attr.expr_loc in
    match (expr_ext, expr_list) with
    | ArrayEntry, _ -> not_pure_error loc
    | ArrayUpdate, _ -> not_a_value_error loc
    | _ -> Cont.type_check_expr expr_ext expr_list expr_attr expected_typ functs

  let type_check_basic_stmt (call_decl : Callable.call_decl) (stmt_ext : Stmt.stmt_ext)
      (expr_list : expr list) (loc : location) (disam_tbl : ProgUtils.DisambiguationTbl.t)
      (functs : type_check_stmt_functs) =
    let open Rewriter.Syntax in
    let array_instance_exn base =
      let+ inst = parsed_array_instance base disam_tbl functs in
      match inst with
      | Some inst -> inst
      | None -> Error.internal_error loc "ArrayExt: access to a non-array"
    in
    (* Type-checks [basic_stmt], a core statement. *)
    let process (basic_stmt : Stmt.basic_stmt_desc) =
      let+ stmt, disam_tbl =
        functs.check_stmt call_decl
          { stmt_desc = Basic basic_stmt; stmt_loc = loc }
          disam_tbl
      in
      match stmt.stmt_desc with
      | Basic basic_stmt -> (basic_stmt, disam_tbl)
      | _ -> Error.internal_error loc "ArrayExt: expected a basic statement"
    in
    match (stmt_ext, expr_list) with
    | ArrayRead { lhs; is_init }, [ base; index ] -> (
        match lhs with
        | [ _ ] ->
            let* inst = array_instance_exn base in
            let read =
              Expr.mk_app ~loc ~typ:Type.any Read
                [ cell ~loc inst base index; value_field ~loc inst ]
            in
            process
              (Assign { assign_lhs = lhs; assign_rhs = read; assign_is_init = is_init })
        | _ ->
            Error.type_error loc "An array entry can only be read into a single variable")
    | ArrayWrite { lhs; is_init }, [ base; index; value ] -> (
        match (lhs, base) with
        | [ x ], App (Var y, [], _) when QualIdent.equal x y && not is_init ->
            let* inst = array_instance_exn base in
            process
              (FieldWrite
                 {
                   field_write_ref = cell ~loc inst base index;
                   field_write_field = member ~loc inst "value";
                   field_write_val = value;
                 })
        | _ -> not_a_value_error loc)
    | ArrayVarDef var_def, [] -> (
        match var_def.var_init with
        | Some (App (MapLookUp, [ base; _ ], _)) ->
            (* The variable's type, unless declared, is the arrays' element type; the
               read that initializes it is an assignment of its own. *)
            let* inst = array_instance_exn base in
            let* var_type =
              if Type.is_any var_def.var_decl.var_type then
                let+ field = Rewriter.find_and_reify_field (member ~loc inst "value") in
                Type.field_val field.field_type
              else Rewriter.return var_def.var_decl.var_type
            in
            process
              (VarDef
                 {
                   var_def with
                   var_decl = { var_def.var_decl with var_type };
                   var_init = None;
                 })
        | _ -> not_a_value_error loc)
    | (ArrayRead _ | ArrayWrite _ | ArrayVarDef _), _ ->
        Error.internal_error loc "ArrayExt: wrong number of operands"
    | _ -> Cont.type_check_basic_stmt call_decl stmt_ext expr_list loc disam_tbl functs
end
