(** The text an editor shows for a symbol, and the uses of names that the type checker
    records for it (see [Rewriter.record_reference]). *)

open Base
open Util
open AstDef

let application_loc application =
  let extend loc next =
    if String.equal (Loc.file_name loc) (Loc.file_name next) then Loc.merge loc next
    else loc
  in
  List.fold
    (Module.application_args application)
    ~init:(QualIdent.to_loc (Module.application_target application))
    ~f:(fun loc -> function
      | Module.ModArg name -> extend loc (QualIdent.to_loc name)
      | Module.TypeArg typ -> extend loc (Type.to_loc typ))

(** The declaration of [symbol] as written in its source: from the beginning of the line
    of its name to the end of its header, with [{ … }] in place of a body. *)
let declaration_text (symbol : Module.symbol) : string option =
  let name_loc, end_locs, has_body =
    match symbol with
    | CallDef ({ call_decl = d; _ } as c) ->
        let var_locs vs = List.map vs ~f:(fun (v : var_decl) -> v.var_loc) in
        let spec_locs specs =
          List.map specs ~f:(fun (s : Stmt.spec) -> Expr.to_loc s.spec_form)
        in
        (* The name keeps its location when the member is inherited; the declaration's
             is set to the inheriting module's for error messages. *)
        ( Ident.to_loc d.call_decl_name,
          var_locs d.call_decl_formals @ var_locs d.call_decl_returns
          @ spec_locs d.call_decl_precond
          @ spec_locs d.call_decl_postcond
          @ Option.to_list
              (Option.map d.call_decl_opens ~f:(fun clause -> clause.opens_loc)),
          (not (Callable.is_abstract c)) || d.call_decl_is_sealed )
    | TypeDef td -> (td.type_def_loc, [], false)
    | VarDef vd ->
        ( vd.var_decl.var_loc,
          Option.to_list (Option.map vd.var_init ~f:Expr.to_loc),
          false )
    | FieldDef fd -> (fd.field_loc, [], false)
    | ModInst mi ->
        ( mi.mod_inst_loc,
          Option.to_list (Option.map mi.mod_inst_def ~f:application_loc),
          false )
    | symbol -> (Symbol.to_loc symbol, [], false)
  in
  let same_file loc = String.equal (Loc.file_name loc) (Loc.file_name name_loc) in
  let last_end =
    List.fold (List.filter end_locs ~f:same_file) ~init:name_loc.Loc.loc_end
      ~f:(fun last loc ->
        if loc.Loc.loc_end.pos_cnum > last.pos_cnum then loc.Loc.loc_end else last)
  in
  let line_start =
    { name_loc.Loc.loc_start with pos_cnum = name_loc.Loc.loc_start.pos_bol }
  in
  Option.map
    (Loc.source_text (Loc.make line_start last_end))
    ~f:(fun text ->
      let indent = String.length text - String.length (String.lstrip text) in
      let dedent line =
        let ws = String.length line - String.length (String.lstrip line) in
        String.drop_prefix line (min ws indent)
      in
      let text =
        String.concat ~sep:"\n" (List.map (String.split text ~on:'\n') ~f:dedent)
      in
      (* The header ends at its last parameter when it has neither returns nor a
         contract, and an instance at its last argument. *)
      let unclosed opening closing =
        String.make
          (max 0
             (String.count text ~f:(Char.equal opening)
             - String.count text ~f:(Char.equal closing)))
          closing
      in
      let text = text ^ unclosed '(' ')' ^ unclosed '[' ']' in
      (* A callable without parameters, returns or contract ends at its name. *)
      let text =
        match symbol with
        | CallDef _ when not (String.mem text '(') -> text ^ "()"
        | ModInst { mod_inst_def = Some (ApplyUnit _); _ }
          when not (String.is_suffix text ~suffix:"()") ->
            text ^ "()"
        | _ -> text
      in
      if has_body then text ^ " { … }" else text)

(** The use of [name], as written, of [symbol], which it resolves to as [target]. A local
    variable is shown with its type, as the type checker inferred it. *)
let reference ~(name : qual_ident) ~(target : qual_ident) (symbol : Module.symbol) :
    Diagnostics.References.t =
  let local = List.is_empty (QualIdent.path target) in
  let detail =
    lazy begin match symbol with
    | VarDef { var_decl; _ } when local ->
        Some
          (Printf.sprintf !"%s%s: %{Type#user}"
             (if var_decl.var_ghost then "ghost " else "")
             (Ident.name var_decl.var_name)
             var_decl.var_type)
    | ModDef { mod_decl; _ }
      when not
             (String.equal
                (Ident.name mod_decl.mod_decl_name)
                (Ident.name (QualIdent.unqualify target))) ->
        (* A functor's parameter, whose symbol is its interface, or an instance, whose
             symbol is the instantiated functor. *)
        let name = Ident.name (QualIdent.unqualify target)
        and source = Ident.name mod_decl.mod_decl_name in
        Some
          (if mod_decl.mod_decl_is_interface then
             Printf.sprintf "module %s: %s" name source
           else Printf.sprintf "module %s = %s[…]" name source)
    | _ -> declaration_text symbol
    end
  in
  let def_loc =
    match symbol with
    | CallDef { call_decl; _ } -> Ident.to_loc call_decl.call_decl_name
    | _ -> Symbol.to_loc symbol
  in
  {
    use_loc = QualIdent.to_loc name;
    use_name = Ident.name (QualIdent.unqualify name);
    target = QualIdent.to_string_user target;
    kind = Symbol.kind symbol;
    def_loc;
    detail;
  }
