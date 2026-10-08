(** Annotations for editors: inherited contracts and members. *)

open Base
open Ast
open Util

(** The identifiers in [text]. *)
let identifiers_of (text : string) : string list =
  let is_ident_char c = Char.is_alphanum c || Char.equal c '_' || Char.equal c '\'' in
  String.split_on_chars text
    ~on:(List.filter (String.to_list text) ~f:(fun c -> not (is_ident_char c)))
  |> List.filter ~f:(fun s -> not (String.is_empty s))

(** The text of a clause of [orig_decl] as written at [span] in [content], with the
    parameters in [renaming] renamed by the member's names: at their occurrences in
    [exprs], the clause's formula and triggers. A bound variable whose name is one of the
    member's names gets a fresh one, at its declaration and its uses. If an occurrence's
    text is not as expected, or one of the member's names occurs in the clause otherwise,
    the clause keeps its text and a comment names the renaming. *)
let renamed_clause_text ~(content : string) ~(span_start : int) ~(span_end : int)
    ~(renaming : (var_decl * var_decl) list) (exprs : expr list) : string =
  let text = String.sub content ~pos:span_start ~len:(span_end - span_start) in
  let renaming =
    List.filter renaming ~f:(fun ((o : var_decl), (v : var_decl)) ->
        not (String.equal (Ident.name o.var_name) (Ident.name v.var_name)))
  in
  if List.is_empty renaming then text
  else
    (* Occurrences of variables, and bound variables with their declarations. *)
    let occurrences = ref [] and bound = ref [] in
    let rec walk (e : expr) =
      match e with
      | App (Var qi, [], attr) when List.is_empty (QualIdent.path qi) ->
          occurrences := (QualIdent.unqualify qi, attr.expr_loc) :: !occurrences
      | App (_, args, _) -> List.iter args ~f:walk
      | Binder (_, vars, trigs, body, _) ->
          bound := vars @ !bound;
          List.iter (List.concat trigs) ~f:walk;
          walk body
    in
    List.iter exprs ~f:walk;
    let new_names =
      List.map renaming ~f:(fun (_, (v : var_decl)) -> Ident.name v.var_name)
    in
    let taken = new_names @ identifiers_of text in
    let rec fresh name =
      if List.mem taken name ~equal:String.equal then fresh (name ^ "'") else name
    in
    (* The new name of each variable to rename: the parameters, and bound variables
         whose names would be captured. *)
    let renamed : (Ident.t * string) list =
      List.map renaming ~f:(fun ((o : var_decl), (v : var_decl)) ->
          (o.var_name, Ident.name v.var_name))
      @ List.filter_map !bound ~f:(fun (b : var_decl) ->
          let name = Ident.name b.var_name in
          if List.mem new_names name ~equal:String.equal then Some (b.var_name, fresh name)
          else None)
    in
    let new_name id = List.Assoc.find renamed id ~equal:Ident.equal in
    let edits =
      List.filter_map !occurrences ~f:(fun (id, loc) ->
          Option.map (new_name id) ~f:(fun name ->
              (id, Loc.start_index loc, Loc.end_index loc, name)))
      @ List.filter_map !bound ~f:(fun (b : var_decl) ->
          Option.map (new_name b.var_name) ~f:(fun name ->
              let start = Loc.start_index b.var_loc in
              (b.var_name, start, start + String.length (Ident.name b.var_name), name)))
      |> List.dedup_and_sort ~compare:(fun (_, s1, _, _) (_, s2, _, _) ->
          Int.compare s1 s2)
    in
    let at (start, stop) = String.sub content ~pos:start ~len:(stop - start) in
    let consistent =
      List.for_all edits ~f:(fun (id, start, stop, _) ->
          start >= span_start && stop <= span_end
          && String.equal (at (start, stop)) (Ident.name id))
    in
    (* A member's name that occurs in the clause other than at an edit refers to
         something else, which the renamed clause would capture. *)
    let rest =
      let buf = Buffer.create (String.length text) in
      let pos =
        List.fold edits ~init:span_start ~f:(fun pos (_, start, stop, _) ->
            Buffer.add_string buf (at (pos, start));
            Buffer.add_char buf ' ';
            stop)
      in
      Buffer.add_string buf (at (pos, span_end));
      Buffer.contents buf
    in
    let captures =
      List.exists (identifiers_of rest) ~f:(List.mem new_names ~equal:String.equal)
    in
    if consistent && not captures then (
      let buf = Buffer.create (String.length text) in
      let pos =
        List.fold edits ~init:span_start ~f:(fun pos (_, start, stop, name) ->
            Buffer.add_string buf (at (pos, start));
            Buffer.add_string buf name;
            stop)
      in
      Buffer.add_string buf (at (pos, span_end));
      Buffer.contents buf)
    else
      text ^ "  // where "
      ^ String.concat ~sep:", "
          (List.map renaming ~f:(fun ((o : var_decl), (v : var_decl)) ->
               Ident.name o.var_name ^ " is " ^ Ident.name v.var_name))

(** The declaration of [symbol] as written in its source: from the beginning of the line
    of its name to the end of its header, with [{ … }] in place of a body. Whether there
    is a body is read off the source, as the standard library's are dropped. *)
let declaration_text (symbol : Module.symbol) : string option =
  let name_loc, end_locs, has_body =
    match symbol with
    | CallDef { call_decl = d; _ } ->
        let var_locs vs = List.map vs ~f:(fun (v : var_decl) -> v.var_loc) in
        let spec_locs specs =
          List.map specs ~f:(fun (s : Stmt.spec) -> Expr.to_loc s.spec_form)
        in
        (* The name keeps its location when the member is inherited; the declaration's
             is set to the inheriting module's for error messages. *)
        ( Ident.to_loc d.call_decl_name,
          var_locs d.call_decl_formals @ var_locs d.call_decl_returns
          @ spec_locs d.call_decl_precond
          @ spec_locs d.call_decl_postcond,
          true )
    | TypeDef td -> (td.type_def_loc, [], false)
    | VarDef vd ->
        ( vd.var_decl.var_loc,
          Option.to_list (Option.map vd.var_init ~f:Expr.to_loc),
          false )
    | FieldDef fd -> (fd.field_loc, [], false)
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
  (* A callable has a body if a `{` follows its header in the source. *)
  let has_body =
    has_body
    && Option.value ~default:false
         (Option.map
            (Loc.source_content (Loc.file_name name_loc))
            ~f:(fun content ->
              let rec next i =
                if i >= String.length content then false
                else if Char.is_whitespace content.[i] then next (i + 1)
                else Char.equal content.[i] '{'
              in
              next last_end.pos_cnum))
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
      if has_body then text ^ " { … }" else text)

(** Records for the editor the members that the module or interface [module_ident]
    declared at [module_loc] inherits from the interfaces it implements, rather than
    declaring them itself, each with the interface it originates from. *)
let record_inherited_members ~(module_ident : qual_ident) ~(module_loc : Loc.t)
    (inherited : (qual_ident * Module.symbol) list) =
  let members =
    List.filter_map (List.rev inherited) ~f:(fun (interface_ident, symbol) ->
        let name = Ident.name (Symbol.to_name symbol) in
        let origin =
          Annotations.origin
            ~member:(QualIdent.to_string interface_ident ^ "." ^ name)
            ~default:(QualIdent.to_string interface_ident)
        in
        Annotations.set_origin
          ~member:(QualIdent.to_string module_ident ^ "." ^ name)
          origin;
        Option.map (declaration_text symbol) ~f:(fun text ->
            let member_loc =
              match symbol with
              | CallDef { call_decl; _ } -> Ident.to_loc call_decl.call_decl_name
              | symbol -> Symbol.to_loc symbol
            in
            { Annotations.origin; text; member_loc }))
  in
  if not (List.is_empty members) then
    Annotations.record (InheritedMembers { module_loc; members })

(** Records for the editor that [member] inherits the contract of [orig_decl], the member
    of interface [source], with the clauses as written there and the interface's
    parameters renamed to the member's, see [renamed_clause_text]. *)
let record_inherited_contract ~(member : ident) ~(source : qual_ident) ~source_loc
    ~(renaming : (var_decl * var_decl) list) (orig_decl : Callable.call_decl) =
  let clause keyword (spec : Stmt.spec) =
    let form_loc = Expr.to_loc spec.spec_form in
    Option.bind
      (Loc.source_content (Loc.file_name form_loc))
      ~f:(fun content ->
        (* A clause with triggers starts at the brace before the first one. *)
        let span_start =
          match spec.spec_trigs with
          | (trigger :: _) :: _ ->
              String.rindex_from content (Loc.start_index (Expr.to_loc trigger)) '{'
          | _ -> Some (Loc.start_index form_loc)
        in
        let span_end = Loc.end_index form_loc in
        Option.bind span_start ~f:(fun span_start ->
            if span_start < 0 || span_end > String.length content || span_start > span_end
            then None
            else
              let text =
                renamed_clause_text ~content ~span_start ~span_end ~renaming
                  (spec.spec_form :: List.concat spec.spec_trigs)
              in
              Some { Annotations.keyword; text; clause_loc = form_loc }))
  in
  let clauses =
    List.filter_map orig_decl.call_decl_precond ~f:(clause "requires")
    @ List.filter_map orig_decl.call_decl_postcond ~f:(clause "ensures")
  in
  if not (List.is_empty clauses) then
    Annotations.record
      (InheritedContract
         {
           member_loc = Ident.to_loc member;
           source =
             Printf.sprintf !"%{QualIdent}.%{Ident}" source orig_decl.call_decl_name;
           source_loc;
           clauses;
         })
