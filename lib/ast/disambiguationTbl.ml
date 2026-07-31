(** Used in disambiguating local idents in Typing.ProcessCallable.

    This lives below [Rewriter] (rather than inside [ProgUtils], which depends on
    [Rewriter]) so that [Rewriter]'s [ext_hooks] can mention [DisambiguationTbl.t] in
    the signatures it borrows from the extension API without creating a dependency
    cycle. *)

open Base
open AstDef
open Util

type t = ident ident_map list

let push (disam_tbl : t) : t = Map.empty (module Ident) :: disam_tbl

let pop (disam_tbl : t) : t =
  match disam_tbl with
  | _ :: disam_tbl -> disam_tbl
  | [] -> raise (Invalid_argument "Empty DisambiguationTbl")

let add (disam_tbl : t) loc name new_name : t =
  match disam_tbl with
  | hd :: tl -> (
      match Map.add hd ~key:name ~data:new_name with
      | `Ok hd -> hd :: tl
      | `Duplicate -> Error.redeclaration_error loc (Ident.to_string name))
  | [] -> raise (Invalid_argument "Empty DisambiguationTbl")

let rec find (disam_tbl : t) name =
  match disam_tbl with
  | [] -> None
  | map :: ts -> (
      match Map.find map name with
      | None -> find ts name
      | Some id -> Some id)

let rec find_exn (disam_tbl : t) name =
  match disam_tbl with
  | map :: ts -> (
      match Map.find map name with
      | None -> find_exn ts name
      | Some id -> id)
  | [] -> raise Stdlib.Not_found

(* [~id:1] so the renamed binder never carries number 0. Every *source-level* ident is
   number 0, and the first freshening of a name would otherwise return 0 too -- making
   the "fresh" name byte-identical to the source name it is supposed to be distinct
   from. That aliasing is observable: a binder named after a destructor field (say
   `forall elem: Int`, or a `match` arm's `case cons(elem, tl)`) lands in the callable's
   scope as plain `elem` and shadows the destructor, so a later `x.elem` fails to
   resolve. Numbering from 1 keeps generated names in their own space. *)
let add_var_decl (var_decl : AstDef.Type.var_decl) (disam_tbl : t) :
    AstDef.Type.var_decl * t =
  let new_name =
    Ident.fresh var_decl.var_loc ~id:1 var_decl.var_name.ident_name
  in
  let disam_tbl =
    add disam_tbl var_decl.var_loc var_decl.var_name new_name
  in
  let var_decl = { var_decl with var_name = new_name } in

  (var_decl, disam_tbl)

let pr ppf disam_tbl =
  let open Stdlib.Format in
  fprintf ppf "%a"
    (Fmt.Dump.list (Fmt.Dump.list (Fmt.Dump.pair Ident.pr Ident.pr)))
    (Base.List.map disam_tbl ~f:Base.Map.to_alist)
