open Base
open Ast
open Smt
open SmtLibAst
module Session = SmtSolver.SmtSession

let declare_tuple_sort (arity : int) : command =
  let tuple_sort_name =
    QualIdent.from_ident (Ident.make Util.Loc.dummy ("$tuple_" ^ Int.to_string arity) 0)
  in

  let params =
    Base.List.init arity ~f:(fun i ->
        QualIdent.from_ident (Ident.make Util.Loc.dummy ("X" ^ Int.to_string i) 0))
  in

  let constr = tuple_sort_name in
  let destrs =
    Base.List.init arity ~f:(fun i ->
        QualIdent.from_ident
          (Ident.make Util.Loc.dummy
             ("$tuple_" ^ Int.to_string arity ^ "_" ^ Int.to_string i)
             0))
  in

  let destrs_sorts =
    Base.List.map2_exn destrs params ~f:(fun destr param ->
        (destr, Ast.Type.mk_var param))
  in

  mk_declare_datatype (tuple_sort_name, params, [ (constr, destrs_sorts) ])

let initialize session ~diagnostics ~timeout =
  let open Session in
  let open PreambleConsts in
  let options_list =
    [
      SetOption (":timeout", Int.to_string timeout, None);
      SetOption (":auto-config", "false", None);
      SetOption (":smt.mbqi", "false", None);
      SetOption (":smt.case_split", "3", None);
      SetOption (":smt.candidate_models", "true", None);
      (* Call nlsat on the non-linear part of a query only after many final checks:
         most proofs do not need it, and early calls make the search slower and its
         time more variable. *)
      SetOption (":smt.arith.nl.delay", "200", None);
    ]
    @ if diagnostics then [ SetOption (":smt.qi.profile", "true", None) ] else []
  in

  let list_of_cmds =
    [
      mk_declare_sort loc_ident 0;
      mk_declare_const
        (QualIdent.from_ident (Ident.make Util.Loc.dummy "null" 0))
        Type.ref;
      mk_declare_sort atomic_token_ident 0;
    ]
  in

  Base.List.iter options_list ~f:(write session);
  Base.List.iter list_of_cmds ~f:(write session);

  write_comment session "End of Preamble";
  write_comment session "";
  write_comment session ""

(** Declares the tuple sorts used by the fully lowered program. *)
let declare_tuple_sorts (session : SmtSolver.session) (arities : int list) : unit =
  let open Session in
  match arities with
  | [] -> ()
  | _ ->
      write_comment session "Tuple sorts used by this program";
      Base.List.iter arities ~f:(fun arity -> write session (declare_tuple_sort arity));
      write_comment session ""
