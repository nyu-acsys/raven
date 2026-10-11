open Base
open Ast
open Util
open Smt
module Session = SmtSolver.SmtSession

type context = {
  session : SmtSolver.session;
  path_conditions : expr list;
  auto_dependencies : Dependencies.Graph.t;
}

type 'a t = context -> context * 'a

let create session =
  { session; path_conditions = []; auto_dependencies = Dependencies.Graph.empty }

let write cmd : unit t =
  let open State.Syntax in
  match cmd with
  | SmtLibAst.Assert _ ->
      Error.internal_error Loc.dummy
        "Cannot write assert command directly; use assume_expr instead"
  | _ ->
      let+ context = get_state in
      Session.write context.session cmd

let write_comment comment : unit t =
  let open State.Syntax in
  let+ context = get_state in
  Session.write_comment context.session comment

let push =
  let open State.Syntax in
  map_state ~f:(fun context -> { context with session = Session.push context.session })

let pop =
  let open State.Syntax in
  map_state ~f:(fun context -> { context with session = Session.pop context.session })

let push_path_condn term =
  let open State.Syntax in
  map_state ~f:(fun context ->
      { context with path_conditions = term :: context.path_conditions })

let pop_path_condn =
  let open State.Syntax in
  map_state ~f:(fun context ->
      { context with path_conditions = List.tl_exn context.path_conditions })

let under_path_conditions context expr =
  match context.path_conditions with
  | [] -> expr
  | conditions -> Expr.mk_impl (Expr.mk_and conditions) expr

let assume_expr ?name expr : unit t =
  let open State.Syntax in
  let+ context = get_state in
  let expr = under_path_conditions context expr |> Expr.drop_trivially_true in
  Session.assert_expr ?name context.session expr

let check_valid ?name expr : SmtSolver.validity_result t =
  let open State.Syntax in
  let* context = get_state in
  Logs.debug (fun m -> m "Checking validity of %a" Expr.pr_verbose expr);
  let expr = under_path_conditions context expr in
  let result, session = Session.check_valid ?name context.session expr in
  let+ () = set_state { context with session } in
  result
