open Base
open Ast

let () =
  let open Smt.SmtLibAst in
  let name = "smt_printing_test" in
  let term = Expr.mk_bool true in
  let first = mk_assert ~name term in
  let second = mk_assert ~name term in
  let first_printing = command_to_string first in
  assert (String.equal first_printing (command_to_string first));
  assert (not (String.equal first_printing (command_to_string second)));

  let unnamed = mk_assert term in
  let before = Ident.fresh Util.Loc.dummy "$hyp$" in
  ignore (command_to_string unnamed);
  ignore (command_to_string unnamed);
  let after = Ident.fresh Util.Loc.dummy "$hyp$" in
  assert (after.ident_num = before.ident_num + 1)

let () =
  let open Smt.SmtLibAst in
  assert (match mk_get_unsat_core () with GetUnsatCore _ -> true | _ -> false);
  assert (
    String.equal
      (String.strip (command_to_string (mk_get_unsat_core ())))
      "(get-unsat-core)")

let test_logging logging =
  let open Smt.SmtSolver in
  let solver_file = Stdlib.Filename.temp_file "raven-smt-solver-" ".smt2" in
  let log_file = Stdlib.Filename.temp_file "raven-smt-log-" ".smt2" in
  let log_out_chan = if logging then Some (Stdio.Out_channel.create log_file) else None in
  let session =
    SmtSession.ForTesting.of_owned_descriptors ?log_out_chan ~response_timeout:(Some 1.)
      ~input:(Unix.openfile solver_file [ Unix.O_RDONLY ] 0)
      ~output:(Unix.openfile solver_file [ Unix.O_WRONLY ] 0)
      ()
  in
  Stdlib.Fun.protect
    ~finally:(fun () ->
      stop session;
      Stdlib.Sys.remove solver_file;
      Stdlib.Sys.remove log_file)
    (fun () ->
      let command = Smt.SmtLibAst.mk_assert ~name:"bounds'" (Expr.mk_bool true) in
      SmtSession.write_comment session "first line\nsecond line";
      SmtSession.write session command;
      let sent = Stdio.In_channel.read_all solver_file in
      let expected =
        Smt.SmtLibAst.comment_to_string "first line\nsecond line"
        ^ Smt.SmtLibAst.command_to_string command
      in
      assert (String.equal sent expected);
      let logged = Stdio.In_channel.read_all log_file in
      assert (String.equal logged (if logging then sent else "")))

let () =
  test_logging true;
  test_logging false
