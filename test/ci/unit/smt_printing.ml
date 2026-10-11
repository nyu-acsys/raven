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
  let open Smt.SmtSolver.SmtSession in
  let solver_file = Stdlib.Filename.temp_file "raven-smt-solver-" ".smt2" in
  let log_file = Stdlib.Filename.temp_file "raven-smt-log-" ".smt2" in
  let solver_out = Stdio.Out_channel.create solver_file in
  let log_out = Stdio.Out_channel.create log_file in
  let solver_in = Stdio.In_channel.create solver_file in
  Stdlib.Fun.protect
    ~finally:(fun () ->
      Stdio.Out_channel.close solver_out;
      Stdio.Out_channel.close log_out;
      Stdio.In_channel.close solver_in;
      Stdlib.Sys.remove solver_file;
      Stdlib.Sys.remove log_file)
    (fun () ->
      let session =
        {
          stack_height = 0;
          solver_state =
            {
              out_descr = Unix.descr_of_out_channel solver_out;
              in_descr = Unix.descr_of_in_channel solver_in;
              pid = None;
              log_out_chan = Some log_out;
              response_timeout = Some 1.;
              pending_input = "";
              closed = false;
            };
        }
      in
      let command = Smt.SmtLibAst.mk_assert ~name:"bounds'" (Expr.mk_bool true) in
      write_comment session "first line\nsecond line";
      write session command;
      let logged = Stdio.In_channel.read_all log_file in
      let sent = Stdio.In_channel.read_all solver_file in
      assert (String.equal logged sent);
      let session =
        { session with solver_state = { session.solver_state with log_out_chan = None } }
      in
      write_comment session "first line\nsecond line";
      write session command;
      assert (String.equal (Stdio.In_channel.read_all log_file) logged);
      assert (String.equal (Stdio.In_channel.read_all solver_file) (sent ^ sent)))
