open Base
open Ast
open Smt.SmtLibAst
open Smt.SmtSolver

let with_response response f =
  let reply_file = Stdlib.Filename.temp_file "raven-smt-reply-" ".txt" in
  let query_file = Stdlib.Filename.temp_file "raven-smt-query-" ".smt2" in
  Stdio.Out_channel.write_all reply_file ~data:(response ^ "\n");
  let in_chan = Stdio.In_channel.create reply_file in
  let out_chan = Stdio.Out_channel.create query_file in
  Stdlib.Fun.protect
    ~finally:(fun () ->
      Stdio.In_channel.close in_chan;
      Stdio.Out_channel.close out_chan;
      Stdlib.Sys.remove reply_file;
      Stdlib.Sys.remove query_file)
    (fun () ->
      let session : SmtSession.session =
        {
          stack_height = 2;
          solver_state =
            {
              out_descr = Unix.descr_of_out_channel out_chan;
              in_descr = Unix.descr_of_in_channel in_chan;
              pid = None;
              log_out_chan = None;
              response_timeout = Some 1.;
              pending_input = "";
              closed = false;
            };
        }
      in
      f session)

let () =
  List.iter
    [ ("sat", Sat, Invalid); ("unsat", Unsat, Valid); ("unknown", Unknown, Inconclusive) ]
    ~f:(fun (response, expected_sat, expected_validity) ->
      with_response response (fun session ->
          let before = !SmtSession.num_of_sat_queries in
          let result = SmtSession.check_sat session in
          assert (Poly.equal result expected_sat);
          assert (!SmtSession.num_of_sat_queries = before + 1));
      with_response response (fun session ->
          let before = !SmtSession.num_of_sat_queries in
          let result, restored = SmtSession.check_valid session (Expr.mk_bool true) in
          assert (Poly.equal result expected_validity);
          assert (restored.stack_height = session.stack_height);
          assert (!SmtSession.num_of_sat_queries = before + 1)));
  List.iter [ ""; "timeout"; "success"; "(error \"bad query\")" ] ~f:(fun response ->
      assert (Result.is_error (parse_sat_result response)))
