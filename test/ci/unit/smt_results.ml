open Base
open Raven
open Backend
open Ast
open Smt.SmtLibAst
open Smt.SmtSolver

let with_response response f =
  let reply_file = Stdlib.Filename.temp_file "raven-smt-reply-" ".txt" in
  let query_file = Stdlib.Filename.temp_file "raven-smt-query-" ".smt2" in
  Stdio.Out_channel.write_all reply_file ~data:(response ^ "\n");
  let session =
    SmtSession.ForTesting.of_owned_descriptors ~response_timeout:(Some 1.)
      ~input:(Unix.openfile reply_file [ Unix.O_RDONLY ] 0)
      ~output:(Unix.openfile query_file [ Unix.O_WRONLY ] 0)
      ()
  in
  Stdlib.Fun.protect
    ~finally:(fun () ->
      stop session;
      Stdlib.Sys.remove reply_file;
      Stdlib.Sys.remove query_file)
    (fun () -> f session)

let () =
  List.iter
    [
      ("sat", Sat, Invalid);
      ("unsat", Unsat, Valid);
      ("unknown\n(:reason-unknown \"(incomplete quantifiers)\")", Unknown, Inconclusive);
      ("unknown\n(:reason-unknown \"timeout\")", Unknown, Timeout);
      ("unknown\n(:reason-unknown \"canceled\")", Unknown, Timeout);
    ]
    ~f:(fun (response, expected_sat, expected_validity) ->
      with_response response (fun session ->
          let result = SmtSession.check_sat session in
          assert (Poly.equal result expected_sat));
      with_response response (fun session ->
          SmtSession.with_scope session ~f:(fun () ->
              SmtSession.with_scope session ~f:(fun () ->
                  let result = SmtSession.check_valid session (Expr.mk_bool true) in
                  assert (Poly.equal result expected_validity);
                  assert (SmtSession.ForTesting.stack_height session = 2)));
          assert (SmtSession.ForTesting.stack_height session = 0)));
  List.iter [ ""; "timeout"; "success"; "(error \"bad query\")" ] ~f:(fun response ->
      assert (Result.is_error (parse_sat_result response)))

let () =
  with_response "unexpected" (fun session ->
      assert (
        Result.is_error
          (Result.try_with (fun () -> SmtSession.check_valid session (Expr.mk_bool true))));
      assert (SmtSession.ForTesting.stack_height session = 0));
  with_response "unsat" (fun session ->
      List.iter
        [
          mk_push 1;
          mk_pop 1;
          mk_check_sat ();
          mk_get_model ();
          mk_get_unsat_core ();
          mk_exit ();
        ]
        ~f:(fun command ->
          assert (
            Result.is_error (Result.try_with (fun () -> SmtSession.write session command))));
      assert (SmtSession.ForTesting.stack_height session = 0));
  let session = init ~logging:false 10000 in
  Stdlib.Fun.protect
    ~finally:(fun () -> stop session)
    (fun () ->
      let result =
        Result.try_with (fun () ->
            SmtSession.with_scope session ~f:(fun () ->
                SmtSession.assert_expr session (Expr.mk_bool false);
                failwith "scope body error"))
      in
      assert (
        match result with
        | Error (Failure message) -> String.equal message "scope body error"
        | _ -> false);
      assert (Poly.equal (SmtSession.check_sat session) Sat);
      SmtSession.with_scope session ~f:(fun () ->
          SmtSession.assert_expr session (Expr.mk_bool false);
          SmtSession.with_scope session ~f:(fun () ->
              assert (Poly.equal (SmtSession.check_sat session) Unsat));
          assert (Poly.equal (SmtSession.check_sat session) Unsat));
      assert (Poly.equal (SmtSession.check_sat session) Sat))
