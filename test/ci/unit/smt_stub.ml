open Base

let rec respond response reason =
  match Stdio.In_channel.input_line Stdio.In_channel.stdin with
  | None -> ()
  | Some line ->
      begin match String.strip line with
      | "(check-sat)" -> Logs.app (fun m -> m "%s" response)
      | "(get-info :reason-unknown)" ->
          Logs.app (fun m -> m "(:reason-unknown \"%s\")" reason)
      | _ -> ()
      end;
      respond response reason

let () =
  Logs.set_reporter (Logs_fmt.reporter ~app:Fmt.stdout ());
  Option.iter (Sys.getenv "RAVEN_TEST_STARTED") ~f:(fun path ->
      Stdio.Out_channel.write_all path ~data:"");
  respond
    (Option.value (Sys.getenv "RAVEN_TEST_RESPONSE") ~default:"unsat")
    (Option.value (Sys.getenv "RAVEN_TEST_REASON") ~default:"incomplete quantifiers")
