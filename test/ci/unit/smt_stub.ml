open Base

let rec respond response =
  match Stdio.In_channel.input_line Stdio.In_channel.stdin with
  | None -> ()
  | Some line ->
      if String.equal (String.strip line) "(check-sat)" then
        Logs.app (fun m -> m "%s" response);
      respond response

let () =
  Logs.set_reporter (Logs_fmt.reporter ~app:Fmt.stdout ());
  Option.iter (Sys.getenv "RAVEN_TEST_STARTED") ~f:(fun path ->
      Stdio.Out_channel.write_all path ~data:"");
  respond (Option.value (Sys.getenv "RAVEN_TEST_RESPONSE") ~default:"unsat")
