open Base

let rec respond response reason =
  match Stdio.In_channel.input_line Stdio.In_channel.stdin with
  | None -> ()
  | Some line ->
      begin match String.strip line with
      | "(check-sat)" -> (
          (* With RAVEN_TEST_HANG, the first query of the first process gets no answer. *)
          match Sys.getenv "RAVEN_TEST_HANG" with
          | Some path when not (Stdlib.Sys.file_exists path) ->
              Stdio.Out_channel.write_all path ~data:""
          | _ -> Logs.app (fun m -> m "%s" response))
      | "(get-info :reason-unknown)" ->
          Logs.app (fun m -> m "(:reason-unknown \"%s\")" reason)
      | "(get-info :version)" -> Logs.app (fun m -> m "(:version \"stub\")")
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
