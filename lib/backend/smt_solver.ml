open Unix
open Util__Error

let num_of_sat_queries = ref 0

type solver_state = 
    { out_chan: out_channel;
      in_chan: in_channel;
      pid: int;
      mutable response_count: int;
    }


type session = { 
  log_file_name: string;
	mutable assert_count: int;
  mutable response_count: int;
	(* mutable sat_checked: (solver_state option * response) option; *)
	stack_height: int;
  (* signature: (arity list SymbolMap.t) option; *)
  (* user_sorts: sort IdMap.t; *)
  (* named_clauses: (string, form) Hashtbl.t option; *)
  solver_state: solver_state
}

let start_solver () = 
  let in_read, in_write = Unix.pipe () in
  let out_read, out_write = Unix.pipe () in
  let pid = Unix.create_process "z3" [| "smt2"; "-in" |] out_read in_write in_write in

  close out_read;
  close in_write;

  let solver_state = {
    in_chan = in_channel_of_descr in_read;
    out_chan = out_channel_of_descr out_write;
    pid = pid;
    response_count = 0;
  } in

  {
    log_file_name = "log.smt";
    assert_count = 0;
    response_count = 0;
    stack_height = 0;
    solver_state = solver_state;
  }

let write session cmd =
  output_string session.solver_state.out_chan cmd

let writeln session cmd = 
  write session (cmd ^ "\n")

(* let read_from_chan session chan =
  let lexbuf = Lexing.from_channel chan in
  SmtLibLexer.set_file_name lexbuf session.log_file_name; 
  try
    SmtLibParser.output SmtLibLexer.token lexbuf
  with ProgError.Prog_error (pos, _) ->
    let tok = Lexing.lexeme lexbuf in
    let tail = SmtLibLexer.ruleTail "" lexbuf in
    let msg = 
      "failed to parse SMT solver response while parsing: " ^ tok ^ tail
    in
    ProgError.syntax_error pos (Some msg) *)


let read session = 
  let in_descr = 
    descr_of_in_channel session.solver_state.in_chan
       
  in

  flush session.solver_state.out_chan;
  (* let rec loop () = *)
    let ready, _, _ = Unix.select [in_descr] [] [] (-1.) in

    let in_descr = List.hd ready in
    let in_chan = in_channel_of_descr in_descr in
    let result = In_channel.input_line in_chan in
    match result with
    | None -> raise (Generic_Error "Read from SMT Solver returned nothing")
    | Some str -> str
    (* state.response_count <- state.response_count + 1; *)
    (* if state.response_count > session.response_count
    then begin
      session.response_count <- session.response_count + 1;
      Some state, result
    end *)
    (* else () *)
  (* in
  loop ()
   *)

let is_sat session = 
  incr num_of_sat_queries;
  writeln session "(check-sat)";
  match (read session) with
  | "sat" -> true
  | "unsat" -> false
  | "unknown" -> false
  | _ -> raise (Generic_Error "Unexpected Solver output")


let is_unsat session = 
  incr num_of_sat_queries;
  writeln session "(check-sat)";
  match (read session) with
  | "unsat" -> true
  | "sat" -> false
  | "unknown" -> false
  | _ -> raise (Generic_Error "Unexpected Solver output")
(* in
  session.sat_checked <- Some response;
  match snd response with
  | Sat -> Some true
  | Unsat -> Some false
  | Unknown -> None
  | Error e -> fail session e
  | _ -> fail session "unexpected response from prover" *)
  

let init () =
  let session = start_solver () in
  writeln session "(declare-const x Int)";
  writeln session "(assert (= x 5))";
  is_sat session;

