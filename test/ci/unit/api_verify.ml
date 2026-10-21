(* Builds programs through the API, as a front end does, prints and verifies them. The
   locations are those of a source in another language, here lines of `incr.ml`. *)

open Raven_api

let line n =
  let pos = { Lexing.pos_fname = "incr.ml"; pos_lnum = n; pos_bol = 0; pos_cnum = 0 } in
  Loc.make pos pos

let name s = Name.make ~loc:Loc.none s
let ident s = Ident.make ~loc:Loc.none s

(* field f: Int
   proc incr(x: Ref) requires own(x.f, 0, 1.0) ensures own(x.f, result, 1.0)
   { x.f := 1; } *)
let program ~result =
  let x = Expr.var ~loc:(line 3) (name "x") in
  let own loc v =
    Expr.own ~loc [ Expr.field ~loc x (name "f"); Expr.int ~loc v; Expr.real ~loc 1.0 ]
  in
  let incr =
    Callable.proc ~loc:(line 2)
      ~formals:[ Var.make ~loc:(line 2) (ident "x") (Type.ref ~loc:(line 2)) ]
      ~requires:[ Spec.make (own (line 2) 0) ]
      ~ensures:[ Spec.make (own (line 2) result) ]
      (ident "incr")
      (Some
         [
           Stmt.assign ~loc:(line 3)
             [ Expr.field ~loc:(line 3) x (name "f") ]
             (Stmt.expr_rhs (Expr.int ~loc:(line 3) 1));
         ])
  in
  Program.make ~loc:(line 1)
    [
      Member.field ~loc:(line 1) (ident "f") (Type.int ~loc:(line 1));
      Member.callable incr;
    ]

let report program =
  print_endline (Program.to_string program);
  let result = verify program in
  Printf.printf "verified: %b\n" result.verified;
  List.iter
    (fun (d : Diagnostic.t) ->
      Printf.printf "%s at line %d: %s\n"
        (match d.kind with Verification -> "verification" | _ -> "other")
        (Loc.start d.loc).pos_lnum d.message)
    result.diagnostics

let () =
  Printf.printf "raven.api version %d\n\n" version;
  report (program ~result:1);
  print_newline ();
  report (program ~result:2)
