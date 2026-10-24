open Base
open Raven

let parse text =
  let lexbuf = Lexing.from_string text in
  Frontend.Lexer.set_file_name lexbuf "atomic_parser.rav";
  let _, program =
    Driver.parse_cu ~diagnostics:(Util.Diagnostics.create ())
      ~includes:(Driver.create_includes ()) "." Ast.Predefs.prog_ident lexbuf
  in
  program

let two_calls members =
  match members with
  | [ Ast.Module.SymbolDef (CallDef first); Ast.Module.SymbolDef (CallDef second) ] ->
      assert (String.equal (Ast.Ident.name second.call_decl.call_decl_name) "g");
      assert second.call_decl.call_decl_physical_atomic;
      assert (
        List.for_all second.call_decl.call_decl_precond ~f:(fun spec ->
            not spec.Ast.Stmt.spec_atomic));
      assert (
        List.for_all second.call_decl.call_decl_postcond ~f:(fun spec ->
            not spec.Ast.Stmt.spec_atomic));
      (first, second)
  | _ -> failwith "expected separate callable declarations"

let () =
  let prefixes =
    [
      "func f() returns (r: Int)";
      "func f(x: Int) returns (r: Int) requires true ensures r == x";
      "func f(; r: Int) requires true ensures r == 0";
      "proc f()";
      "proc f() requires true ensures true";
      "lemma f()";
      "axiom f()";
      "pred f()";
      "inv f()";
    ]
  in
  List.iter prefixes ~f:(fun prefix ->
      List.iter
        [ " "; "\n"; "/* comment */"; " /* outer\n /* nested */ */\n"; " // comment\n" ]
        ~f:(fun separator ->
          let source =
            prefix ^ "\natomic" ^ separator ^ "proc g() requires true ensures true"
          in
          let first, _ = two_calls (parse source).mod_def in
          assert (not first.call_decl.call_decl_physical_atomic)));
  let first, _ =
    two_calls
      (parse
         "proc f() atomic requires true atomic ensures true\n\
          atomic proc g() requires true ensures true")
        .mod_def
  in
  assert (not first.call_decl.call_decl_physical_atomic);
  assert (
    List.for_all first.call_decl.call_decl_precond ~f:(fun spec ->
        spec.Ast.Stmt.spec_atomic));
  assert (
    List.for_all first.call_decl.call_decl_postcond ~f:(fun spec ->
        spec.Ast.Stmt.spec_atomic));
  let first, _ =
    two_calls
      (parse
         "atomic proc f() requires true ensures true\n\
          atomic proc g() requires true ensures true")
        .mod_def
  in
  assert first.call_decl.call_decl_physical_atomic

let () =
  let program =
    parse
      "interface I { func f() returns (r: Int)\n\
       atomic /* comment */ proc g() requires true ensures true }"
  in
  match program.mod_def with
  | [ Ast.Module.SymbolDef (ModDef m) ] -> ignore (two_calls m.mod_def)
  | _ -> failwith "expected an interface"

let () =
  let first, _ =
    two_calls
      (parse
         "proc f() {\n\
          assert true\n\
          atomic\n\
          { assert true; }\n\
          assert true\n\
          }\n\
          atomic proc g() {}")
        .mod_def
  in
  match first.call_def with
  | ProcDef { proc_body = Some { stmt_desc = Block { block_body; _ }; _ } } ->
      assert (List.length block_body = 3);
      begin match List.nth_exn block_body 1 with
      | { stmt_desc = Block { block_kind = Atomic; _ }; _ } -> ()
      | _ -> failwith "expected a physical atomic block"
      end
  | _ -> failwith "expected a procedure body"

let () =
  let prefix = "atomic /* outer\n /* nested */ */\n" in
  let lexbuf = Lexing.from_string (prefix ^ "proc") in
  let next = Frontend.Lexer.make_token ~warn:(fun _ _ -> assert false) () in
  assert (Poly.equal (next lexbuf) Frontend.Parser.ATOMIC_PROC);
  assert (lexbuf.lex_start_p.pos_cnum = 0);
  assert (lexbuf.lex_curr_p.pos_cnum = String.length "atomic");
  assert (lexbuf.lex_curr_p.pos_lnum = 1);
  assert (Poly.equal (next lexbuf) Frontend.Parser.PROC);
  assert (lexbuf.lex_start_p.pos_cnum = String.length prefix);
  assert (lexbuf.lex_curr_p.pos_cnum = String.length prefix + String.length "proc");
  assert (lexbuf.lex_start_p.pos_lnum = 3);
  assert (Poly.equal (next lexbuf) Frontend.Parser.EOF)

let () =
  let warnings = ref [] in
  let next =
    Frontend.Lexer.make_token ~warn:(fun loc _ -> warnings := loc :: !warnings) ()
  in
  let lexbuf = Lexing.from_string "atomic {|" in
  assert (Poly.equal (next lexbuf) Frontend.Parser.ATOMIC);
  assert (List.is_empty !warnings);
  assert (Poly.equal (next lexbuf) Frontend.Parser.LBRACEPIPE);
  match !warnings with
  | [ loc ] -> assert (Util.Loc.start_index loc = String.length "atomic ")
  | _ -> failwith "expected a warning at the buffered token"

let chunked text =
  let position = ref 0 in
  Lexing.from_function (fun bytes requested ->
      let length = Int.min 7 (Int.min requested (String.length text - !position)) in
      Stdlib.Bytes.blit_string text !position bytes 0 length;
      position := !position + length;
      length)

let () =
  let comment = " /* " ^ String.make 10000 'x' ^ " */ " in
  let prefix = "func f() returns (r: Int) { " in
  let lexbuf = chunked (prefix ^ "atomic" ^ comment ^ "42 }") in
  match
    Driver.parse_cu ~diagnostics:(Util.Diagnostics.create ())
      ~includes:(Driver.create_includes ()) "." Ast.Predefs.prog_ident lexbuf
  with
  | _ -> failwith "expected an invalid atomic expression"
  | exception Util.Error.Msg errors ->
      assert (
        List.exists errors ~f:(fun (_, loc, message) ->
            String.equal message "Unexpected token 'atomic'"
            && Util.Loc.start_index loc = String.length prefix + String.length "atomic"))

let () =
  let prefix = "atomic /* " ^ String.make 10000 'x' ^ " */ " in
  let lexbuf = chunked (prefix ^ "proc") in
  let next = Frontend.Lexer.make_token ~warn:(fun _ _ -> assert false) () in
  assert (Poly.equal (next lexbuf) Frontend.Parser.ATOMIC_PROC);
  assert (lexbuf.lex_curr_p.pos_cnum = String.length "atomic");
  assert (Poly.equal (next lexbuf) Frontend.Parser.PROC);
  assert (lexbuf.lex_start_p.pos_cnum = String.length prefix)
