open Base
open Raven
module R = Raven_api

let loc = Util.Loc.dummy
let id ?(num = 0) name = Ast.Ident.make loc name num

let parse text =
  let diagnostics = Util.Diagnostics.create () in
  let includes = Driver.create_includes () in
  let lexbuf = Lexing.from_string text in
  Frontend.Lexer.set_file_name lexbuf "source_printing.rav";
  let _, md = Driver.parse_cu ~diagnostics ~includes "." Ast.Predefs.prog_ident lexbuf in
  md

let print md =
  let (module E) = Ext.module_map Ext.ProphecyExt in
  let printers =
    Ast.Rewriter.printers_of_ext_hooks (Ext.to_ext_hooks (module E : ExtApi.Ext))
  in
  Stdlib.Format.asprintf "%a" printers.pr_module_instrs md.Ast.Module.mod_def

let check_printer ~pr ~print ~to_string value =
  let expected = to_string value in
  assert (String.equal expected (Stdlib.Format.asprintf "%a" pr value));
  let path, channel =
    Stdlib.Filename.open_temp_file ~mode:[ Stdlib.Open_binary ] "raven-api-printing"
      ".txt"
  in
  print channel value;
  let input = Stdlib.open_in_bin path in
  let actual = Stdlib.really_input_string input (Stdlib.in_channel_length input) in
  Stdlib.close_in input;
  (* The channel stays open and the formatter has already flushed its output. *)
  Stdlib.output_string channel "suffix";
  Stdlib.close_out channel;
  Stdlib.Sys.remove path;
  assert (String.equal actual expected);
  expected

let roundtrip program =
  let text =
    check_printer ~pr:R.Program.pr ~print:R.Program.print ~to_string:R.Program.to_string
      program
  in
  assert (String.equal text (R.Program.to_string program));
  assert (not (String.mem text '`'));
  assert (String.equal text (print (parse text)));
  text

let () =
  List.iter [ "value"; "Module"; "proof$facts_auth"; "$key"; "proc"; "a.b" ]
    ~f:(fun name ->
      List.iter [ 0; 1; 3 ] ~f:(fun num ->
          let original = id ~num name in
          let expected = if num = 0 then name else Printf.sprintf "%s^%d" name num in
          assert (String.equal (Ast.Ident.to_string original) expected)));
  let qualified =
    Ast.QualIdent.make [ id ~num:2 "Generated$Module" ] (id "proof$field")
  in
  assert (
    String.equal (Ast.QualIdent.to_string qualified) "Generated$Module^2.proof$field")

let () =
  assert (
    Stdlib.Hashtbl.length Frontend.Terminals.keyword_table
    = List.length Ast.SourceKeywords.entries);
  List.iter Ast.SourceKeywords.entries ~f:(fun (name, keyword) ->
      assert (Stdlib.Hashtbl.mem Frontend.Terminals.keyword_table name);
      assert (Ast.SourceKeywords.is_keyword name);
      let next = Frontend.Lexer.make_token () in
      let actual = next (Lexing.from_string name) ~warn:(fun _ _ -> assert false) in
      assert (Poly.equal actual (Frontend.Terminals.keyword_token keyword)));
  Stdlib.Hashtbl.iter
    (fun spelling _ -> assert (not (Ast.SourceKeywords.is_keyword spelling)))
    Frontend.Terminals.operator_table

let () =
  let tokens text =
    let next = Frontend.Lexer.make_token () in
    let lexbuf = Lexing.from_string text in
    let rec collect acc =
      match next lexbuf ~warn:(fun _ _ -> assert false) with
      | Frontend.Parser.EOF -> List.rev acc
      | token -> collect (token :: acc)
    in
    collect []
  in
  List.iter Frontend.Terminals.negated_keywords ~f:(fun (word, token) ->
      assert (Ast.SourceKeywords.is_keyword word);
      assert (not (Ast.SourceKeywords.is_keyword ("!" ^ word)));
      assert (Poly.equal (tokens ("!" ^ word)) [ token ]);
      match tokens ("!" ^ word ^ "side") with
      | [ actual; Frontend.Parser.IDENT suffix ] ->
          assert (Poly.equal actual token);
          assert (String.equal (Ast.Ident.name suffix) "side");
          assert (Util.Loc.start_index (Ast.Ident.to_loc suffix) = 1 + String.length word)
      | _ -> failwith "negated keyword prefix changed");
  begin match tokens "!value" with
  | [ Frontend.Parser.NOT; IDENT name ] ->
      assert (String.equal (Ast.Ident.name name) "value");
      assert (Util.Loc.start_index (Ast.Ident.to_loc name) = 1)
  | _ -> failwith "ordinary negation changed"
  end;
  begin match tokens "!!in" with
  | [ Frontend.Parser.EQOPSYM op; IN ] -> assert (String.equal (Ast.Ident.name op) "!!")
  | _ -> failwith "symbolic operator maximal munch changed"
  end

let () =
  Stdlib.Hashtbl.iter
    (fun keyword _ ->
      if (not (String.is_empty keyword)) && Char.is_lowercase keyword.[0] then begin
        let original = id keyword in
        let next = Frontend.Lexer.make_token () in
        let lexbuf = Lexing.from_string (Ast.Ident.to_source_string original) in
        match next lexbuf ~warn:(fun _ _ -> assert false) with
        | Frontend.Parser.IDENT actual -> assert (Ast.Ident.equal original actual)
        | _ -> failwith ("keyword is not printed as an identifier: " ^ keyword)
      end)
    Frontend.Terminals.keyword_table

let () =
  let loc = R.Loc.none in
  let id name = R.Ident.make ~loc name in
  let q name = R.Name.make ~loc name in
  let var name = R.Expr.var ~loc (q name) in
  let fields =
    [
      "proof$facts_auth";
      "proof.facts_auth";
      "proof_facts_auth_1";
      "";
      "?";
      "choose";
      "subseteq";
      "in";
      "a`b";
      "a\\b";
      "a\nb";
      "a\000b";
      "true";
    ]
  in
  let program =
    R.Program.make ~loc
      (List.map fields ~f:(fun name -> R.Member.field ~loc (id name) (R.Type.int ~loc))
      @ [
          R.Member.module_ ~loc (id "Generated$Module")
            [ R.Member.type_ ~loc (id "T$Value") (Some (R.Type.int ~loc)) ];
          R.Member.callable
            (R.Callable.proc ~loc
               ~formals:[ R.Var.make ~loc (id "proc") (R.Type.ref ~loc) ]
               ~returns:[ R.Var.make ~loc (id "return") (R.Type.int ~loc) ]
               (id "read$value")
               (Some
                  [
                    R.Stmt.assign ~loc
                      [ var "return" ]
                      (R.Stmt.expr_rhs
                         (R.Expr.field ~loc (var "proc") (q "proof$facts_auth")));
                  ]));
        ])
  in
  let text = roundtrip program in
  assert (not (String.mem text '$'));
  let parsed = parse text in
  let field_names =
    List.filter_map parsed.mod_def ~f:(function
      | Ast.Module.SymbolDef (FieldDef field) ->
          Some (Ast.Ident.to_string field.field_name)
      | _ -> None)
  in
  assert (Set.length (Set.of_list (module String) field_names) = List.length fields);
  assert (List.mem field_names "proof_facts_auth_1" ~equal:String.equal);
  assert (List.mem field_names "proof_facts_auth_2" ~equal:String.equal);
  assert (List.mem field_names "proof_facts_auth_3" ~equal:String.equal)

let () =
  let loc = R.Loc.none in
  let id name = R.Ident.make ~loc name in
  let name s = R.Name.make ~loc s in
  let var s = R.Expr.var ~loc (name s) in
  let ctor = id "case$some" and none = id "case$none" in
  let data =
    R.Type.data ~loc
      [
        R.Type.variant ~loc ctor [ (id "value$field", R.Type.int ~loc) ];
        R.Type.variant ~loc none [];
      ]
  in
  let cases =
    [
      (R.Expr.Case (ctor, [ id "value$bound" ]), var "value$bound");
      (R.Expr.Case (none, []), R.Expr.int ~loc 0);
    ]
  in
  let assign e = R.Stmt.assign ~loc [ var "return" ] (R.Stmt.expr_rhs e) in
  let get =
    R.Callable.proc ~loc
      ~formals:
        [ R.Var.make ~loc (id "input$value") (R.Type.named ~loc (name "S$Value") []) ]
      ~returns:[ R.Var.make ~loc (id "return") (R.Type.int ~loc) ]
      ~ensures:
        [
          R.Spec.make
            (R.Expr.binary ~loc Eq (var "return")
               (R.Expr.match_ ~loc (var "input$value") cases));
        ]
      (id "match$value")
      (Some
         [
           R.Stmt.match_ ~loc (var "input$value")
             (List.map cases ~f:(fun (pattern, body) -> (pattern, [ assign body ])));
         ])
  in
  let program =
    R.Program.make ~loc
      [ R.Member.type_ ~loc (id "S$Value") (Some data); R.Member.callable get ]
  in
  let text = roundtrip program in
  assert (not (String.mem text '$'))

let () =
  let loc = R.Loc.none in
  let label = R.Spec.make ~name:"proof$label" (R.Expr.bool ~loc true) in
  let p =
    R.Callable.proc ~loc
      (R.Ident.make ~loc "labelled")
      (Some [ R.Stmt.assert_ ~loc label ])
  in
  let text = roundtrip (R.Program.make ~loc [ R.Member.callable p ]) in
  assert (not (String.mem text '$'))

let config : Driver.config =
  {
    no_library = false;
    typecheck_only = false;
    lsp_mode = false;
    lsp_annotations = false;
    base_dir = "";
    prog_stats = false;
    smt_timeout = 10000;
    smt_diagnostics = false;
    max_errors = None;
    log_level = None;
    strict = false;
    only = None;
    counterexamples = false;
    fingerprints = false;
    cache_dir = None;
  }

let verifies text =
  Ast.Ident.restore ();
  match
    Driver.check_program ~includes:(Driver.create_includes ())
      ~extension_mode:(`Explicit Ext.ProphecyExt)
      ~diagnostics:(Util.Diagnostics.create ()) config (parse text)
  with
  | () -> true
  | exception Util.Error.Msg errors ->
      assert (not (List.is_empty errors));
      false

let () =
  let loc = R.Loc.none in
  let id name = R.Ident.make ~loc name in
  let name s = R.Name.make ~loc s in
  let var s = R.Expr.var ~loc (name s) in
  let program wrong =
    let f =
      R.Callable.func ~loc
        ~formals:
          (List.map [ "x$value"; "x_value_1" ] ~f:(fun n ->
               R.Var.make ~loc (id n) (R.Type.int ~loc)))
        ~returns:[ R.Var.make ~loc (id "result") (R.Type.int ~loc) ]
        ~ensures:[ R.Spec.make (R.Expr.binary ~loc Eq (var "result") (var "x$value")) ]
        (id "pick$value")
        (Some (var (if wrong then "x_value_1" else "x$value")))
    in
    R.Program.make ~loc [ R.Member.callable f ]
  in
  assert (verifies (roundtrip (program false)));
  assert (not (verifies (roundtrip (program true))))

let () =
  let rejected text =
    match parse text with _ -> false | exception Util.Error.Msg _ -> true
  in
  assert (rejected "lemma capture() { val `$key`: Int := 7; }");
  assert (rejected "lemma access() { assert `M$Impl`.hidden() == 42; }")

let () =
  List.iter [ Ast.Stmt.Fold; Unfold ] ~f:(fun kind ->
      let name = if Poly.equal kind Ast.Stmt.Fold then "fold" else "unfold" in
      let pred = Ast.QualIdent.from_ident (id "p") in
      let argument =
        Ast.Expr.mk_var ~typ:Ast.Type.ref (Ast.QualIdent.from_ident (id "x"))
      in
      let statement witnesses =
        Ast.Surface.Stmt.at ~loc (Ast.Surface.Stmt.use kind pred ~witnesses [ argument ])
      in
      assert (String.equal (Ast.Stmt.to_string (statement [])) (name ^ " p(x)"));
      assert (
        String.equal
          (Ast.Stmt.to_string (statement [ (id "n", Ast.Expr.mk_int 7) ]))
          (name ^ " p(x)[n := 7]")))

let () =
  let expression =
    Ast.Surface.Expr.tuple_get ~loc
      (Ast.Surface.Expr.tuple ~loc [ Ast.Expr.mk_int 7; Ast.Expr.mk_bool true ])
      0
  in
  let parsed =
    parse ("func projection() returns (r: Int) { " ^ Ast.Expr.to_string expression ^ " }")
  in
  match parsed.mod_def with
  | [
   Ast.Module.SymbolDef
     (CallDef { call_def = FuncDef { func_body = Some (App (TupleLookUp, _, _)) }; _ });
  ] ->
      ()
  | _ -> failwith "a tuple projection must remain a projection"

let () =
  let text =
    "func chained(r: (Ref, Map[Int, Int])) returns (v: Int) { (r#0).value + (r#1)[0] }"
  in
  let printed = print (parse text) in
  assert (String.equal printed (print (parse printed)));
  assert (String.is_substring printed ~substring:"r#0.value");
  assert (String.is_substring printed ~substring:"r#1[0]")

let () =
  let expression text =
    let program = parse ("func sample() returns (result: Int) { " ^ text ^ " }") in
    match program.mod_def with
    | [
     Ast.Module.SymbolDef (CallDef { call_def = FuncDef { func_body = Some body }; _ });
    ] ->
        body
    | _ -> failwith "expected a function body"
  in
  List.iter
    [
      ("r#0.next", "(r#0).next");
      ("r#1[0]", "(r#1)[0]");
      ("r#1[0 := v].next", "((r#1)[0 := v]).next");
      ("r#0#1.next", "((r#0)#1).next");
      ("r.value[0]#1.next", "((r.value[0])#1).next");
      ("M.N.f(r)#0.next", "(M.N.f(r)#0).next");
      ("r#0.(M.value)", "(r#0).(M.value)");
      ("r#0[lo..hi].next", "((r#0)[lo..hi]).next");
    ]
    ~f:(fun (chained, grouped) ->
      assert (Int.equal (Ast.Expr.compare (expression chained) (expression grouped)) 0))

let () =
  let loc = R.Loc.none in
  let expression = R.Expr.binary ~loc Plus (R.Expr.int ~loc 1) (R.Expr.int ~loc 2) in
  let _ =
    check_printer ~pr:R.Expr.pr ~print:R.Expr.print ~to_string:R.Expr.to_string expression
  in
  let diagnostic : R.Diagnostic.t =
    {
      severity = Error;
      kind = Verification;
      code = None;
      loc;
      message = "sample diagnostic";
      related = [ { related_loc = loc; related_message = "related location" } ];
    }
  in
  let _ =
    check_printer ~pr:R.Diagnostic.pr ~print:R.Diagnostic.print
      ~to_string:R.Diagnostic.to_string diagnostic
  in
  let formals =
    List.init 8 ~f:(fun i ->
        R.Var.make ~loc
          (R.Ident.make ~loc ("parameter_" ^ Int.to_string i))
          (R.Type.int ~loc))
  in
  let program =
    R.Program.make ~loc
      [
        R.Member.callable
          (R.Callable.proc ~loc ~formals (R.Ident.make ~loc "sample") None);
      ]
  in
  let render margin =
    let buffer = Buffer.create 128 in
    let ppf = Stdlib.Format.formatter_of_buffer buffer in
    Stdlib.Format.pp_set_margin ppf margin;
    R.Program.pr ppf program;
    Stdlib.Format.pp_print_flush ppf ();
    Buffer.contents buffer
  in
  let narrow = render 40 and wide = render 200 in
  assert (not (String.equal narrow wide));
  assert (String.equal (print (parse narrow)) (print (parse wide)))
