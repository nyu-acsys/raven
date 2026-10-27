open Base
open Raven
module R = Raven_api

let loc = R.Loc.none
let id value = R.Ident.make ~loc value
let name ?path value = R.Name.make ~loc ?path value
let variable value = R.Expr.var ~loc (name value)
let integer_type = R.Type.int ~loc
let local_type = R.Type.named ~loc (name "T") []
let formals typ = [ R.Var.make ~loc (id "x") typ ]
let returns () = [ R.Var.make ~loc (id "v") integer_type ]

let resource_members typ cell_body shared_body =
  [
    R.Member.callable
      (R.Callable.func ~loc ~kind:Pred ~formals:(formals typ) ~returns:(returns ())
         (id "cell") cell_body);
    R.Member.callable
      (R.Callable.func ~loc ~kind:Inv ~formals:(formals typ) (id "shared") shared_body);
  ]

let aliases target =
  [
    R.Member.callable
      (R.Callable.resource_alias ~loc ~formals:(formals local_type) ~returns:(returns ())
         (id "cell")
         (name ~path:[ target ] "cell"));
    R.Member.callable
      (R.Callable.resource_alias ~loc ~kind:Invariant ~formals:(formals local_type)
         (id "shared")
         (name ~path:[ target ] "shared"));
  ]

let assertions owner =
  let call member args = R.Expr.call ~loc (name ~path:[ owner ] member) args in
  R.Spec.make
    (R.Expr.binary ~loc And
       (call "cell" [ variable "x"; variable "v" ])
       (call "shared" [ variable "x" ]))

let program =
  let concrete_type = R.Member.type_ ~loc (id "T") (Some integer_type) in
  R.Program.make ~loc
    [
      R.Member.module_ ~loc ~interface:true (id "Resource")
        (R.Member.type_ ~loc (id "T") None :: resource_members local_type None None);
      R.Member.module_ ~loc
        ~implements:[ (name "Resource", []) ]
        (id "Actual")
        (concrete_type
        :: resource_members local_type
             (Some (R.Expr.binary ~loc Eq (variable "v") (variable "x")))
             (Some (R.Expr.bool ~loc true)));
      R.Member.module_ ~loc
        ~implements:[ (name "Resource", []) ]
        (id "View")
        (concrete_type :: aliases "Actual");
      R.Member.module_ ~loc (id "Chain") (concrete_type :: aliases "View");
      R.Member.callable
        (R.Callable.proc ~loc ~kind:Lemma
           ~formals:
             [
               R.Var.make ~loc (id "x") integer_type;
               R.Var.make ~loc ~ghost:true (id "v") integer_type;
             ]
           ~requires:[ assertions "Actual" ]
           ~ensures:[ assertions "Chain" ]
           (id "same") (Some []));
    ]

let check_emission () =
  let source = R.Program.to_string program in
  let lexbuf = Lexing.from_string source in
  Frontend.Lexer.set_file_name lexbuf "resource_aliases_api.rav";
  let _, parsed =
    Driver.parse_cu ~diagnostics:(Util.Diagnostics.create ())
      ~includes:(Driver.create_includes ()) "." Ast.Predefs.prog_ident lexbuf
  in
  let count = ref 0 in
  List.iter parsed.mod_def ~f:(function
    | Ast.Module.SymbolDef (ModDef module_) ->
        List.iter module_.mod_def ~f:(function
          | Ast.Module.SymbolDef (CallDef callable)
            when Option.is_some callable.call_decl.call_decl_alias ->
              Int.incr count;
              begin match callable.call_decl.call_decl_kind with
              | Pred ->
                  begin match callable.call_decl.call_decl_returns with
                  | [ output ] ->
                      assert output.var_implicit;
                      assert output.var_ghost
                  | _ -> failwith "predicate alias lost its output"
                  end
              | Invariant -> assert (List.is_empty callable.call_decl.call_decl_returns)
              | Func | Proc | Lemma -> failwith "resource alias changed kind"
              end;
              begin match callable.call_def with
              | FuncDef { func_body = None } -> ()
              | FuncDef { func_body = Some _ } | ProcDef _ ->
                  failwith "resource alias acquired a body"
              end
          | _ -> ())
    | _ -> ());
  assert (!count = 4)

let () =
  check_emission ();
  let result = R.verify program in
  if not result.verified then
    failwith
      (String.concat ~sep:"\n" (List.map result.diagnostics ~f:R.Diagnostic.to_string))
