open Raven_api

let loc = Loc.none
let id value = Ident.make ~loc value
let name value = Name.make ~loc value
let var value = Expr.var ~loc (name value)
let typ = Type.named ~loc (name "T") []

let func operation inputs output body =
  Callable.func ~loc
    ~formals:(List.map (fun input -> Var.make ~loc (id input) typ) inputs)
    ~returns:[ Var.make ~loc (id "result") output ]
    (id operation) (Some body)
  |> Member.callable

let program =
  let subtract = Expr.binary ~loc Expr.Minus (var "a") (var "b") in
  let members =
    [
      Member.type_ ~loc ~rep:true (id "T") (Some (Type.int ~loc));
      Member.value ~loc ~const:true ~typ (id "id") (Some (Expr.int ~loc 0));
      func "comp" [ "a"; "b" ] typ subtract;
      func "frame" [ "a"; "b" ] typ (var "a");
      func "valid" [ "a" ] (Type.bool ~loc) (Expr.bool ~loc true);
      func "fpuAllowed" [ "a"; "b" ] (Type.bool ~loc) (Expr.bool ~loc true);
    ]
  in
  Program.make ~loc
    [
      Member.module_ ~loc
        ~implements:[ (Name.make ~loc ~path:[ "Library" ] "ResourceAlgebra", []) ]
        (id "Bad") members;
    ]

let () =
  let result = verify program in
  let diagnostics =
    String.concat "\n"
      (List.map
         (fun (d : Diagnostic.t) ->
           Printf.sprintf "%s @%d, related=[%s]" d.message (Loc.start d.loc).pos_lnum
             (String.concat "; "
                (List.map
                   (fun (r : Diagnostic.related) ->
                     Printf.sprintf "%s @%d" r.related_message
                       (Loc.start r.related_loc).pos_lnum)
                   d.related)))
         result.diagnostics)
  in
  if result.verified then failwith "Invalid resource algebra verified";
  let inherited_law message =
    String.starts_with ~prefix:"Lemma compCommute inherited from axiom" message
  in
  if
    not
      (List.exists
         (fun (diagnostic : Diagnostic.t) ->
           diagnostic.kind = Verification
           && List.exists
                (fun (related : Diagnostic.related) ->
                  inherited_law related.related_message)
                diagnostic.related)
         result.diagnostics)
  then failwith diagnostics;
  assert (
    not
      (List.exists
         (fun (diagnostic : Diagnostic.t) ->
           diagnostic.kind = Other && inherited_law diagnostic.message)
         result.diagnostics))
