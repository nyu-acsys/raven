(* Rendering the solver's model values in source terms. *)

open Base
module Counterexample = Backend.Counterexample

let sexp = Sexplib.Sexp.of_string

let reference = function
  | "$Loc!val!0" -> Some "ref#1"
  | "$Loc!val!1" -> Some "null"
  | _ -> None

let render text =
  Counterexample.render ~reference (Counterexample.expand_lets (sexp text))

let field text = Counterexample.render_field ~reference (sexp text)

let () =
  List.iter
    [
      ("3", "3");
      ("(- 2)", "-2");
      ("1.0", "1");
      ("(/ 1.0 2.0)", "1/2");
      ("(- (/ 1.0 4.0))", "-1/4");
      ("true", "true");
      ("$Loc!val!0", "ref#1");
      ("$Loc!val!1", "null");
      ("Library.List.nil", "nil");
      ("(Library.List.cons 1 Library.List.nil)", "cons(1, nil)");
      ( "(let ((a!1 (Library.List.cons 2 Library.List.nil))) (Library.List.cons 1 a!1))",
        "cons(1, cons(2, nil))" );
      ("((as const (Array Int Bool)) false)", "…");
      ("(store a 1 2)", "…");
    ]
    ~f:(fun (value, expected) ->
      let shown = render value in
      if not (String.equal shown expected) then
        Printf.failwithf "%s is shown as %s, not %s" value shown expected ())

let () =
  assert (
    Option.equal String.equal
      (field "(Frac$f.frac_chunk 4 1.0)")
      (Some "4 (permission 1)"));
  assert (
    Option.equal String.equal
      (field "(Frac$f.frac_chunk $Loc!val!0 (/ 1.0 2.0))")
      (Some "ref#1 (permission 1/2)"));
  assert (Option.is_none (field "Frac$f.frac_null"));
  assert (Option.equal String.equal (field "Agree.agree_top") (Some "agree_top"))
