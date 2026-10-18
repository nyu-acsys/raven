(* Rendering the solver's model values in source terms. *)

open Base
module Counterexample = Backend.Counterexample

let sexp = Sexplib.Sexp.of_string

(* The names of one counterexample: null, and its abstract values in the order shown. *)
let names = Hashtbl.of_alist_exn (module String) [ ("$Loc!val!1", "null") ]
let reference = Counterexample.abstract_values names

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
      ("$Loc!val!0", "Ref#1");
      ("$Loc!val!1", "null");
      ("$Loc!val!0", "Ref#1");
      ("$Loc!val!5", "Ref#2");
      ("TicketLock.R.T!val!0", "R#1");
      ("M.K!val!2", "K#1");
      ("GenInst$$Library_Seq$$TypeMod$$Library_Type$$Int.T!val!3", "Seq#1");
      ("$tuple_0", "()");
      ("($tuple_2 1 true)", "(1, true)");
      ("Library.List.nil", "nil");
      ("(Library.List.cons 1 Library.List.nil)", "cons(1, nil)");
      ( "(let ((a!1 (Library.List.cons 2 Library.List.nil))) (Library.List.cons 1 a!1))",
        "cons(1, cons(2, nil))" );
      ("(store (store ((as const (Set Int)) false) 1 true) 3 true)", "{|1, 3|}");
      ("(store (store ((as const (Set Int)) false) 1 true) 1 false)", "{||}");
      ("(store ((as const (Set Int)) true) 2 false)", "all but {|2|}");
      ( "(store (store ((as const (Array Int Int)) 4) 1 5) 2 6)",
        "[1 := 5, 2 := 6, else 4]" );
      ("(store (store ((as const (Array Int Int)) 4) 1 5) 1 7)", "[1 := 7, else 4]");
      ("((as const (Array Int Int)) 0)", "[else 0]");
      ("(_ as-array k!0)", "…");
      ("(lambda ((x Int)) (= x 1))", "…");
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
      (Some "Ref#1 (permission 1/2)"));
  assert (Option.is_none (field "Frac$f.frac_null"));
  assert (Option.equal String.equal (field "Agree.agree_top") (Some "agree_top"))
