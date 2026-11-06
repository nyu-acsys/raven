open Base
open Raven_api

let loc line =
  let position =
    {
      Lexing.pos_fname = "progress.ml";
      pos_lnum = line;
      pos_bol = line * 10;
      pos_cnum = line * 10;
    }
  in
  Loc.make position { position with pos_cnum = position.pos_cnum + 4 }

let procedure line name valid =
  let loc = loc line in
  Callable.proc ~loc (Ident.make ~loc name)
    (Some [ Stmt.assert_ ~loc (Spec.make (Expr.bool ~loc valid)) ])
  |> Member.callable

let report (snapshot : Progress.t) =
  let pending =
    List.filter snapshot.checks ~f:(fun check -> Poly.equal check.outcome Pending)
  in
  List.iter snapshot.checks ~f:(fun check ->
      let position = Loc.start check.loc in
      assert (String.equal position.pos_fname "progress.ml");
      assert (String.equal check.kind "proc");
      assert (
        (String.is_suffix check.name ~suffix:"good" && position.pos_lnum = 2)
        || (String.is_suffix check.name ~suffix:"bad" && position.pos_lnum = 4)));
  match snapshot.phase with
  | Typed ->
      assert (List.is_empty snapshot.checks);
      assert (List.is_empty snapshot.diagnostics);
      Logs.app (fun m -> m "typed")
  | Scheduled ->
      assert (List.length snapshot.checks = 2);
      assert (List.length pending = 2);
      Logs.app (fun m -> m "scheduled pending=%d" (List.length pending))
  | Progress ->
      if List.is_empty pending then begin
        assert (
          List.exists snapshot.checks ~f:(fun check ->
              String.is_suffix check.name ~suffix:"good"
              && Poly.equal check.outcome Verified));
        assert (
          List.exists snapshot.checks ~f:(fun check ->
              String.is_suffix check.name ~suffix:"bad" && Poly.equal check.outcome Failed));
        assert (
          List.exists snapshot.diagnostics ~f:(fun diagnostic ->
              Poly.equal diagnostic.kind Diagnostic.Verification))
      end;
      Logs.app (fun m -> m "progress pending=%d" (List.length pending))
  | Final ->
      assert (List.is_empty pending);
      assert (not (List.is_empty snapshot.diagnostics));
      Logs.app (fun m -> m "final")

let () =
  Logs.set_reporter (Logs_fmt.reporter ~app:Fmt.stdout ());
  let program =
    Program.make ~loc:(loc 1) [ procedure 2 "good" true; procedure 4 "bad" false ]
  in
  let result = verify ~on_progress:report program in
  assert (not result.verified);
  let errors =
    List.count result.diagnostics ~f:(fun diagnostic ->
        Poly.equal diagnostic.kind Diagnostic.Verification)
  in
  assert (errors = 1);
  Logs.app (fun m -> m "verified=%b verification-errors=%d" result.verified errors)
