open Base
open Raven_api

let loc = Loc.none
let ident name = Ident.make ~loc name

let procedure name valid =
  Callable.proc ~loc (ident name)
    (Some [ Stmt.assert_ ~loc (Spec.make ~name:(name ^ "_check") (Expr.bool ~loc valid)) ])
  |> Member.callable

let program = Program.make ~loc [ procedure "good" true; procedure "bad" false ]

let select name (check : Progress.check) =
  assert (Poly.equal check.outcome Pending);
  assert (List.mem [ "proc"; "lemma" ] check.kind ~equal:String.equal);
  String.equal check.name name

let run ?cache_dir ?select_member program =
  let snapshots = ref [] in
  let on_progress snapshot = snapshots := snapshot :: !snapshots in
  let result = verify ?cache_dir ?select_member ~on_progress program in
  let final = List.hd_exn !snapshots in
  assert (Poly.equal final.phase Final);
  (result, List.rev !snapshots)

let checks snapshots = (List.last_exn snapshots).Progress.checks

let assert_selected name snapshots =
  List.iter snapshots ~f:(fun (snapshot : Progress.t) ->
      List.iter snapshot.checks ~f:(fun (check : Progress.check) ->
          assert (String.equal check.name name || String.equal check.name (name ^ "_check"))));
  assert (
    List.exists (checks snapshots) ~f:(fun (check : Progress.check) ->
        String.equal check.name name))

let assert_verification_error (result : result) =
  assert (not result.verified);
  assert (
    List.exists result.diagnostics ~f:(fun diagnostic ->
        Poly.equal diagnostic.kind Diagnostic.Verification))

let test_names () =
  let result, snapshots = run ~select_member:(select "good") program in
  assert result.verified;
  assert_selected "good" snapshots;
  let result, snapshots = run ~select_member:(select "bad") program in
  assert_verification_error result;
  assert_selected "bad" snapshots

let test_frontend () =
  let malformed =
    Callable.proc ~loc (ident "malformed")
      (Some [ Stmt.assert_ ~loc (Spec.make (Expr.int ~loc 0)) ])
    |> Member.callable
  in
  let result, snapshots =
    run ~select_member:(select "good")
      (Program.make ~loc [ procedure "good" true; malformed ])
  in
  assert (not result.verified);
  assert (List.is_empty (checks snapshots));
  assert (
    List.exists result.diagnostics ~f:(fun diagnostic ->
        Poly.equal diagnostic.kind Diagnostic.Type))

let test_generated () =
  let function_ =
    Callable.func ~loc (ident "function_")
      ~returns:[ Var.make ~loc (ident "r") (Type.int ~loc) ]
      ~ensures:[ Spec.make (Expr.bool ~loc false) ]
      (Some (Expr.int ~loc 0))
    |> Member.callable
  in
  let result, snapshots =
    run
      ~select_member:(select "$function__contract")
      (Program.make ~loc [ function_; procedure "good" true ])
  in
  assert_verification_error result;
  assert_selected "$function__contract" snapshots

let test_cache () =
  let cache_dir = Stdlib.Filename.temp_file "raven-selection-" "" in
  Stdlib.Sys.remove cache_dir;
  let cleanup () =
    let cache = Stdlib.Filename.concat cache_dir "verified" in
    if Stdlib.Sys.file_exists cache then Stdlib.Sys.remove cache;
    if Stdlib.Sys.file_exists cache_dir then Unix.rmdir cache_dir
  in
  Stdlib.Fun.protect ~finally:cleanup (fun () ->
      let result, snapshots = run ~cache_dir ~select_member:(select "good") program in
      assert result.verified;
      assert_selected "good" snapshots;
      let result, snapshots = run ~cache_dir ~select_member:(select "bad") program in
      assert_verification_error result;
      assert_selected "bad" snapshots;
      let result, snapshots = run ~cache_dir program in
      assert_verification_error result;
      assert (
        List.exists (checks snapshots) ~f:(fun (check : Progress.check) ->
            String.equal check.name "good" && Poly.equal check.outcome Cached));
      assert (
        List.exists (checks snapshots) ~f:(fun (check : Progress.check) ->
            String.equal check.name "bad" && Poly.equal check.outcome Failed)))

let () =
  test_names ();
  test_frontend ();
  test_generated ();
  test_cache ()
