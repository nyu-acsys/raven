(* Parses each file given, prints it, parses the printed text again and prints it once
   more: the printer produces parseable Raven if both printed texts agree. *)

open Base
open Util

let parse ~file_name text =
  let diagnostics = Diagnostics.create () in
  let includes = Driver.create_includes () in
  let lexbuf = Lexing.from_string text in
  Frontend.Lexer.set_file_name lexbuf file_name;
  let _, md =
    Driver.parse_cu ~diagnostics ~includes
      (Stdlib.Filename.dirname (Stdlib.Sys.getcwd () ^ "/" ^ file_name))
      Ast.Predefs.prog_ident lexbuf
  in
  md

let printers =
  let (module E) = Ext.module_map Ext.ProphecyExt in
  Ast.Rewriter.printers_of_ext_hooks (Ext.to_ext_hooks (module E : ExtApi.Ext))

let print (md : Ast.Module.t) =
  Stdlib.Format.asprintf "%a" printers.pr_module_instrs md.mod_def

let check file_name =
  let text = Stdio.In_channel.read_all file_name in
  match parse ~file_name text with
  | exception _ -> `Unparseable
  | md -> (
      match print md with
      | exception exn -> `Reparse_failed ("printing raised " ^ Exn.to_string exn, "")
      | printed -> (
          match parse ~file_name:(file_name ^ " (printed)") printed with
          | exception Error.Msg errs ->
              let _, loc, msg = List.hd_exn errs in
              let line =
                List.nth (String.split_lines printed) (Loc.start_line loc - 1)
                |> Option.value ~default:""
              in
              `Reparse_failed
                (Printf.sprintf "%s\n    at: %s" msg (String.strip line), printed)
          | exception exn -> `Reparse_failed (Exn.to_string exn, printed)
          | md' ->
              let printed' = print md' in
              if String.equal printed printed' then `Ok else `Differs (printed, printed'))
      )

let () =
  let files = List.tl_exn (Array.to_list (Sys.get_argv ())) in
  let ok, unparseable, failed =
    List.fold files ~init:(0, 0, []) ~f:(fun (ok, unparseable, failed) file ->
        match check file with
        | `Ok -> (ok + 1, unparseable, failed)
        | `Unparseable -> (ok, unparseable + 1, failed)
        | `Reparse_failed (msg, _) -> (ok, unparseable, (file, msg) :: failed)
        | `Differs (printed, printed') ->
            Option.iter (Sys.getenv "ROUNDTRIP_DUMP") ~f:(fun dir ->
                Stdio.Out_channel.write_all (dir ^ "/first.rav") ~data:printed;
                Stdio.Out_channel.write_all (dir ^ "/second.rav") ~data:printed');
            let first_difference =
              (fun a b ->
                ( List.zip_exn
                    (List.take a (min (List.length a) (List.length b)))
                    (List.take b (min (List.length a) (List.length b))),
                  () ))
                (String.split_lines printed) (String.split_lines printed')
              |> fst
              |> List.find ~f:(fun (l, l') -> not (String.equal l l'))
              |> Option.value_map ~default:"(lengths differ)" ~f:(fun (l, l') ->
                  Printf.sprintf "%s\n    vs: %s" (String.strip l) (String.strip l'))
            in
            ( ok,
              unparseable,
              (file, "printed texts differ: " ^ first_difference) :: failed ))
  in
  Stdio.printf "ok: %d, unparseable inputs: %d, failed: %d\n" ok unparseable
    (List.length failed);
  List.iter (List.rev failed) ~f:(fun (file, msg) -> Stdio.printf "%s\n  %s\n" file msg)
