(* Parses each file given, prints it, parses the printed text again and prints it once
   more: the printer writes parseable Raven if both printed texts agree. Files that do not
   parse are skipped, as are files whose syntax belongs to more than one extension, which
   no single chain of extensions prints. Fails with the files whose round trip does not
   hold. With ROUNDTRIP_DUMP set to a directory, the printed texts of a failing file are
   written there. *)

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

(* With the printers of the extension the program's syntax selects, as `--extension auto`
   does, or of the default one where that cannot be decided. *)
let printers (md : Ast.Module.t) =
  let extension = try Ext.detect_extension md with Error.Msg _ -> Ext.ProphecyExt in
  let (module E) = Ext.module_map extension in
  Ast.Rewriter.printers_of_ext_hooks (Ext.to_ext_hooks (module E : ExtApi.Ext))

let print (printers : Ast.Rewriter.printers) (md : Ast.Module.t) =
  Stdlib.Format.asprintf "%a" printers.pr_module_instrs md.mod_def

let dump printed printed' =
  Option.iter (Sys.getenv "ROUNDTRIP_DUMP") ~f:(fun dir ->
      Stdio.Out_channel.write_all (dir ^ "/first.rav") ~data:printed;
      Stdio.Out_channel.write_all (dir ^ "/second.rav") ~data:printed')

let line text n = List.nth (String.split_lines text) (n - 1) |> Option.value ~default:""

let first_difference printed printed' =
  let lines, lines' = (String.split_lines printed, String.split_lines printed') in
  let common = Int.min (List.length lines) (List.length lines') in
  List.zip_exn (List.take lines common) (List.take lines' common)
  |> List.find ~f:(fun (l, l') -> not (String.equal l l'))
  |> Option.value_map ~default:"the printed texts differ in length" ~f:(fun (l, l') ->
      Printf.sprintf "%s\n    then: %s" (String.strip l) (String.strip l'))

(** Why the round trip of [file_name] fails, if it does. *)
let check file_name =
  let text = Stdio.In_channel.read_all file_name in
  let parsed = try Some (parse ~file_name text) with Error.Msg _ -> None in
  let printed =
    Option.bind parsed ~f:(fun md ->
        try Some (printers md, print (printers md) md) with Error.Msg _ -> None)
  in
  match printed with
  | None -> None
  | Some (printers, printed) -> (
      match parse ~file_name:(file_name ^ " (printed)") printed with
      | exception Error.Msg errs ->
          dump printed "";
          let _, loc, msg = List.hd_exn errs in
          Some
            (Printf.sprintf "%s\n    at: %s" msg
               (String.strip (line printed (Loc.start_line loc))))
      | md' ->
          let printed' = print printers md' in
          if String.equal printed printed' then None
          else begin
            dump printed printed';
            Some ("printed again differently: " ^ first_difference printed printed')
          end)

let () =
  let files = List.tl_exn (Array.to_list (Sys.get_argv ())) in
  let failures =
    List.filter_map files ~f:(fun file ->
        Option.map (check file) ~f:(fun why -> (file, why)))
  in
  List.iter failures ~f:(fun (file, why) -> Stdio.printf "%s\n  %s\n" file why);
  if not (List.is_empty failures) then Stdlib.exit 1
