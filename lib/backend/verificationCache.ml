(** The fingerprints of the proof obligations verified before (see [Fingerprints]), kept
    in a directory between runs. A failure to read or write the cache only costs its use.
*)

open Base

type t = {
  file : string;
  known : (string, float) Hashtbl.t;  (** Each fingerprint, with when it was last used. *)
}

(** At most this many fingerprints are kept, those used last. *)
let capacity = 50_000

let file_name dir = Stdlib.Filename.concat dir "verified"

let read file : (string, float) Hashtbl.t =
  let known = Hashtbl.create (module String) in
  begin match Result.try_with (fun () -> Stdio.In_channel.read_lines file) with
  | Error _ -> ()
  | Ok lines ->
      List.iter lines ~f:(fun line ->
          match String.split line ~on:' ' with
          | [ fingerprint; used ] ->
              Option.iter (Float.of_string_opt used) ~f:(fun used ->
                  Hashtbl.set known ~key:fingerprint ~data:used)
          | _ -> ())
  end;
  known

let rec make_dir dir =
  if not (Stdlib.Sys.file_exists dir) then begin
    make_dir (Stdlib.Filename.dirname dir);
    Unix.mkdir dir 0o755
  end

let load dir = { file = file_name dir; known = read (file_name dir) }
let mem cache fingerprint = Hashtbl.mem cache.known fingerprint

(** Adds the fingerprints [used] in this run, hits or newly verified, to those in the
    cache now, which another run may have extended meanwhile. *)
let save cache ~(used : string list) =
  if not (List.is_empty used) then begin
    let now = Unix.gettimeofday () in
    let known = read cache.file in
    List.iter used ~f:(fun fingerprint -> Hashtbl.set known ~key:fingerprint ~data:now);
    let entries =
      Hashtbl.to_alist known
      |> List.sort ~compare:(fun (_, t1) (_, t2) -> Float.compare t2 t1)
      |> Fn.flip List.take capacity
    in
    let dir = Stdlib.Filename.dirname cache.file in
    let written =
      Result.try_with (fun () ->
          make_dir dir;
          let temp = Stdlib.Filename.temp_file ~temp_dir:dir "verified" ".tmp" in
          Stdio.Out_channel.write_lines temp
            (List.map entries ~f:(fun (fingerprint, used) ->
                 Printf.sprintf "%s %.0f" fingerprint used));
          Unix.rename temp cache.file)
    in
    match written with
    | Ok () -> ()
    | Error exn ->
        Logs.warn (fun m ->
            m "Could not save the verification cache in %s: %s" dir (Exn.to_string exn))
  end
