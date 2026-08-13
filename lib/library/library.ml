let base_types = [%blob "base_types.rav"]
let resource_algebra = [%blob "resource_algebra.rav"]
let atomics = [%blob "atomics.rav"]

(* Each source is named by its path relative to the repository root, not by its bare
   basename. That path is the source's identity everywhere downstream: it is what
   [Loc.file_name] carries for a location inside the library, what `--dump-stdlib`
   reproduces on disk, and what lets a location be resolved back to a real file when the
   binary is running inside a checkout (see [Config.library_source_path]). Basenames
   would collide as soon as two extensions shipped a file with the same name. *)
let sources =
  [ ("lib/library/base_types.rav", base_types);
    ("lib/library/resource_algebra.rav", resource_algebra);
    ("lib/library/atomics.rav", atomics) ]
