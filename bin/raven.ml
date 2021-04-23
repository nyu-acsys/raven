open Base

let greeting =
  "Raven version " ^ Config.version ^ "\n"
                                              
let usage_message =
  greeting ^
  "\nUsage:\n  " ^ (Sys.get_argv ()).(0) ^ 
  " <input file> [options]\n"

let _ =
  Stdlib.Arg.parse Config.cmd_options_spec (fun _ -> ()) usage_message
