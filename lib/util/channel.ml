open Stdlib

let null_channel () =
  (let devnull = if (Sys.os_type = "Win32") then "NUL" else "/dev/null" in
         Stdio.Out_channel.create devnull);