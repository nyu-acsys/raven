(lang dune 3.12)
(using menhir 2.1)
(map_workspace_root false)

(generate_opam_files)

(source (github nyu-acsys/raven))

(authors "Ekanshdeep Gupta" "Nisarg Patel" "Thomas Wies")

(maintainers "Ekanshdeep Gupta" "Nisarg Patel" "Thomas Wies")

(license MIT)

(package
 (name Raven)
 (synopsis "Intermediate verification language and deductive verifier for concurrent programs")
 (description "Raven is an intermediate verification language and SMT-based deductive verifier based on concurrent separation logic. It is intended as an intermediate layer for building program verification tools that target concurrent programs. Raven can also be used as a standalone educational tool.")
 (depends
  (ocaml
   (>= 4.12.0))
  (dune
   (>= 3.12))
  (z3
   (>= 4.13.0))
  (ocamlformat
   (>= 0.26.2))
  (base
   (>= 0.14))
  (stdio
   (>= 0.14))
  (logs
   (>= 0.7.0))
  (fmt
   (>= 0.9.0))
  (cmdliner
   (>= 1.2.0))
  (ppx_custom_printf
   (>= 0.14.1))
  (ppx_compare
   (>= 0.14.0))
  (ppx_hash
   (>= 0.14.0))
  (ppx_sexp_conv
   (>= 0.14.3))
  (ppx_let
   (>= 0.16.0))
  (ppx_blob
   (>= 0.7.2))  
 )
)
