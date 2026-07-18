  $ dune exec -- raven --shh ./import_all_uninstantiated_functor.rav
  [Error] File "./import_all_uninstantiated_functor.rav", line 5, columns 0-23:
  5 | import Library.Option._
      ^^^^^^^^^^^^^^^^^^^^^^^
  Type Error: Cannot import all members of `Library.Option` because it is a generic functor that has not been instantiated; write `import Library.Option[...]._` after an explicit instantiation.
  [1]
