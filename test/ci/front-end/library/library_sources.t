Raven's library sources are embedded in the binary rather than being files on disk, so a
diagnostic pointing into one names no openable path. These two options hand the text
back out: `--dump-library` writes them all, reproducing the paths they are reported
under, and `--print-library-source` emits one. An editor uses the latter to display a
library location; both produce exactly the bytes this binary verifies against.

  $ dune exec -- raven --shh --dump-library ./dumped
  ./dumped/lib/library/base_types.rav
  ./dumped/lib/library/resource_algebra.rav
  ./dumped/lib/library/atomics.rav
  ./dumped/lib/ext/prophecyExt/prophecyLib.rav
  ./dumped/lib/ext/decreasesExt/well_founded_order.rav

The set follows the active extension, since that is what was verified against.

  $ dune exec -- raven --shh --extension eris --dump-library ./dumped-eris
  ./dumped-eris/lib/library/base_types.rav
  ./dumped-eris/lib/library/resource_algebra.rav
  ./dumped-eris/lib/library/atomics.rav
  ./dumped-eris/lib/ext/errorCreditsExt/errorCreditsLib.rav
  ./dumped-eris/lib/ext/decreasesExt/well_founded_order.rav

A single source, named as diagnostics report it, goes to stdout.

  $ dune exec -- raven --shh --print-library-source lib/library/base_types.rav | head -3
  interface Type {
    rep type T
  }

Printing and dumping agree, and neither depends on the working directory.

  $ dune exec -- raven --shh --print-library-source lib/library/resource_algebra.rav | diff - ./dumped/lib/library/resource_algebra.rav && echo identical
  identical

An unknown name is reported rather than silently producing nothing.

  $ dune exec -- raven --shh --print-library-source lib/library/nope.rav
  [Error] No library source named 'lib/library/nope.rav'. Known sources: lib/library/base_types.rav, lib/library/resource_algebra.rav, lib/library/atomics.rav, lib/ext/prophecyExt/prophecyLib.rav, lib/ext/decreasesExt/well_founded_order.rav
