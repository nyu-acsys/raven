  $ dune exec -- raven --shh ./resource_alias_inline.rav
  [Error] File "./resource_alias_inline.rav", line 2, columns 25-29:
  2 | module Bad { inline pred cell(x: Ref) = cell }
                               ^^^^
  Type Error: A resource alias cannot declare contracts, locals or callable modifiers.
  [1]
