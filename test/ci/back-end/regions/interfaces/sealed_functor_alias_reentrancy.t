  $ dune exec -- raven --shh ./sealed_functor_alias_reentrancy.rav
  [Error] Type Error: Cannot establish invariant namespace separation between GenInst$$Q_5F24Program_24_240_24_24Actual_24_240$$Q_5F24Program_24_240_24_24TypeMod_5F24_5F24QLibrary_5F5F24_5F5F240_5F5F24_5F5F24Type_5F5F24_5F5F240_5F24_5F24Int_24_240.leaf and GenInst$$Q_5F24Program_24_240_24_24Sealed_5F24Hidden_24_240$$Q_5F24Program_24_240_24_24TypeMod_5F24_5F24QLibrary_5F5F24_5F5F240_5F5F24_5F5F24Type_5F5F24_5F5F240_5F24_5F24Int_24_240.root
  [Error] File "./sealed_functor_alias_reentrancy.rav", line 30, columns 2-17:
  30 |   Public.step(x);
         ^^^^^^^^^^^^^^^
  Related Location: This generic check requires the namespaces to be disjoint.
  [1]
