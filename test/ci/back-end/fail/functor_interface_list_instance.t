  $ dune exec -- raven --shh ./functor_interface_list_instance.rav
  [Error] File "./functor_interface_list_instance.rav", line 29, columns 9-61:
  29 |   assert CellFns.located(List.::(1, List.::(2, List.nil)), 3);
                ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  Verification Error: This assertion may be violated.
  [1]
