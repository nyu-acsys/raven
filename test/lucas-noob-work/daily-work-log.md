# additional polish, small bug reports
- If we have more bindings on the left than are available, i.e:
lk, p, r := openAU(phi)

we get this error: [Error] length mismatch in fold2_exn: 1 <> 3, which is a bit
confusing. Error would be nicer if it directly pointed to the openAU call
instead of fold2_exn, which I assume is used somewhere in the underlying layers
of the openAU implementation.
