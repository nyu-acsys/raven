let base_types = [%blob "base_types.rav"]
let resource_algebra = [%blob "resource_algebra.rav"]
let well_founded_order = [%blob "well_founded_order.rav"]

let sources =
  [ ("base_types.rav", base_types);
    ("resource_algebra.rav", resource_algebra);
    ("well_founded_order.rav", well_founded_order) ]
