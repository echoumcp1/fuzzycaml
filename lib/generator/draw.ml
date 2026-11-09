open Hegel

let int tc lo hi = draw_silent tc (integers ~min_value:lo ~max_value:hi ())
let bool ?p tc = draw_silent tc (booleans ?p ())
let unbounded tc = draw_silent tc (integers ())
let float tc generator = draw_silent tc generator
