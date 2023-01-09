type set = int list list

let analyze (e : Ddeast.expr) : Ddeinterp.result_value * set =
  (BoolResult false, [])
