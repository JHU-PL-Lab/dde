type t = Ddeast.expr * int list

let return e = (e, [])

let ( >>= ) m f =
  let e, sigma = m in
  let e', sigma' = f e in
  (e', sigma' @ sigma)

(* let push  *)