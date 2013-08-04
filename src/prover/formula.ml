type t = Var of string | App of string * t list

let mk_app op xs = App (op, xs)
let mk_var v = Var v

let eq _ _ = failwith "TODO"
let hash _ = failwith "TODO"

let mk_0 op = mk_app op []
let mk_1 op a = mk_app op [a]
let mk_2 op a b = mk_app op [a; b]

let mk_star = mk_2 "*"
let mk_big_star = mk_app "*"
let mk_or = mk_2 "or"

let mk_eq = mk_2 "=="

let mk_string_const s = mk_1 "<string>" (mk_0 s)
let mk_int_const s = mk_1 "<int>" (mk_0 s)

let is_interpreted _ = failwith "TODO"


let emp = mk_0 "emp"
let fls = mk_0 "fls"

let pp _ = failwith "TODO"
