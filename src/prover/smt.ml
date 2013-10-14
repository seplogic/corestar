type sort = Expression.sort
type symbol = string
type term = Expression.t
type var = Expression.var

exception Error of string
type check_sat_response = Sat | Unsat | Unknown

let define_fun _ = failwith "TODO: Smt.define_fun"
let push _ = failwith "TODO: Smt.push"
let pop _ = failwith "TODO: Smt.pop"
let say _ = failwith "TODO: Smt.say"
let check_sat _ = failwith "TODO: Smt.check_sat"
