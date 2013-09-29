open Corestar_std
open Format

type t = Var of string | App of string * t list
  (* TODO: explain which are valid names; empty string is not *)

let mk_app op xs = App (op, xs)
let mk_var v = Var v

let pvar_re = Str.regexp "[a-z]"
let lvar_re = Str.regexp "_"

let is_pvar v = Str.string_match pvar_re v 0
let is_lvar v = Str.string_match lvar_re v 0

let eq = (=)  (* TODO: hash-consing *)

let hash e =
  let eh = Hashtbl.hash "" in
  let rec h acc = function
    | Var v -> 31 * (31 * acc + Hashtbl.hash v) + eh
    | App (v, xs) -> 31 * (List.fold_left h (31 * acc + Hashtbl.hash v) xs) + eh
  in h 0 e

let vars x =
  let rec f vs = function
    | Var v -> StringSet.add v vs
    | App (_, xs) -> List.fold_left f vs xs in
  StringSet.elements (f StringSet.empty x)

let substitute xys =
  let f = ListH.lookup xys in
  let rec r = function
    | Var v as e -> (try f v with Not_found -> e)
    | App (op, xs) -> App (op, List.map r xs) in
  r

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

let rec pp f =
  let pp_rec f e = fprintf f " %a" pp e in
  function
    | Var v -> pp_string f v
    | App (op, xs) -> fprintf f "(%s%a)" op (pp_list pp_rec) xs
