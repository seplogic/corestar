open Corestar_std
open Format

type t = Var of string | App of string * t list
  (* TODO: explain which are valid names; empty string is not *)

let mk_app op xs = App (op, xs)
let mk_var v =
  assert (not (v = "")); (* otherwise, hashes are messed up *)
  Var v

let bk_app = function
  | Var _ -> invalid_arg "bk_app"
  | App (op, xs) -> (op, xs)

let bk_var = function
  | Var v -> v
  | App _ -> invalid_arg "bk_var"

(* Assumes the input is one of 'STEM', '_STEM', or '_STEM#ID'.
Produces '_STEM#ID' where ID is fresh for the given STEM. *)
let freshen =
  let counts = Hashtbl.create 0 in
  fun v ->
    let i = (if v.[0] = '_' then 1 else 0) in
    let len = (try String.index v '#' with Not_found -> String.length v) - i in
    let v = String.sub v i len in
    let c = (try Hashtbl.find counts v with Not_found -> 0) + 1 in
    Hashtbl.replace counts v c;
    Printf.sprintf "_%s#%d" v c

let pvar_re = Str.regexp "[a-z]"
let lvar_re = Str.regexp "_"
let tpat_re = Str.regexp "\\?"
let vpat_re = Str.regexp "_" (* TODO: lval/vpat confusion? *)

let is_pvar v = Str.string_match pvar_re v 0
let is_lvar v = Str.string_match lvar_re v 0
let is_tpat p = Str.string_match tpat_re p 0
let is_vpat p = Str.string_match vpat_re p 0

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
let mk_neq = mk_2 "!="

(* TODO: don't do this! Instead, have some general mechanism for types. *)
let mk_string_const s = mk_1 "<string>" (mk_0 s)
let mk_int_const s = mk_1 "<int>" (mk_0 s)

let is_interpreted _ = failwith "TODO"


let nil = mk_0 "nil" 
let emp = mk_0 "emp"
let fls = mk_0 "fls"

let rec pp f =
  let pp_rec f e = fprintf f " %a" pp e in
  function
    | Var v -> pp_string f v
    | App (op, xs) -> fprintf f "(%s%a)" op (pp_list pp_rec) xs
