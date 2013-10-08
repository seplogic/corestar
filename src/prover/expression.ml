open Corestar_std
open Format

type t_orig = Var of string | App of string * exp list
and exp = t_orig * int
  (* TODO: explain which are valid names; empty string is not *)

let hash = snd
let eq = (==)

module ExpBase = Hashtbl.Make (struct
  type t = exp
  let hash = hash
  let equal f1 f2 = match fst f1, fst f2 with
    | Var x1, Var x2 -> x1 = x2
    | App (op1, xs1), App (op2, xs2) ->
        op1 = op2
        && (try List.for_all2 eq xs1 xs2 with Invalid_argument _ -> false)
    | _ -> false
end)

let exp_base = ExpBase.create 0

let hash_orig =
  let eh = Hashtbl.hash "" in (* any string that is not a valid varname works *)
  let f acc x = 31 * acc + hash x in
  function
    | Var v -> 31 * (Hashtbl.hash v) + eh
    | App (op, xs) -> 31 * (List.fold_left f (Hashtbl.hash op) xs) + eh

let hash_cons f =
  try ExpBase.find exp_base f
  with Not_found -> ExpBase.add exp_base f f; f

let mk_app op xs =
  let e = App (op, xs) in
  hash_cons (e, hash_orig e)
let mk_var v =
  assert (not (v = "")); (* otherwise, hashes are messed up *)
  let e = Var v in
  hash_cons (e, hash_orig e)

let bk_app f = match fst f with
  | Var _ -> invalid_arg "bk_app"
  | App (op, xs) -> (op, xs)

let bk_var f = match fst f with
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

(* TODO: Memoize if profiling shows that this is slow. *)
let rec size e = match fst e with
  | Var _ -> 1
  | App (_, xs) -> List.fold_left (+) 1 (List.map size xs)

module ExprHashSet = HashSet.Make(
struct
  type t = exp
  let hash = hash
  let equal = eq 
end)

let vars x =
  let vs = ExprHashSet.create 0 in
  let rec f exp = match fst exp with
    | Var _ -> ExprHashSet.add vs exp
    | App (_, xs) -> List.iter f xs in
  let g exp a = match fst exp with 
    | Var v -> v::a
    | _ -> assert false in
  f x ; ExprHashSet.fold g vs [] 

let substitute xys =
  let f = ListH.lookup xys in
  let rec r exp = match fst exp with
    | Var v -> (try f v with Not_found -> exp)
    | App (op, xs) -> mk_app op (List.map r xs) in
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
  fun g -> match fst g with
    | Var v -> pp_string f v
    | App (op, xs) -> fprintf f "(%s%a)" op (pp_list pp_rec) xs

type t = exp
