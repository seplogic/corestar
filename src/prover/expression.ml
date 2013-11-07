open Corestar_std
open Format

type symbol = string (* u, v, ... *)
type var = symbol (* x, y, ... *)
type op = symbol (* g, h, ... *)
type sort = string (* t *)

type t_orig = Var of string | App of string * exp list
and exp = t_orig * int  (* e, f, ... *)
  (* TODO: explain which are valid names; empty string is not *)

let rec pp f =
  let pp_rec f e = fprintf f "@ %a" pp e in
  fun g -> match fst g with
    | Var v -> pp_string f v
    | App (op, xs) -> fprintf f "@[<2>(%s%a)@]" op (pp_list pp_rec) xs

let hash = snd
let equal = (==)

let sorts = ref StringSet.empty
let symbols = StringHash.create 0

let declare_sort t =
  assert (not (StringSet.mem t !sorts));
  sorts := StringSet.add t !sorts

let declare_symbol u t =
  assert (not (StringHash.mem symbols u));
  StringHash.add symbols u t

module ExpBase = Hashtbl.Make (struct
  type t = exp
  let hash = hash
  let equal f1 f2 = match fst f1, fst f2 with
    | Var x1, Var x2 -> x1 = x2
    | App (op1, xs1), App (op2, xs2) ->
        op1 = op2
        && (try List.for_all2 equal xs1 xs2 with Invalid_argument _ -> false)
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

let pvar_re = Str.regexp "[a-z$@]" (* TODO: $ and @ are too complicated. *)
let lvar_re = Str.regexp "_"
let tpat_re = Str.regexp "\\?"
let vpat_re = Str.regexp "_" (* TODO: lval/vpat confusion? *)

let is_pvar v = Str.string_match pvar_re v 0
let is_lvar v = Str.string_match lvar_re v 0
let is_tpat p = Str.string_match tpat_re p 0
let is_vpat p = Str.string_match vpat_re p 0

let iob b = if b then 1 else 0

(* TODO: sort checking *)
let mk_app op xs =
  let e = App (op, xs) in
  hash_cons (e, hash_orig e)
let mk_var v =
  assert begin
    let one_of xs = List.fold_left (+) 0 (List.map (iob @@ (|>) v) xs) = 1in
    one_of [is_pvar; is_lvar] || one_of [is_tpat; is_vpat]
  end;
  assert (not (v = "")); (* otherwise, hashes are messed up *)
  let e = Var v in
  hash_cons (e, hash_orig e)

let bk_app f = match fst f with
  | Var _ -> invalid_arg "bk_app"
  | App (op, xs) -> (op, xs)

let bk_var f = match fst f with
  | Var v -> v
  | App _ -> invalid_arg "bk_var"

let cases var app e = match fst e with
  | Var v -> var v
  | App (op, xs) -> app op xs

let symbol_of = cases (fun x -> x) (fun f _ -> f)

let sort_of = StringHash.find symbols @@ symbol_of

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

(* TODO: Memoize if profiling shows that this is slow. *)
let rec size e = match fst e with
  | Var _ -> 1
  | App (_, xs) -> List.fold_left (+) 1 (List.map size xs)

module ExprHashSet = HashSet.Make(
struct
  type t = exp
  let hash = hash
  let equal = equal
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

module ExprHashMap = Hashtbl.Make(
struct
  type t = exp
  let hash = hash
  let equal = equal
end)

let substitute xys =
  let m = ExprHashMap.create 0 in
  List.iter (fun (v, t) -> ExprHashMap.add m (mk_var v) t) xys;
  let f = ExprHashMap.find m in
  let rec r exp = match fst exp with
    | Var _ -> (try f exp with Not_found -> exp)
    | App (op, xs) -> mk_app op (List.map r xs) in
  r

let mk_0 op = mk_app op []
let mk_1 op a = mk_app op [a]
let mk_2 op a b = mk_app op [a; b]

(* NOTE: The main point of [on_*] functions is to avoid using strings in other
places in the codebase, because that is bug-prone. *)
type 'a automorphism = 'a -> 'a
type 'a app_eval = (op -> exp list -> 'a) automorphism
type 'a app_eval_n = (exp list -> 'a) -> 'a app_eval
type 'a app_eval_1 = (exp -> 'a) -> 'a app_eval
type 'a app_eval_2 = (exp -> exp -> 'a) -> 'a app_eval


let on_op op_ref f g op =
  if op = op_ref then f else g op

let on_1 op_ref f =
  let f = function
    | [e] -> f e
    | _ -> failwith ("INTERNAL: "^ op_ref ^ " should have arity 1" ) in
  on_op op_ref f

let on_2 op_ref f =
  let f = function
    | [e1; e2] -> f e1 e2
    | _ -> failwith ("INTERNAL: "^ op_ref ^ " should have arity 2" ) in
  on_op op_ref f

let on_const op_ref f =
  let f = function
    | [e] -> let s, xs = bk_app e in assert (xs = []); f s
    | _ -> failwith ("INTERNAL: "^ op_ref ^ " should have arity 1") in
  on_op op_ref f


let mk_star = mk_2 "*"
let mk_big_star = mk_app "*"
let on_star f = on_op "*" f
let mk_or = mk_2 "or"
let mk_big_or = mk_app "or"
let on_or f = on_op "or" f

let mk_not = mk_1 "not"
let on_not f = on_1 "not" f

let mk_eq = mk_2 "=="
let on_eq f = on_2 "==" f
let mk_neq = mk_2 "!="
let on_neq f = on_2 "!=" f

let mk_string_const s = mk_1 "<string>" (mk_0 s)
let on_string_const f = on_const "<string>" f
let mk_int_const s = mk_1 "<int>" (mk_0 s)
let on_int_const f = on_const "<int>" f

let is_interpreted _ = failwith "TODO"


let nil = mk_0 "nil"  (* TODO: Why do we have this? *)
let emp = mk_0 "emp"
let fls = mk_0 "fls"

type t = exp
