open Corestar_std
open Format

type symbol = string (* u, v, ... *)
type var = symbol (* x, y, ... *)
type op = symbol (* g, h, ... *)
type sort = string (* t *)

type t_orig = Var of string | App of string * expr list
and expr = t_orig * int  (* e, f, ... *)
  (* TODO: explain which are valid names; empty string is not *)

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
  type t = expr
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

let pvar_re = Str.regexp "[a-zA-Z$@]" (* TODO: I'd prefer just [a-z]. *)
let lvar_re = Str.regexp "_"
let tpat_re = Str.regexp "\\?"
let vpat_re = Str.regexp "_" (* TODO: lval/vpat confusion? *)
let pure_re = Str.regexp "!"

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

let match_ e var app = cases var app e

let recurse f op es = mk_app op (List.map f es)

let symbol_of = cases (fun x -> x) (fun f _ -> f)

let sort_of = StringHash.find symbols @@ symbol_of

let stem v =
  let i = iob (v.[0] = '_') in
  let len = (try String.index v '#' with Not_found -> String.length v) - i in
  String.sub v i len

let fresh_pvar =
  let counts = Hashtbl.create 0 in
  fun v ->
    let v = stem v in
    let c = (try Hashtbl.find counts v with Not_found -> 0) + 1 in
    Hashtbl.replace counts v c;
    Printf.sprintf "%s#%d" v c

(* Assumes the input is one of 'STEM', '_STEM', or '_STEM#ID'.
Produces '_STEM#ID' where ID is fresh for the given STEM. *)
let freshen v = Printf.sprintf "_%s" (fresh_pvar v)

(* TODO: Memoize if profiling shows that this is slow. *)
let rec size e = match fst e with
  | Var _ -> 1
  | App (_, xs) -> List.fold_left (+) 1 (List.map size xs)

module ExprHashSet = HashSet.Make(
struct
  type t = expr
  let hash = hash
  let equal = equal
end)

let vars x =
  let vs = ExprHashSet.create 0 in
  let rec f expr = match fst expr with
    | Var _ -> ExprHashSet.add vs expr
    | App (_, xs) -> List.iter f xs in
  let g expr a = match fst expr with
    | Var v -> v::a
    | _ -> assert false in
  f x ; ExprHashSet.fold g vs []

module ExprHashMap = Hashtbl.Make(
struct
  type t = expr
  let hash = hash
  let equal = equal
end)

let substitute_gen xys =
  let m = ExprHashMap.create 0 in
  List.iter (uncurry (ExprHashMap.add m)) xys;
  let rec r e =
    try ExprHashMap.find m e
    with Not_found ->
      cases (fun _ -> e) (fun op -> mk_app op @@ List.map r) e in
  r

let substitute =
  substitute_gen @@ List.map (fun (x, y) -> (mk_var x, y))

let mk_0 op = mk_app op []
let mk_1 op a = mk_app op [a]
let mk_2 op a b = mk_app op [a; b]

(* NOTE: The main point of [on_*] functions is to avoid using strings in other
places in the codebase, because that is bug-prone. *)
type 'a automorphism = 'a -> 'a
type 'a app_eval = (op -> expr list -> 'a) automorphism
type 'a app_eval_n = (expr list -> 'a) -> 'a app_eval
type 'a app_eval_0 = (unit -> 'a) -> 'a app_eval
type 'a app_eval_1 = (expr -> 'a) -> 'a app_eval
type 'a app_eval_2 = (expr -> expr -> 'a) -> 'a app_eval


let on_op op_ref f g op =
  if op = op_ref then f else g op

let on_0 op_ref f =
  let f = function
    | [] -> f ()
    | _ -> failwith ("INTERNAL: "^ op_ref ^ " should have arity 0" ) in
  on_op op_ref f

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

let on_tag op_ref f =
  let f = function
    | [e] -> let s, xs = bk_app e in assert (xs = []); f s
    | _ -> failwith ("INTERNAL: "^ op_ref ^ " should have arity 1") in
  on_op op_ref f

let emp = mk_0 "emp"
let on_emp f = on_0 "emp" f
let fls = mk_0 "fls"
let on_fls f = on_0 "fls" f

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
let on_string_const f = on_tag "<string>" f
let mk_int_const s = mk_1 "<int>" (mk_0 s)
let on_int_const f = on_tag "<int>" f

let rec is_pure e =
  let c0 x () = x in
  let terr _ = failwith "INTERNAL: should be formula, not term (sda8in)" in
  match_ e terr
  ( on_string_const terr
  & on_int_const terr
  & on_emp (c0 true)
  & on_fls (c0 true)
  & on_star (List.for_all is_pure)
  & on_or (List.for_all is_pure)
  & on_not (fun e -> assert (is_pure e); true)
  & on_eq (c2 true)
  & on_neq (c2 true)
  & fun op _ -> Str.string_match pure_re op 0)

(* NOTE: pretty printing is for debug, so don't rely on it for anything else *)

(* close to SMT-LIB's language *)
let rec pp_prefix f =
  let pp_rec f e = fprintf f "@ %a" pp_prefix e in
  fun g -> match fst g with
    | Var v -> pp_string f v
    | App (op, xs) -> fprintf f "@[<2>(%s%a)@]" op (pp_list pp_rec) xs

(* WARNING: close to input language, but somewhat mangled wrt data structure *)
let rec pp_infix f e =
  let pp_n op = fprintf f "@[(%a)@]" (pp_list_sep op pp_infix) in
  let pp_2 op e1 e2 = pp_n op [e1; e2] in
  let pp_1 op e = fprintf f "@[%s%a@]" op pp_infix e in
  let pp_0 op () = fprintf f "%s" op in
  match_ e
    (pp_string f)
    ( on_string_const (fprintf f "\"%s\"")
    & on_int_const (fprintf f "%s")
    & on_emp (pp_0 "emp")
    & on_fls (pp_0 "false")
    & on_star (pp_n " * ")
    & on_or (pp_n " || ")
    & on_not (pp_1 "!")
    & on_eq (pp_2 "=")
    & on_neq (pp_2 "!=")
    & fun op es -> fprintf f "@[%s(%a)@]" op (pp_list_sep ", " pp_infix) es)

(* NOTE: This function should be used *only* for debug. The [pp_prefix] version
is a verbatim dump of the data structure, and should be preferred. The
[pp_infix] version is a hack that you might want to use if you want to print
expressions, edit them, then read them back with corestar's parser. All this
while debugging, of course.*)
let pp = pp_infix

type t = expr
