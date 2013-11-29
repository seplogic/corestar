(* TODO: This should be ported to Z3's OCAML API. *)

open Corestar_std
open Debug
open Printf
open Scanf

module Expr = Expression

type sort = Expr.sort  (* p, p1, p2, q, ... *)
type symbol = string  (* s, s1, s2, *)
type term = Expr.t  (* t, t1, t2, *)
type var = Expr.var  (* x, y, ... *)

type check_sat_response = Sat | Unsat | Unknown

(* TODO: The lhs is brittle: It must be whatever [Expression] uses internally. *)
let interpreted =
  [ "!=", "distinct"
  ; "*", "and"
  ; "==", "="
  ; "emp", "true"
  ; "fls", "false"
  ; "not", "not"
  ; "or", "or" ]
(* TODO: The name [identities] is bad. *)
let identities =
  [ "and", "true"
  ; "or", "false" ]

let uniq_id = ref 0
let str_map = StringHash.create 0
let sym_map = StringHash.create 0
let () = List.iter (uncurry (StringHash.add sym_map)) interpreted

let bad_id_re = Str.regexp "[^a-zA-Z0-9]+"

let sanitize pre map id =
  try StringHash.find map id
  with Not_found -> begin
    let clean = Str.global_replace bad_id_re "" in
    let r = sprintf "%s-%s-%d" pre (clean id) (incr uniq_id; !uniq_id) in
    StringHash.add map id r; r
  end

let sanitize_sym = sanitize "sym" sym_map
let sanitize_str = sanitize "str" str_map
let sanitize_int = sanitize "int" str_map (* TODO: handle integers properly *)

let z3_out, z3_in, z3_err =
  Unix.open_process_full "z3 -smt2 -in" (Unix.environment())

let z3_log =
  if log log_smt then open_out "smt.corestar.log" else stderr

let log_comment = fprintf z3_log "; %s\n"

let declared = ref [StringHash.create 0]

let declared_sort s =
  let rec loop = function
    | [] -> raise Not_found
    | h :: hs -> (try StringHash.find h s with Not_found -> loop hs) in
  loop !declared

let declared_push () =
  declared := StringHash.create 0 :: !declared

let declared_pop () =
  declared := List.tl !declared;
  assert (!declared <> [])

let is_predeclared =
  let s = List.map snd interpreted in
  let s = List.fold_right StringSet.add s StringSet.empty in
  flip StringSet.mem s

let is_declared s =
  is_predeclared s
  || (try ignore (declared_sort s); true with Not_found -> false)

(* Helpers to send strings to Z3. *) (* {{{ *)
(* NOTE: Many of these function resemble pretty-printers from [Corestar_std],
but there are some differences. For example, here we must use [Printf] rather
than [Format], because we don't want the latter to introduce spaces at its
whim. *)

(* NOTE: Helper functions should use [fprintf];
toplevel sending to z3 should use [sendK]. *)
let send0 f format = fprintf f format; if log log_smt then fprintf z3_log format
let send1 f format x = fprintf f format x; if log log_smt then fprintf z3_log format x
let send2 f format x y = fprintf f format x y; if log log_smt then fprintf z3_log format x y
let send3 f format x y z = fprintf f format x y z; if log log_smt then fprintf z3_log format x y z

let send_string f = fprintf f "%s"

let send_list pp f = List.iter (fprintf f " %a" pp)

let find_op op =
 try List.assoc op identities
 with Not_found -> op

let rec send_expr f =
  let ps = fprintf f "%s" in
  let app op = function
    | [] -> fprintf f "%s" (find_op op)
    | xs -> fprintf f "(%s%a)" op (send_list send_expr) xs in
  Expr.cases
    (ps @@ sanitize_sym)
    ( Expr.on_string_const (ps @@ sanitize_str)
    & Expr.on_int_const (ps @@ sanitize_int)
    & (app @@ sanitize_sym))

(* }}} *)

let declare s ((ps, q) as psq) =
  if not (is_predeclared s) then
  try
    let psq_old = declared_sort s in
    assert (psq = psq_old)
  with Not_found -> begin
    send1 z3_in "(declare-fun %s" s;
    send3 z3_in " (%a) %s)\n%!" (send_list send_string) ps q;
    StringHash.add (List.hd !declared) s psq
  end

let () = (* send prelude *)
  send0 z3_in "(declare-sort Ref)\n%!"

(* TODO: Replace by some proper implementation; should use [Expr.sort_of]. *)
let analyze_sorts =
  let rec repeat x = function [] -> [] | _ :: ts -> x :: repeat x ts in
  let dec ts c  = declare c (repeat "Ref" ts, "Ref") in
  let var = dec [] @@ sanitize_sym in
  let str = dec [] @@ sanitize_str in
  let int = dec [] @@ sanitize_int in
  let rec app op ts = dec ts (sanitize_sym op); List.iter visit ts
  and visit t = Expr.cases var
    ( Expr.on_string_const str
    & Expr.on_int_const int
    & app) t in
  visit

(* For debugging. *)
let read_error () =
  let b = Buffer.create 0 in
  let r () = fscanf z3_out "%c" (fun c -> Buffer.add_char b c; c) in
  let rec f = function
    | 0 -> Buffer.sub b 0 (Buffer.length b - 1)
    | n -> (match r () with
        | '(' -> f (n + 1) | ')' -> f (n - 1)
        | '\'' -> g n '\'' | '"' -> g n '"'
        | _ -> f n)
  and g n c = if r () = c then f n else g n c in
  f 1

let smt_listen () =
  send0 z3_in "%!";
  fscanf z3_out " %s" (function
    | "sat" -> Sat
    | "unsat" -> Unsat
    | "unknown" -> Unknown
    | "(error" -> failwith ("Z3 error: " ^ read_error ())
    | s -> failwith ("Z3 says: " ^ s))

let define_fun sm vs st tm  =
  let send_arg f (v, s) = fprintf f "(%s %s)" v s in
  send3 z3_in "(define-fun %s (%a)" sm (send_list send_arg) vs;
  send3 z3_in " %s %a)\n" st send_expr tm

let say e =
  analyze_sorts e;
  send2 z3_in "(assert %a)\n" send_expr e

let check_sat () =
  (* TODO: Handle (distinct ...) efficiently. *)
  let ss = StringHash.fold (fun _ -> ListH.cons) str_map [] in
  let ss = List.filter is_declared ss in
  if ss <> [] then
    send2 z3_in "(assert (distinct%a))\n" (send_list send_string) ss;
  send0 z3_in "(check-sat)\n%!";
  smt_listen ()

let push () =
  declared_push ();
  send0 z3_in "(push)\n%!"

let pop () =
  declared_pop ();
  send0 z3_in "(pop)\n%!"
