(* TODO: This should be ported to Z3's OCAML API. *)

open Corestar_std
open Printf
open Scanf

module D = Debug
module Expr = Expression

type sort = Expr.sort  (* p, p1, p2, q, ... *)
type symbol = string  (* s, s1, s2, *)
type term = Expr.t  (* t, t1, t2, *)
type var = Expr.var  (* x, y, ... *)

type check_sat_response = Sat | Unsat | Unknown


let z3_out, z3_in, z3_err =
  Unix.open_process_full "z3 -smt2 -in" (Unix.environment())

(* Helpers to send strings to Z3. *) (* {{{ *)
(* NOTE: Many of these function resemble pretty-printers from [Corestar_std],
but there are some differences. For example, here we must use [Printf] rather
than [Format], because we don't wan't the latter to introduce spaces at its
whim. *)

let send_string f = fprintf f "%s"

let send_list pp f = List.iter (fprintf f " %a%!" pp)

let rec send_expr f =
  let ps = fprintf f "%s%!" in
  let app op = function
    | [] -> failwith (op ^ " function should have arguments (indsfisa)")
    | xs -> fprintf f "(%s%a)" op (send_list send_expr) xs in
  Expr.cases ps
    ( Expr.on_string_const (fprintf f "str-%s") (* TODO: really uniqify *)
    & Expr.on_int_const ps
    & app )


(* }}} *)
let declared = ref [StringHash.create 0]
let string_constants = ref StringSet.empty

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

let declare s ((ps, q) as psq) =
  let check_old () =
    try
      let psq_old = declared_sort s in
      assert (psq = psq_old)
    with Not_found -> () in
  check_old ();
  fprintf z3_in "(declare-fun %s (%a) %s)\n%!" s (send_list send_string) ps q;
  StringHash.add (List.hd !declared) s psq

let () = (* send prelude *)
  fprintf z3_in "(declare-sort String)\n%!";
  fprintf z3_in "(declare-sort Ref)\n%!";
  declare "string-literal" (["String"], "Ref")

(* TODO: Replace by some proper implementation. *)
let analyze_sorts t =
  let rec repeat x = function [] -> [] | _ :: ts -> x :: repeat x ts in
  let var x = declare x ([], "Ref") in
  let app op ts = declare op (repeat "Ref" ts, "Ref") in
  failwith "CONTINUE HERE"

(* For debugging. *)
let read_error () =
  let b = Buffer.create 0 in
  let r () =
    fscanf z3_out "%c" (fun c -> Buffer.add_char b c; c) in
  let rec f = function
    | 0 -> Buffer.sub b 0 (Buffer.length b - 1)
    | n -> (match r () with
        | '(' -> f (n + 1) | ')' -> f (n - 1)
        | '\'' -> g n '\'' | '"' -> g n '"'
        | _ -> f n)
  and g n c = if r () = c then f n else g n c in
  f 1

let smt_listen () = fscanf z3_out " %s" (function
  | "sat" -> Sat
  | "unsat" -> Unsat
  | "unknown" -> Unknown
  | "(error" -> failwith ("Z3 error: " ^ read_error ())
  | s -> failwith ("Z3 says: " ^ s))

let define_fun sm vs st tm  =
  let send_args f = List.iter (fun (v, s) -> fprintf f "(%s %s)%!" v s) in
  fprintf z3_in "(define-fun %s (%a) %s %a)\n%!"
    sm send_args vs st send_expr tm

let say e =
  fprintf z3_in "(assert %a)\n%!" send_expr e

let check_sat () =
  fprintf z3_in "(check-sat)\n%!";
  smt_listen ()

let push () = fprintf z3_in "(push)\n%!"
let pop () = fprintf z3_in "(pop)\n%!"
