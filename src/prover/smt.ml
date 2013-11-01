(* TODO: This should be ported to Z3's OCAML API. *)

open Corestar_std
open Printf
open Scanf

module D = Debug
module Expr = Expression

type sort = Expr.sort
type symbol = string
type term = Expr.t
type var = Expr.var

type check_sat_response = Sat | Unsat | Unknown

let z3_out, z3_in, z3_err =
  Unix.open_process_full "z3 -smt2 -in" (Unix.environment())

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

(* The code below assumes that vars and sorts are strings *)

let rec send_expr f =
  let ps = fprintf f "%s%!" in
  let app op = function
    | [] -> failwith (op ^ " function should have arguments (indsfisa)")
    | xs -> fprintf f "(%s%a)" op send_list xs in
  Expr.cases ps
    ( Expr.on_string_const (fprintf f "str-%s") (* TODO: really uniqify *)
    & Expr.on_int_const ps
    & app )
and send_list f = List.iter (fprintf f " %a%!" send_expr)

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
