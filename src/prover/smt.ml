open Corestar_std
open Printf

module D = Debug
module Expr = Expression

type sort = Expr.sort
type symbol = string
type term = Expr.t
type var = Expr.var

exception Error of string

type check_sat_response = Sat | Unsat | Unknown

let smt_init () =
  let smt_path =
    if (!Config.solver_path <> "") then !Config.solver_path
    else System.getenv "JSTAR_SMT_PATH"
  in
  if smt_path = "" then failwith "SMT path is empty!"
  else
    try
      begin
        if Config.smt_debug() then printf "@[Initialising SMT@.";
        let args = System.getenv "JSTAR_SMT_ARGUMENTS" in
        let command = Filename.quote smt_path ^ " " ^ args in
        if D.log D.log_phase then Format.fprintf D.logf "@[execute <%s>@." command;
        let o, i, e = Unix.open_process_full command (Unix.environment()) in
        if Config.smt_debug() then printf "@[SMT running.@";
        output_string i "(set-option :print-success false)\n";
        flush i;
        (o, i, e)
      end
    with Unix.Unix_error (Unix.ENOENT, _, a) ->
      printf "@[@{<b>ERROR:@} Bad path for SMT solver: %s@." a;
      failwith "Cannot go on."

let smt_out, smt_in, smt_err = smt_init ()

let smt_command cmd =
  try
    if Config.smt_debug() then printf "@[%s@." cmd;
    Format.print_flush();
    output_string smt_in cmd;
    output_string smt_in "\n";
    flush smt_in;
  with End_of_file | Sys_error _ -> raise (Error "SMT error in command call")

let smt_listen () =
  let match_it = function
    | "sat" -> Sat
    | "unsat" -> Unsat
    | "unknown" -> Unknown
    | _ -> raise (Error "SMT result is unexpected")
  in
  Scanf.fscanf smt_out " %s " match_it

(* The code below assumes that vars and sorts are strings *)

let rec send_expr f =
  let ps = fprintf f "%s" in
  let app op = function
    | [] -> failwith (op ^ " function should have arguments (indsfisa)")
    | xs -> fprintf f "(%s%a)" op send_list xs in
  Expr.cases ps
    ( Expr.on_string_const (fprintf f "str-%s")
    & Expr.on_int_const ps
    & app )
and send_list f = List.iter (fprintf f " %a" send_expr)

let rec term_to_smt_term t =
  let if_var x = x in
  let if_app op xs =
    if xs = [] then failwith "An SMT function app needs an argument";
    let xs_s = List.fold_left (fun acc x -> sprintf "%s %s" acc
      (term_to_smt_term x)) "" xs in sprintf "( %s %s )" op xs_s
  in Expr.cases if_var if_app t

let define_fun sm vs st tm  = (* ( define-fun <symbol> ( <sorted_var>* ) <sort> <term> ) *)
  let sm_s = sm in
  let vs_s = List.fold_left (fun acc (v,s) -> sprintf "%s ( %s %s )" acc v s) "" vs in
  let st_s = st in
  let tm_s = term_to_smt_term tm in
  let x = sprintf "( define-fun %s ( %s ) %s %s )" sm_s vs_s st_s tm_s in
  smt_command x

let say tm = (* ( assert <term> ) *)
  let x = sprintf "( assert %s )" (term_to_smt_term tm) in
  smt_command x

let check_sat () =
  smt_command "( check-sat )";
  let x = smt_listen () in
  if Config.smt_debug() then (
    printf "@[listened '%s'@." ( match x with
      Unsat -> "Unsat"
    | Sat -> "Sat"
    | Unknown -> "Unknown" )); x

let push () = smt_command "(push)"
let pop () = smt_command "(pop)"
