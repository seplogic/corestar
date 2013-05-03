(********************************************************
   This file is part of coreStar
        src/utils/config.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(** In this file we can put all global flags *)

let verbosity = ref 0

let parse_debug_ref = ref false
let parse_debug() = !parse_debug_ref

let smt_debug_ref = ref false
let smt_debug () = !smt_debug_ref

let abs_int_join_ref = ref false
let abs_int_join() = !abs_int_join_ref

let smt_run = ref true
let solver_path = ref ""
let smt_custom_commands = ref ""

let set_debug_char (c : char) : unit =
  match c with
  | 'p' -> parse_debug_ref := true
  | 'm' -> smt_debug_ref := true
  | _ -> ()

let abs_int_plugins = ref []
let set_abs_int_plugins (comma_sep_lis : string) : unit =
  abs_int_plugins := Str.split (Str.regexp ":") comma_sep_lis

let check_arg_specs xs =
  let xs = List.map (fun (x, _, _) -> x) xs in
  if HashSet.length (HashSet.of_list xs) <> List.length xs then
    failwith "INTERNAL: Bad specs for [Arg.parse]."

let use_abduction_ref = ref true

let args_default =
  [ "-v", Arg.Unit (fun () -> incr verbosity), "increase verbosity"
  ; "-d", Arg.String (String.iter set_debug_char), "set debug modes [pm]"
  ; "-nosmt", Arg.Clear smt_run, "don't use the SMT solver"
  ; "-p", Arg.Set_string solver_path, "SMT solver (absolute path)"
  ; "-b", Arg.Set_string smt_custom_commands, "background predicate"
  ; "-ai", Arg.String set_abs_int_plugins, "AI plugins, separated by :"
  ; "-join", Arg.Set abs_int_join_ref, "numeric abstraction"
  ; "-noabd", Arg.Clear use_abduction_ref, "do not use abduction"  ]
let () = check_arg_specs args_default
