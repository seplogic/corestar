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

(** Flag for empty creating specs template *)
let specs_template_mode = ref false

(** Flag to print heaps on every node in the cfg *)
let dotty_print = ref false

let symb_debug_ref = ref false
let symb_debug() = !symb_debug_ref

let eclipse_ref = ref false
let eclipse_mode() = !eclipse_ref

let parse_debug_ref = ref false
let parse_debug() = !parse_debug_ref

let cfg_debug_ref = ref false
let cfg_debug() = !cfg_debug_ref

let smt_debug_ref = ref false
let smt_debug() = !smt_debug_ref

let abs_int_join_ref = ref false
let abs_int_join() = !abs_int_join_ref

let smt_run = ref true
let solver_path = ref ""
let smt_custom_commands = ref ""

let set_debug_char (c : char) : unit =
  match c with
  | 'p' -> parse_debug_ref := true
  | 's' -> symb_debug_ref := true
  | 'c' -> cfg_debug_ref := true
  | 'm' -> smt_debug_ref := true
  | _ -> ()

let abs_int_plugins = ref []
let set_abs_int_plugins (comma_sep_lis : string) : unit =
  abs_int_plugins := Str.split (Str.regexp ":") comma_sep_lis

let args_default = [
("-v", Arg.Unit (fun () -> incr verbosity), "increase verbosity");
("-d", Arg.String(String.iter set_debug_char), "set debug modes");
("-nosmt", Arg.Clear(smt_run),"Don't use the SMT solver");
("-p", Arg.Set_string(solver_path), "SMT solver path");
("-b", Arg.Set_string(smt_custom_commands), "Background predicate");
("-ai", Arg.String(set_abs_int_plugins), "Colon separated list of AI plugins filenames");
("-join", Arg.Set(abs_int_join_ref), "On abstraction join heaps over their numeric part");
]
