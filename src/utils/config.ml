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

let solver_path = ref "z3"
let smt_custom_commands = ref ""

let set_debug_char (c : char) : unit =
  match c with
  | 'p' -> parse_debug_ref := true
  | 'm' -> smt_debug_ref := true
  | _ -> ()

let check_arg_specs xs =
  let xs = List.map (fun (x, _, _) -> x) xs in
  if HashSet.length (HashSet.of_list xs) <> List.length xs then
    failwith "INTERNAL: Bad specs for [Arg.parse]."

let use_abduction = ref true

let args_default =
  [ "-v", Arg.Unit (fun () -> incr verbosity), "increase verbosity"
  ; "-d", Arg.String (String.iter set_debug_char), "set debug modes [pm]"
  ; "-p", Arg.Set_string solver_path, "SMT solver (absolute path)"
  ; "-b", Arg.Set_string smt_custom_commands, "background predicate"
  ; "-noabd", Arg.Clear use_abduction, "do not use abduction"  ]
let () = check_arg_specs args_default
