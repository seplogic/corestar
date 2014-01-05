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


(** list of Z3 options
    The following parameters can be set:

    - proof  (Boolean)           Enable proof generation
    - debug_ref_count (Boolean)  Enable debug support for Z3_ast reference counting
    - trace  (Boolean)           Tracing support for VCC
    - trace_file_name (String)   Trace out file for VCC traces
    - timeout (unsigned)         default timeout (in milliseconds) used for solvers
    - well_sorted_check          type checker
    - auto_config                use heuristics to automatically select solver and configure it
    - model                      model generation for solvers, this parameter can be overwritten when creating a solver
    - model_validate             validate models produced by solvers
    - unsat_core                 unsat-core generation for solvers, this parameter can be overwritten when creating a solver
*)
let z3_options = ref [ "timeout", "5000" ]

let check_arg_specs xs =
  let xs = List.map (fun (x, _, _) -> x) xs in
  if HashSet.length (HashSet.of_list xs) <> List.length xs then
    failwith "INTERNAL: Bad specs for [Arg.parse]."

let use_abduction = ref true

let args_default =
  [ "-v", Arg.Unit (fun () -> incr verbosity), "increase verbosity"
  ; "-noabd", Arg.Clear use_abduction, "do not use abduction"  ]
let () = check_arg_specs args_default
