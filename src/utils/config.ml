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

let check_arg_specs xs =
  let xs = List.map (fun (x, _, _) -> x) xs in
  if HashSet.length (HashSet.of_list xs) <> List.length xs then
    failwith "INTERNAL: Bad specs for [Arg.parse]."

let use_abduction = ref true

let args_default =
  [ "-v", Arg.Unit (fun () -> incr verbosity), "increase verbosity"
  ; "-noabd", Arg.Clear use_abduction, "do not use abduction"  ]
let () = check_arg_specs args_default
