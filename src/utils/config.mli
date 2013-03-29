(********************************************************
   This file is part of coreStar
        src/utils/config.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

val verbosity : int ref
val specs_template_mode : bool ref
val dotty_print : bool ref
val symb_debug : unit -> bool
val eclipse_ref : bool ref
val parse_debug : unit -> bool
val smt_debug : unit -> bool
val abs_int_join : unit -> bool
val solver_path : string ref
val smt_run : bool ref
val smt_custom_commands : string ref
val args_default : (string * Arg.spec * string) list
val eclipse_mode : unit -> bool
val abs_int_plugins : string list ref
