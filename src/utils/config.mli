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

val args_default : (Arg.key * Arg.spec * Arg.doc) list
val check_arg_specs : (Arg.key * Arg.spec * Arg.doc) list -> unit
val use_abduction : bool ref
val verbosity : int ref
val z3_options : ((string * string) list) ref
