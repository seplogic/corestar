(********************************************************
   This file is part of coreStar
        src/utils/debug.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val safe : bool
val log_specs : int
val log_phase : int
val log_load : int
val log_prove : int
val log_exec : int
val log_logic : int
val log_mm : int
val log_cc : int
val log_smt : int
val log : int -> bool
val logf : Format.formatter
val add_formatter_tag : Format.formatter -> Format.tag * string * string -> unit
val prof_phase : string -> unit

(* TODO: [add_formatter_tag] should probably be in another module *)
