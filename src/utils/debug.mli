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
val log_smt : int
val log_stats : int
val log : int -> bool
val logf : Format.formatter
val add_formatter_tag : Format.formatter -> Format.tag * string * string -> unit
val prof_phase : string -> unit
val prof_start : string -> unit
val prof_stop : string -> unit
val prof_print_stats : unit -> unit
(*** NOTE: the functions below can alter the behaviour of the profiled
     functions because they use Hashtbl whose state is global *)
val prof_fun1 : string -> ('x1 -> 'result) -> ('x1 -> 'result)
val prof_fun2 : string -> ('x1 -> 'x2 -> 'result) -> ('x1 -> 'x2 -> 'result)
val prof_fun3 : string -> ('x1 -> 'x2 -> 'x3 -> 'result) -> ('x1 -> 'x2 -> 'x3 -> 'result)
val prof_fun4 : string -> ('x1 -> 'x2 -> 'x3 -> 'x4 -> 'result) -> ('x1 -> 'x2 -> 'x3 -> 'x4 -> 'result)

(* TODO: [add_formatter_tag] should probably be in another module *)
