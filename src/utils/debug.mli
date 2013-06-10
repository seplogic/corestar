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
val log : int -> bool
val logf : Format.formatter
val debug : bool
val buffer_dump : Buffer.t
val proof_dump : Format.formatter ref
val unsupported : unit -> 'a
val unsupported_s : string -> 'a
val pp_list : ('a -> 'b -> unit) -> 'a -> 'b list -> unit
val string_of : (Format.formatter -> 'a -> 'b) -> 'a -> string
val list_format :
  string ->
  (Format.formatter -> 'a -> unit) -> Format.formatter -> 'a list -> unit
val toString : (Format.formatter -> 'a -> unit) -> 'a -> string
