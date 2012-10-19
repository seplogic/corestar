(********************************************************
   This file is part of coreStar
        src/symbfront/symbfront.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


val logic_file_name : string ref
val absrules_file_name : string ref
val arg_list : (string * Arg.spec * string) list
val main : unit -> unit
