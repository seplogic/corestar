(********************************************************
   This file is part of coreStar
        src/utils/load.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

exception FileNotFound of string

exception CyclicDependency of string list

type 'a entry = ImportEntry of string | NormalEntry of 'a

val file_name : string option ref (* for error reporting from the parser *)

val load : ?path:string list -> (string -> 'a entry list) -> string -> 'a list
