(********************************************************
   This file is part of coreStar
        src/utils/backtrack.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


exception No_match
val find_no_match_simp : ('a -> 'b) -> 'a list -> 'b
val tryall : ('a -> 'b -> 'c -> 'd) -> 'a list -> 'b -> 'c -> 'd
val andthen
  : ('a -> ('b * 'c list -> 'd) -> 'e) ->
    ('b -> ('f * 'c list -> 'g) -> 'd) ->
     'a -> ('f * 'c list -> 'g) -> 'e
val using : 'a -> 'b -> ('a -> 'b -> 'c) -> 'c
