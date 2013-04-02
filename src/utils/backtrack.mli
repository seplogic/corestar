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

val tryall : ('a -> 'b) -> 'a list -> 'b
  (** [tryall f xs] evaluates [f x] on each [x] in [xs] until [No_match]
  in not thrown. *)

val chain : ('a -> ('a -> 'b) -> 'b) list -> ('a -> ('a -> 'b) -> 'b)
  (** Like [andthen], but n-ary rather than binary. *)
