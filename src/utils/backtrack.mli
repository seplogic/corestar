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

(** Clients of this module should throw this exception when a dead-end is
reached.  However, instead of catching the exception, they should just use
the combinators below. *)
exception No_match

val tryall : ('a -> 'b) -> 'a list -> 'b
  (** [tryall f xs] evaluates [f x] on each [x] in [xs] until [No_match]
  in not thrown. This is a disjunctive combinator. *)

val chain : ('a -> ('a -> 'b) -> 'b) list -> ('a -> ('a -> 'b) -> 'b)
  (** [chain [f1; ...; fn] x cont] evaluates
  to [f1 x (fun x -> f2 x (fun x -> f3 x (... (fun x -> fn x cont))))].
  This is a sequencing combinator. *)

val wrap
  : ('a -> 'b) -> ('c -> 'd)
    -> ('b -> ('c -> 'e) -> 'e)
    -> ('a -> ('d -> 'e) -> 'e)
  (** Adds [wrap pre post f] does the same as [f], but with preprocessing [pre]
  and postprocessing [post].  The postprocessing is done after whatever [f]
  does, but before the continuation of is called. *)

val seq
  : ('a -> ('b -> 'd) -> 'd)
    -> ('b -> ('c -> 'd) -> 'd)
    -> ('a -> ('c -> 'd) -> 'd)
  (** A binary version of [chain] with more flexible types: But, the length of
  the list of functions to apply must by known to the compiler, so it can't be
  an actual OCaml list. [seq f g] takes a function [f] that transforms ['a] into
  ['b] and then calls a continuation, a function [g] that transforms ['b] into
  ['c] and then calls a continuation, and returns a function that transforms
  ['a] into ['c] and then calls a continuation. NOTE: [chain] is the case
  ['a='b='c]. *)

val repeat : ('a -> 'a) -> 'a -> 'a
  (** Iterate until [No_match] is thrown, then return the value that cause the exception.
   Thus [repeat f] will not throw No_match.
   Warning: [repeat f] will loop forever if [f] never throws No_match. *)

val lexico : ('a -> 'a) list -> 'a -> 'a
  (** A list version of [repeat]: [lexico [f1; ...; fn] x cont] evaluates
  to [((...((f1*;f2)*; f3)*;...)*; fn)*]. *)


val early_exit_fold :
  ('a -> bool) ->
  ('a -> 'b -> 'a) -> ('b -> bool) -> ('b -> 'b) -> 'a -> 'b -> 'a
  (** Generalized early exit fold. *)

val early_exit_fold_list :
  ('a -> bool) -> ('a -> 'b -> 'a) -> 'a -> 'b list -> 'a

val min_penalty : int
val max_penalty : int

val choose :
  ('a -> 'b * int) -> ('a -> bool) ->
  ('a -> 'a) -> 'b * int -> 'a -> 'b * int
val choose_list :
  ('a -> 'b * int) -> 'b * int -> 'a list -> 'b * int
val combine :
  ('a -> 'b list * int) -> ('a -> bool) ->
  ('a -> 'a) -> 'b list * int -> 'a -> 'b list * int
val combine_list :
  ('a -> 'b list * int) -> 'b list * int -> 'a list -> 'b list * int
