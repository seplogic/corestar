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

val min_penalty : int
val max_penalty : int

val choose :
  ('a -> 'b * int) -> ('a -> bool) ->
  ('a -> 'a) -> 'b * int -> 'a -> 'b * int
  (* [choose f end next z start] is like [choose_list], but applied on a list
  [xs] that is computed implicitly as follows: [start], [next start],
  [next (next start)], ..., up to (and not including) the first [x] for which
  [end x] evaluates to [true]. *)

val choose_list :
  ('a -> 'b * int) -> 'b * int -> 'a list -> 'b * int
  (* [choose_list f z xs] applies [f] to the elements of [xs] in turn.  The
  results must be pairs (value, score).  If a score [<=min_penalty] is returned,
  then that pair is returned without evaluating [f] on the rest of [xs].
  Otherwise, the first pair (value, score) with the smallest score is returned.
  In case [xs] is empty, [z] is returned. *)

val combine_list :
  ('a -> 'b list * int) -> 'b list * int -> 'a list -> 'b list * int
  (* [combine_list f ([], 0) xs] is similar to
      let yss, ps = List.split (List.map f xs) in (List.concat yss, sum ps)
  except that the mapping stops early if the sum of penalties exceeds
  [max_penalty]. *)
