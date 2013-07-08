(********************************************************
   This file is part of coreStar
        src/utils/multiset.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std

(* Search and remove structure *)
(* Multiset that allows for iteration through the elements *)

module type S =
  sig
    type t
    type multiset
    val is_empty : multiset -> bool
    val has_more : multiset -> bool
    val next  : multiset -> multiset
    val peek : multiset -> t
    val remove : multiset -> t * multiset
    val restart : multiset -> multiset
    val iter : (t -> unit) -> multiset -> unit
    val fold : ('a -> t -> 'a) -> 'a -> multiset -> 'a
    val from_list : t list -> multiset
    val to_list : multiset -> t list
    val union : multiset -> multiset -> multiset
    val empty : multiset
    val intersect : multiset -> multiset -> (multiset * multiset * multiset)
    val back : multiset -> int -> multiset
  end

module Make (A : Set.OrderedType) : S with type t = A.t =
  struct
    type t = A.t
    type multiset = A.t list * A.t list

(* TODO(rgrig): I don't understand the following comment.
 * Invariant all inner list must be non-empty
   That is, forall splittings
   forall xs,ys. t != xs @ [] :: ys
*)

    exception Empty

    let is_empty (xs, ys) =
      xs = [] && ys = []

    let has_more (xs, ys) =
      xs <> []

    let next (xs, ys) = match xs with
      | [] -> raise Empty
      | x :: xs  -> (xs, x :: ys)

    let rec back ((xs, ys) as zs) = function
      | 0 -> zs
      | n ->
          begin match ys with
            | [] -> raise Empty
            | y :: ys -> back (y :: xs, ys) (n - 1)
          end

    let peek = function
      | (x :: _, _) -> x
      | _ -> raise Empty

    let remove = function
      | (x :: xs, ys) -> (x, (xs, ys))
      | _ -> raise Empty

    let from_list xs =
      (List.sort compare xs, [])

    let to_list (xs, ys) =
      List.rev_append ys xs

    let restart zs =
      (to_list zs, [])

    let union a b =
      (List.merge compare (to_list a) (to_list b), [])

    let empty =
      ([], [])

    let iter f (xs, ys) =
      List.iter f (List.rev ys);
      List.iter f xs

    let fold f z (xs, ys) =
      List.fold_left f (List.fold_right (flip f) ys z) xs

    let intersect set1 set2 =
      if is_empty set1 then
        empty,empty,set2
      else if is_empty set2 then
        empty,set1,empty
      else
        let set1 = restart set1 in
        let set2 = restart set2 in
        let rec f set1 set2 res =
          if has_more set1 && has_more set2 then
            let x1,nset1 = remove set1 in
            let x2,nset2 = remove set2 in
            if compare x1 x2 = 0 then
              f nset1 nset2 (x1::res)
            else if compare x1 x2 < 0 then
              f (next set1) set2 res
            else
              f set1 (next set2) res
          else
            (List.rev res,[]), restart set1, restart set2
        in
        f set1 set2 []

  end
