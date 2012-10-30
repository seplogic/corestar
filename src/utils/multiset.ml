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
    val lift_list : t list -> multiset
    val union : multiset -> multiset -> multiset
    val empty : multiset
    val intersect : multiset -> multiset -> (multiset * multiset * multiset)
    val back : multiset -> int -> multiset
    val map_to_list : multiset -> (t -> 'b) -> 'b list
    val fold_to_list : multiset -> (t -> 'a -> 'a) -> 'a -> 'a
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

    let rec revapp xs ys =
      match xs with
	[] -> ys
      | x::xs -> revapp xs (x::ys)

    let is_empty (x,y) : bool =
      match x,y with
	[],[] -> true
      | _,_ -> false

    let has_more ((x,y) : multiset) : bool =
      match x with
	[] -> false
      | _ -> true

    let next ((x,y) : multiset) : multiset=
      match x with
	[] -> raise Empty
      | (x::xs)  -> (xs,x::y)

    let rec back ((xs,ys) : multiset) (n : int) : multiset=
      match n with
	0 -> (xs,ys)
      | n ->
	  begin
	    match ys with
	      [] -> raise Empty
	    | (y::ys)  -> back (y::xs,ys) (n-1)
	  end

    let peek ((x,y) : multiset) : A.t =
      match x with
      [] -> raise Empty
      | (x::xs) -> x

    let remove ((x,y) : multiset) : A.t * multiset=
      match x with
	[] -> raise Empty
      | (x::xs) -> x,(xs,y)

    let lift_list (xs : A.t list)  : multiset =
      List.sort compare xs, []

    let restart (x,y) : multiset =
      revapp y x, []

    let union a b =
      let a = restart a in
      let b = restart b in
      match a, b with
	(a,[]), (b,[]) -> List.merge compare a b, []
      | _ -> assert false

    let empty =
      [],[]

    let iter f (x, y) =
      List.iter f (List.rev y);
      List.iter f x

    let fold f s (x, y) =
      let f' a b = f b a in
      List.fold_left f (List.fold_right f' y s) x

    let map_to_list a f =
      let a = restart a in
      let rec inner a rs =
      if has_more a then
        let x,a = remove a in
        inner a ((f x)::rs)
      else
        rs
      in inner a []

    let fold_to_list a f b =
      let a = restart a in
      let rec inner a b =
	      if has_more a then
	        let x,a = remove a in
          let r = f x b in
	        inner a r
	      else
	        b
      in inner a b

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
