(********************************************************
   This file is part of coreStar
        src/utils/misc.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std

(* TODO(rgrig): Don't open these. *)
open Backtrack

let rec fold_pairs f acc = function
  | [] | [_] -> acc
  | x :: ((y :: _) as xs) -> fold_pairs f (f acc x y) xs

let iter_pairs f =
  let f () x = f x in fold_pairs f

let rec iter_pairs f = function
  | [] | [_] -> ()
  | x :: ((y :: _) as xs) -> f x y; iter_pairs f xs

let iter_all_pairs f xs =
  let g = function [] -> () | x :: xs -> List.iter (f x) xs in
  List.iter g (ListH.tails xs)

let map_lift_exists f l
    =
  List.fold_right
    (fun el rest->
      match f el, rest  with
	None,_ -> rest
   |	Some el,Some rest -> Some (el::rest)
   |  Some el, None -> Some [el]) l None

let map_lift_forall f l
    =
  List.fold_right
    (fun el rest->
      match f el, rest  with
     	  None,_ -> None
	    | _, None -> None
      |	Some el,Some rest -> Some (el::rest)) l (Some [])


type ('a,'b) sum =
    Inr of 'a
  | Inl of 'b

let map_sum f l
    =
  List.fold_right
    (fun el (restl,restr) ->
      match f el with
      | Inl l -> (l::restl,restr)
      | Inr r -> (restl,r::restr)) l ([],[])

(* operations with sorted lists, strictly increasing ones *) (* {{{ *)
let remove_duplicates cmp xs =
  let uniq x ys = if ys = [] || cmp x (List.hd ys) <> 0 then x :: ys else ys in
  List.fold_right uniq (List.sort cmp xs) []

let merge_lists xs ys =
  let rec f zs = function
    | [], ys | ys, [] -> List.rev_append ys zs
    | ((x :: xs) as xxs), ((y :: ys) as yys) ->
        let c = compare x y in
        if c < 0 then f (x :: zs) (xs, yys)
        else if c > 0 then f (y :: zs) (xxs, ys)
        else f (x :: zs) (xs, ys) in
  List.rev (f [] (xs, ys))

let insert_sorted x xs =
  let rec f ys = function
    | [] -> List.rev (x :: ys)
    | z :: zs as zzs ->
        let c = compare x z in
        if c < 0 then List.rev_append ys (x :: zzs)
        else if c > 0 then f (z :: ys) zs
        else xs in
  f [] xs

(* }}} *)
let rec map_and_find f = function
  | [] -> raise Not_found
  | x :: xs -> try f x with _ -> map_and_find f xs

let lift_pair f =
  fun (x,y) -> (f x, f y)

let lift_option f =
  fun x -> match x with
    Some x -> f x
  | None -> None

let rec add_index
    ( xs : 'a list )
    ( i : int ) : ('a * int) list =
  match xs with  | []     ->  []
                 | y::ys  ->  ( (y,i) :: (add_index ys (i+1)) )

let memo f =
  let cache = Hashtbl.create 101 in
  fun g x ->
    try Hashtbl.find cache x
    with Not_found ->
      let r = f g x in
      (Hashtbl.add cache x r; r)

let cross_product l1 l2 =
  let product l v2 = List.map (fun v1 -> (v1, v2)) l in
  l2 >>= product l1

let rec product = function
  | [] -> [[]]
  | xs :: xss -> List.map (fun (x,y)->x::y) (cross_product xs (product xss))

let tuples n xs = product (ListH.replicate n xs)

let fresh_int () =
  let n = ref (-1) in
  fun () -> incr n; assert (!n >= 0); !n (* checks for overflow *)

module type HASHTBL = sig
  type key
  type 'value t
  val create : int -> 'value t
  val add : 'value t -> key -> 'value -> unit
  val find : 'value t -> key -> 'value
end

let summarize_list create add find one plus key value xs =
  let h = create (List.length xs) in
  let entry x = match key x, value x with
    | None, _ | _, None -> ()
    | Some k, Some v ->
        (try add h k (plus v (find h k))
        with Not_found -> add h k (one v)) in
  List.iter entry xs;
  h

let hash_of_list one plus key value xs =
  summarize_list Hashtbl.create Hashtbl.add Hashtbl.find one plus key value xs

let shuffle xs = xs
  (* TODO. Note: It's a bit annoying that [Random] has one global state. *)

