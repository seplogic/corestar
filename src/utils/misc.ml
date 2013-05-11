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

open Backtrack

let rec iter_pairs f = function
  | [] | [_] -> ()
  | x :: ((y :: _) as xs) -> f x y; iter_pairs f xs

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


let remove_duplicates c l =
  let l = List.sort c l in
  snd (
  List.fold_left
    (fun (complast,list) next  ->
      if complast next = 0 then (complast,list) else (c next, next::list)
	) ((fun _ -> -1),[]) l
    )


(* TODO(rgrig): Isn't intcmp x y = compare y x? *)
let intcmp a b =
  if a<b then -1 else if a=b then 0 else 1

(* TODO(rgrig): Isn't intcmp2 x y = compare y x? *)
let intcmp2 (x1,x2) (y1,y2) =
  let v = intcmp x1 y1 in
  if v = 0 then intcmp x2 y2
  else v

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

let memo2 f =
  let cache = Hashtbl.create 101 in
  fun x y ->
    try Hashtbl.find cache (x, y)
    with Not_found ->
      let r = f x y in
      (Hashtbl.add cache (x, y) r; r)

let cross_product l1 l2 =
  let product l v2 = List.map (fun v1 -> (v1, v2)) l in
  List.concat (List.map (product l1) l2)

let fresh_int () =
  let n = ref (-1) in
  fun () -> incr n; assert (!n >= 0); !n (* checks for overflow *)

let hash_of_list one plus key value xs =
  let h = Hashtbl.create (List.length xs) in
  let entry x = match key x, value x with
    | None, _ | _, None -> ()
    | Some k, Some v ->
        (try Hashtbl.add h k (plus v (Hashtbl.find h k))
        with Not_found -> Hashtbl.add h k (one v)) in
  List.iter entry xs;
  h
