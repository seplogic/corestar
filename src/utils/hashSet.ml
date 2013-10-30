open Corestar_std

type 'a t = ('a, unit) Hashtbl.t

let add h e = Hashtbl.replace h e ()

let remove h e = Hashtbl.remove h e

let create n = Hashtbl.create n

let singleton e =
  let h = create 1 in
  add h e; h

let of_list es =
  let h = create (2 * List.length es) in
  List.iter (add h) es; h

let mem = Hashtbl.mem

let find = Hashtbl.find

let iter f h = Hashtbl.iter (fun x _ -> f x) h

let fold f h z = Hashtbl.fold (fun x _ r -> f x r) h z

exception X

let for_all_gen iter p h =
  let f x = if not (p x) then raise X in
  try iter f h; true with X -> false

let for_all p h = for_all_gen iter p h

let exists p = not @@ for_all (not @@ p)

let elements h = fold ListH.cons h []

let choose_gen iter h =
  let r = ref None in
  try iter (fun x -> r := Some x; raise X) h; raise Not_found
  with X -> (match !r with Some x -> x | _ -> failwith "impossible")

let choose h = choose_gen iter h

let length h = Hashtbl.length h

let map f = of_list @@ List.map f @@ elements

module type HashedType = Hashtbl.HashedType

module type S = sig
  type elt
  type t
  val add : t -> elt -> unit
  val choose : t -> elt
  val create : int -> t
  val elements : t -> elt list
  val iter : (elt -> unit) -> t -> unit
  val fold : (elt -> 'a -> 'a) -> t -> 'a -> 'a
  val for_all : (elt -> bool) -> t -> bool
  val exists : (elt -> bool) -> t -> bool
  val length : t -> int
  val mem : t -> elt -> bool
  val find : t -> elt -> unit
  val remove : t -> elt -> unit
  val singleton : elt -> t
  val of_list : elt list -> t
  val map : (elt -> elt) -> t -> t
end

module Make (E : HashedType) = struct
  module H = Hashtbl.Make (E)
  type elt = E.t
  type t = unit H.t
  let add h e = H.replace h e ()
  let create = H.create
  let iter f = H.iter (fun x _ -> f x)
  let fold f = H.fold (fun x _ r -> f x r)
  let length = H.length
  let mem = H.mem
  let find = H.find
  let remove = H.remove
  let singleton e = let h = create 1 in add h e; h
  let of_list es =
    let h = create (2 * List.length es) in List.iter (add h) es; h

  (* Depend on [iter]/[fold]. *)
  let choose = choose_gen iter
  let elements h = fold ListH.cons h []
  let for_all = for_all_gen iter
  let exists p = not @@ for_all (not @@ p)

  let map f h = h |> elements |> List.map f |> of_list
end
