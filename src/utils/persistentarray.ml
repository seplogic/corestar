(********************************************************
   This file is part of coreStar
        src/utils/persistentarray.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(*   This file contains an implementation of Persistent Array following:
     A Persistent Union-Find Data Structure
     Sylvain Conchon        Jean-Christophe Filliatre
     Workshop on ML'07

   However, we have extended it to enable the array to be grown dynamically.

*)

(* grow makes all arrays grow, not just current one*)
module type S = sig
  type elt
  type t
  val set : t -> int -> elt -> t
  val reset : t -> int -> t
  val get : t -> int -> elt
  val create : unit -> t
  val size : t -> int
  val grow : t -> int -> t
  val foldi : (int -> elt -> 'a -> 'a) -> t -> 'a -> 'a
  val find_indices : (elt -> bool) -> t -> int list
  (* After calling [unsafe_create a], don't dare to touch [a] again. *)
  val unsafe_create : elt array -> t
end

module type CREATOR = sig
  type elt
  val create : int -> elt
end

module Make (Creator : CREATOR) : S with type elt = Creator.elt
= struct
    type elt = Creator.elt

    type t = data ref * int
    and data =
        RealArray of elt array
      | Diff of int * elt * t

    (* Make array currently being accessed top *)
    let rec reroot (a,ir') =
      match !a with
      | RealArray _ -> ()
      | Diff(i,x,(b,ir)) ->
          reroot (b,ir);
          match !b with
            Diff(_,_,_) ->
            (* reroot will make top thing the RealArray so not
               possible for it to be a Diff. *)
              assert false
          | RealArray c ->
              let oldi = Array.get c i in
              Array.set c i x;
              a := RealArray c;
              b := Diff (i, oldi, (a,ir'))



    let create () = (ref (RealArray (Array.init 2 Creator.create)), 0)

    let unsafe_create a = (ref (RealArray a), Array.length a)

    let rec get (a,ir) i =
      assert (0 <= i && i < ir);
      reroot (a,ir);
      match !a with
        RealArray a -> Array.get a i
      | Diff _ -> assert false

    let rec set (a,ir) i x =
      assert (0 <= i && i < ir);
      reroot (a,ir);
      match !a with
        RealArray a' as n ->
          let old = Array.get a' i in
          if old <> x then begin
            Array.set a' i x;
            let na = ref n,ir in
            a := Diff(i,old,na);
            na
          end else
            (a,ir)
      | _ -> ref (Diff (i,x,(a,ir))), ir

    let reset a i = set a i (Creator.create i)

    (* Helper functions for accessing the underlying array to allow it
    to be resized. *)
    let rec real_array (a,ir) =
      match !a with
        RealArray _ -> a
      | Diff (i,x,a) -> real_array a

    let real_size (a,ir) =
      let ra = real_array (a,ir) in
      match !ra with
        RealArray a -> Array.length a
      | Diff(_,_,_) -> assert false

    let size (a,ir) = ir

    (* Make underlying array twice as large *)
    let double (a,ir) =
      let ra = real_array (a,ir) in
      match !ra with
        RealArray a ->
          let n = Array.length a in
          let f i = if i < n then a.(i) else Creator.create i in
          ra := RealArray (Array.init (n*2) f)
      | Diff(_,_,_) -> assert false

    (* Extend array, possibly growing underlying array if necessary. *)
    let grow ((a, ir) as t) n =
      while ir + n > real_size t do double t done;
      (a, ir + n)

    let foldi f xs z =
      let n = size xs in
      let rec go acc i =
        if i = n
        then acc
        else go (f i (get xs i) acc) (succ i) in
      go z 0

    let find_indices p xs =
      let f i x is = if p x then i :: is else is in
      List.rev (foldi f xs [])
  end

