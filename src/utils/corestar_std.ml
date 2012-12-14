(********************************************************
   This file is part of coreStar
        src/utils/corestar_std.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Format

module Int = struct type t = int let compare = compare end
module StringSet = Set.Make (String)
module IntSet = Set.Make (Int)
module StringMap = Map.Make (String)
module IntMap = Set.Make (Int)

let ( @@ ) f g x = f (g x)
let ( & ) f x = f x
let ( |> ) x f = f x
let ( =:: ) xs x = xs := x :: !xs
let ( !* ) = Lazy.force

let curry f a b = f (a, b)
let uncurry f (a, b) = f a b

let option n f = function
  | None -> n
  | Some x -> f x

let option_map f = function
  | None -> None
  | Some x -> Some (f x)

let map_option f l =
  let f' acc x = match f x with
    | None -> acc
    | Some y -> y :: acc in
  List.rev (List.fold_left f' [] l)

let from_option d = function
  | None -> d
  | Some x -> x

let is_some = function Some _ -> true | _ -> false
let is_none = function None -> true | _ -> false

let flip f x y = f y x

module CharH = struct
  let is_space =
    let spaces = " \t\n\r\x0b\x0c" in
    fun c -> String.contains spaces c
end

module StringH = struct
  let trim s =
    let n = String.length s in
    let i, j = ref 0, ref (n - 1) in
    while !i < n && CharH.is_space s.[!i] do incr i done;
    if !i = n then ""
    else begin
      while CharH.is_space s.[!j] do decr j done;
      String.sub s !i (!j - !i + 1)
    end

  let starts_with prefix s =
    let n = String.length prefix in
    if n > String.length s
    then false
    else String.sub s 0 n = prefix

  let ends_with suffix s =
    let m = String.length s in
    let n = String.length suffix in
    if n > m
    then false
    else String.sub s (m - n) n = suffix
end

module MapHelper = functor (M : Map.S) -> struct
  let filter (p : M.key -> 'a -> bool) (map : 'a M.t) : 'a M.t =
    M.fold (fun k v a -> if p k v then M.add k v a else a) map M.empty
end

module HashtblH = struct
  let of_list l =
    let h = Hashtbl.create (2 * List.length l + 1) in
    List.iter (uncurry (Hashtbl.replace h)) l; h
end

module ListH = struct
  let init n f =
    let rec loop acc = function
      | 0 -> acc
      | n -> loop (f (n - 1) :: acc) (n - 1) in
    loop [] n
end

let cons x xs = x :: xs

let pp_string f s = fprintf f "%s" s

let pp_list pp f = List.iter (pp f)

let pp_list_sep sep pp f = function
  | [] -> ()
  | x :: xs ->
      let pp f x = fprintf f "%s%a" sep pp x in
      fprintf f "%a@,%a" pp x (pp_list pp) xs
