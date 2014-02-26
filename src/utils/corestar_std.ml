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

module Defaults = struct
  let compare = compare
  let equal = (=)
  let hash = Hashtbl.hash
end
module Str = struct type t = string include Defaults end
module Int = struct type t = int include Defaults end
module StringSet = Set.Make (Str)
module IntSet = Set.Make (Int)
module StringMap = Map.Make (Str)
module StringHash = Hashtbl.Make (Str)
module IntMap = Map.Make (Int)
module IntHash = Hashtbl.Make (Int)

let ( @@ ) f g x = f (g x)
let ( & ) f x = f x
let ( |> ) x f = f x
let ( >>= ) x f = x |> List.map f |> List.concat
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

let lift_option2 op o1 o2 = match o1, o2 with
  | Some x1, Some x2 -> Some (op x1 x2)
  | _ -> None

let map_option f l =
  let f' acc x = match f x with
    | None -> acc
    | Some y -> y :: acc in
  List.rev (List.fold_left f' [] l)

let from_option d = function
  | None -> d
  | Some x -> x

let from_some = function Some x -> x | None -> failwith "from_some: None"

let is_some = function Some _ -> true | _ -> false
let is_none = function None -> true | _ -> false

let flip f x y = f y x

let undefined _ = failwith "INTERNAL: undefined"

let c0 x = x
let c1 x _ = x
let c2 x _ _ = x

let id = c0
let const = c1

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

  let rec tails = function
    | []  -> [[]]
    | (_ :: xs) as t -> t :: tails xs

  let rec replicate n x = if n = 0 then [] else x :: replicate (n - 1) x

  let cons x xs = x :: xs

  let split3 xs =
    let f (x, y, z) (xs, ys, zs) = (x :: xs, y :: ys, z :: zs) in
    List.fold_right f xs ([], [], [])

  let group_by cmp =
    let rec f yss xs = match yss, xs with
      | yss, [] -> List.rev_map List.rev yss
      | [], x :: xs -> f [[x]] xs
      | (y :: _) as ys :: yss, x :: xs when cmp y x -> f ((x :: ys) :: yss) xs
      | yss, x :: xs -> f ([x] :: yss) xs in
    f []

  let span p =
    let rec f ys = function
      | x :: xs when p x -> f (x :: ys) xs
      | xs -> (List.rev ys, xs) in
    f []

  let lookup xys =
    let h = HashtblH.of_list xys in
    Hashtbl.find h

  let foldli f z xs =
    let g (acc, i) x = (f acc i x, i + 1) in
    fst (List.fold_left g (z, 0) xs)
  
  let foldri f xs z =
    let g x (i, acc) = (i - 1, f i x acc) in
    snd (List.fold_right g xs (List.length xs - 1, z))

  let mapi f xs =
    let g ys i x = f i x :: ys in
    foldli g [] xs

  let rev_mapi f xs =
    let g ys i x = f i x :: ys in
    foldli g [] xs

  let iteri f = ignore @@ mapi f

  let concatMap f xs = List.concat (List.map f xs)
end (* of ListH *)

type 'a pretty_printer = formatter -> 'a -> unit

let pp_int f x = fprintf f "%d" x

let pp_string f s = fprintf f "%s" s

let pp_list pp f = List.iter (pp f)

let pp_list_sep sep pp f = function
  | [] -> ()
  | x :: xs ->
      let pp_sep f x = fprintf f "@,%s%a" sep pp x in
      fprintf f "%a%a" pp x (pp_list pp_sep) xs

let string_of pp x =
  let b = Buffer.create 1 in
  let f = formatter_of_buffer b in
  pp f x;
  pp_print_flush f ();
  Buffer.contents b
