(********************************************************
   This file is part of coreStar
        src/utils/backtrack.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std

exception No_match

let tryall f =
  let rec ta = function
    | [] -> raise No_match
    | x :: xs -> (try f x with No_match -> ta xs)
  in ta

let tryall2 y1 y2 f = tryall (fun x -> f x y1 y2)

let chain fs x cont =
  List.fold_right flip fs cont x

let using x cont f =
  f x cont
