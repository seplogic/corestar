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

let chain fs x cont =
  List.fold_right flip fs cont x

let wrap pre post f x cont =
  f (pre x) (cont @@ post)

let seq f g x cont =
  cont |> flip g |> f x
