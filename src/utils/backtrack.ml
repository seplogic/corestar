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

let rec repeat f x =
  try
    let y = f x in
    repeat f y
  with No_match -> x

let id x = x

let lexico fs =
  let add acc f = repeat (f @@ acc) in
  List.fold_left add id fs


(* Early exit folding of structures *)
let rec early_exit_fold exitable plus leaf next f acc c =
  if leaf c then acc else
  let new_acc = plus acc (f c) in
  if exitable new_acc then new_acc
  else early_exit_fold exitable plus leaf next f new_acc (next c)

let early_exit_fold_list exitable plus f acc l =
  let f_head = f @@ List.hd in
  early_exit_fold exitable plus ((=) []) List.tl f_head acc l


let min_penalty = 0
let max_penalty = 100

let exitable_choice (_, penalty) = penalty <= min_penalty

let plus_choice (best, best_penalty) (candidate, penalty) =
  if (penalty < best_penalty) then (candidate, penalty)
  else (best, best_penalty)

let choose f = early_exit_fold exitable_choice plus_choice f

let choose_list f = early_exit_fold_list exitable_choice plus_choice f

let exitable_combination (_, penalty) = penalty > max_penalty
    
let plus_combination (best_proof, best_penalty) (proof, penalty) =
  (best_proof @ proof, best_penalty + penalty)

let combine f = early_exit_fold exitable_combination plus_combination f

let combine_list f = early_exit_fold_list exitable_combination plus_combination f

