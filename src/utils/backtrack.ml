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

exception No_match

let rec find_no_match_simp f l =
  let rec fnm_inner f l =
  match l with 
    [] -> raise No_match
  | x::l -> try f x with No_match -> fnm_inner f l
  in fnm_inner f l 

let rec tryall f l t cont =
  let rec fnm_inner l =
  match l with 
    [] -> raise No_match
  | x::l -> try f x t cont with No_match -> fnm_inner l
  in fnm_inner l 

let andthen first second x cont =
  let mk_cont f cont (ts, eq1) = f ts (function y, eq2 -> cont (y, eq2 @ eq1)) in
  let cont = mk_cont second cont in
  let cont = mk_cont first cont in
  cont (x, [])

let using x cont f =
  f x cont 
