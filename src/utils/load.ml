(********************************************************
   This file is part of coreStar
        src/utils/load.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(* File to read a logic file and its imports. *)

open Corestar_std
open Debug
open Format

exception FileNotFound of string
exception CyclicDependency of string list

type 'a entry = ImportEntry of string | NormalEntry of 'a

type 'a tree = Leaf of 'a | Branch of 'a tree list

let rec flatten ys = function
  | [] -> List.rev ys
  | Leaf x :: xs -> flatten (x :: ys) xs
  | Branch zs :: xs -> flatten (flatten ys zs) xs

let load ?(path = []) parse fn =
  let rec load ps ds fn =
    let fn =
      (try System.find_file_from_dirs ds fn
      with Not_found -> raise (FileNotFound fn)) in
    if StringSet.mem fn ps then
      raise (CyclicDependency (StringSet.elements ps));
    let ps = StringSet.add fn ps in
    let ds = Filename.dirname fn :: ds in
    let load_entry = function
      | ImportEntry fn -> Branch (load ps ds fn)
      | NormalEntry x -> Leaf x in
    List.map load_entry (parse fn) in
  flatten [] (load StringSet.empty path fn)
