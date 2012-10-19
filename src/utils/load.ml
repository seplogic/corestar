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

open Debug
open Format

type 'a importoption =
    ImportEntry of string
  | NormalEntry of 'a


let import_flatten_extra_rules dirs filename extra_rules fileparser lexer =
  let rec import_flatten_inner dirs filename acc already_included =
    let rel_dir = (Filename.dirname filename) in
    let filename =
      try
	System.find_file_from_dirs dirs filename
      with Not_found  ->  (failwith ("Cannot find file " ^ filename)) in
    if List.mem filename already_included then
      (if log log_phase then
        fprintf logf "@[<4>File %s@ already included.@." filename;
      (acc, already_included))
    else (
    let already_included = filename::already_included in
    if log log_phase then
      fprintf logf "@[<4>Parsing logic in@ %s.@." filename;
    let file_entry_list = System.parse_file fileparser lexer filename "logic" in
    if log log_phase then
      fprintf logf "@[Parsed %s.@." filename;
    List.fold_left
      (fun (acc,already_included) entry ->
	match entry with
	  ImportEntry filen ->
	    import_flatten_inner (rel_dir::dirs) filen acc already_included
	| NormalEntry ent ->
	    (ent::acc, already_included)
      ) (acc,already_included) (extra_rules@file_entry_list)
     )
  in
  fst (import_flatten_inner dirs filename [] [])

let import_flatten dirs filename fileparser =
  import_flatten_extra_rules dirs filename [] fileparser
