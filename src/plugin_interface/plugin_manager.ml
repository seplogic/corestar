(********************************************************
   This file is part of coreStar
        src/plugins/plugin_manager.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std

open Plugin


(* Loads plugin using (nat) dynlink *)
let load_plugin (filename : string) =
  try Dynlink.loadfile (Dynlink.adapt_filename filename)
  with Dynlink.Error e -> failwith (Dynlink.error_message e)


(* Runs abstract_val from abstract interpretation plugins on a given pform *)
let abstract_val (pheap : Psyntax.pform) : Psyntax.pform =
  List.fold_left (fun pform abs_int -> 
    match (!abs_int).abstract_val with
    | None -> pform
    | Some abstract_val -> !abstract_val pform) 
    pheap !Registry.abs_int_registry

(* Runs join from abstract interpretation plugins on given pforms *)
let join (pheap1 : Psyntax.pform) (pheap2 : Psyntax.pform) : Psyntax.pform list =
  List.map (fun join -> !join pheap1 pheap2)
    (map_option (fun abs_int -> (!abs_int).join) !Registry.abs_int_registry)

(* Runs meet from abstract interpretation plugins on given pforms *)
let meet (pheap1 : Psyntax.pform) (pheap2 : Psyntax.pform) : Psyntax.pform list =
  List.map (fun meet -> !meet pheap1 pheap2)
    (map_option (fun abs_int -> (!abs_int).meet) !Registry.abs_int_registry)

(* Runs widening from abstract interpretation plugins on given pforms *)
let widening (pheap1 : Psyntax.pform) (pheap2 : Psyntax.pform) : Psyntax.pform list =
  List.map (fun widening -> !widening pheap1 pheap2)
    (map_option (fun abs_int -> (!abs_int).widening) !Registry.abs_int_registry)


(* Force Plugin_callback.add_abs_int to be linked with plugin_interface;
   there does not seem to be another way do achieve this from the code *)
let _ = Plugin_callback.add_abs_int
