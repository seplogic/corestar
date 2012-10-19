(********************************************************
   This file is part of coreStar
        src/symbexe_syntax/spec.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


(** Data structures used to represent specifications.
  Also, their pretty-printing. *)

open Format

module ClassMap = Map.Make (struct type t = string let compare = compare end)

type excep_post = Psyntax.pform ClassMap.t 

type spec = 
    { pre : Psyntax.pform;
      post : Psyntax.pform;
      excep : excep_post }


let mk_spec pre post excep = 
    { pre = pre;
      post = post;
      excep = excep }

let spec2str ppf (spec: spec)  = 
  let po s = fprintf ppf "@\n@[<4>{%a}@]" Psyntax.string_form s in
  po spec.pre; po spec.post;
  ClassMap.iter (fun _ s -> po s) spec.excep

let specSet2str ppf specs =
  fprintf ppf "@\n@[<4>{";
  Debug.list_format ", " spec2str ppf (HashSet.elements specs);
  fprintf ppf "}@]"

let pprinter_core_spec2str = ((Debug.toString spec2str) : (spec -> string))
  
let name_ret_v1 = "$ret_v1"
let ret_v1 = Vars.concretep_str name_ret_v1

let parameter n = "@parameter"^(string_of_int n)^":"
let parameter_var n = (Vars.concretep_str (parameter n))
