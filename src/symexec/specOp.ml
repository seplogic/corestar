(********************************************************
   This file is part of coreStar
        src/symexec_ast/specOp.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Format

let spec2str ppf spec  =
  let po s = fprintf ppf "@\n@[<4>{%a}@]" Psyntax.string_form s in
  po spec.Spec.pre; po spec.Spec.post

let specSet2str ppf specs =
  fprintf ppf "@\n@[<4>{";
  Debug.list_format ", " spec2str ppf (HashSet.elements specs);
  fprintf ppf "}@]"

let pprinter_core_spec2str = Debug.toString spec2str

let name_ret_v1 = "$ret_v1"
let ret_v1 = Vars.concretep_str name_ret_v1

let parameter n = "@parameter"^(string_of_int n)^":"
let parameter_var n = (Vars.concretep_str (parameter n))
