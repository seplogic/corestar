(********************************************************
   This file is part of coreStar
        src/plugins/registry.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

 
(* Registry of plugins for abstract interpretation *)
let abs_int_registry : (Plugin.abs_int ref) list ref = ref []
