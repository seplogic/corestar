(********************************************************
   This file is part of coreStar
        src/symexec_ast/specOp.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

val spec2str : Format.formatter -> Spec.ast_spec -> unit
val specSet2str : Format.formatter -> Core.ast_spec -> unit
val pprinter_core_spec2str : Spec.ast_spec -> string
val name_ret_v1 : string
val ret_v1 : Vars.var
val parameter : int -> string
val parameter_var : int -> Vars.var
