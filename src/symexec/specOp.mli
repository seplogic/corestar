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

val mk_spec :
  Psyntax.form -> Psyntax.form -> Spec.excep_post -> Spec.spec
val spec2str : Format.formatter -> Spec.spec -> unit
val specSet2str : Format.formatter -> Spec.spec HashSet.t -> unit
val pprinter_core_spec2str : Spec.spec -> string
val name_ret_v1 : string
val ret_v1 : Vars.var
val parameter : int -> string
val parameter_var : int -> Vars.var
