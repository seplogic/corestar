(********************************************************
   This file is part of coreStar
        src/symexec_ast/pp_core.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

val pp_ast_core : Format.formatter -> Core.ast_spec Core.core_statement -> unit

val pp_inner_core
  : Format.formatter -> Core.inner_spec Core.core_statement -> unit
