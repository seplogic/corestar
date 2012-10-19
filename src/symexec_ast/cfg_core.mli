(********************************************************
   This file is part of coreStar
        src/symbexe_syntax/cfg_core.mli
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


type cfg_node = {
  skind : Core.core_statement;
  sid : int;
  mutable succs : cfg_node list;
  mutable preds : cfg_node list;
}
val mk_node : Core.core_statement -> cfg_node
val stmts_to_cfg : cfg_node list -> unit
val print_icfg_dotty : (cfg_node list * string) list -> string -> unit
val print_core : string -> string -> cfg_node list -> unit
