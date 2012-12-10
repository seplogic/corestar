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
  skind : Core.ast_core;
  sid : int;
  mutable succs : cfg_node list;
  mutable preds : cfg_node list;
}
val mk_node : Core.ast_core -> cfg_node
val stmts_to_cfg : cfg_node list -> unit
val print_icfg_dotty : (cfg_node list * string) list -> string -> unit


(* Not used by coreStar itself, but useful for frontends. *)
val print_core : string -> string -> cfg_node list -> unit
