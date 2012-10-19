(********************************************************
   This file is part of coreStar
        src/symbexe_syntax/pprinter_core.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Core
open Psyntax
open Spec

(** Pretty printer for core programs. Note that this handles a lot more
  than the data structure in core.ml. *)

let core_debug () = false

let rec args2str  arg = 
  match arg with 
  | Arg_var v -> Vars.string_var v
  | Arg_string s -> s 
  | Arg_op ("builtin_plus",[a1;a2]) ->  "("^(args2str a1)^"+"^(args2str a2)^")"
  | Arg_op ("builtin_minus",[a1;a2]) ->  "("^(args2str a1)^"-"^(args2str a2)^")"
  | Arg_op ("builtin_mult",[a1;a2]) ->  "("^(args2str a1)^"*"^(args2str a2)^")"  
  | Arg_op (name,args) ->  name^"("^( args_list2str args)^")" 
  | Arg_cons (name,args) -> name^"("^( args_list2str args)^")" 
  | Arg_record fldlist -> "[{"^(args_fldlist2str fldlist)^"}]"
and args_list2str argsl = 
  match argsl with 
  | [] -> ""
  | [a] ->  args2str a
  | a::al ->  (args2str a)^","^(args_list2str al)
and args_fldlist2str fdl =  
  match fdl with 
  | [] ->  ""
  | [(f,a)] -> f^"="^( args2str a)
  | (f,a)::fdl -> f^"="^(args2str a)^"; "^(args_fldlist2str fdl)



let rec form_at2str pa =  
  match pa with 
    P_NEQ(a1,a2) ->(args2str a1)^ "!= "^  (args2str a2)
  | P_EQ(a1,a2) ->  (args2str a1)^ " = "^ (args2str a2)
  | P_PPred(op,al) -> "!"^op^"("^ (args_list2str al)^")"
  | P_SPred (s,al) -> s^"("^ (args_list2str al)^")"
  | P_Or(f1,f2) -> "[[("^(list_form2str f1)^" || "^" [("^( list_form2str f2)^")]]"
  | P_Wand(f1,f2) -> "[[("^(list_form2str f1)^" -* "^" [("^( list_form2str f2)^")]]"
  | P_Septract(f1,f2) ->  "[[("^(list_form2str f1)^" -o "^" [("^( list_form2str f2)^")]]"
  | P_False ->  "False"
and list_form2str  list = 
  match list with 
    [] ->  ""
  | [x] ->  (form_at2str x)
  | x::xs -> (form_at2str x)^" * "^list_form2str  xs 






  
let variable_list2str lv =
  Debug.list_format "," Vars.pp_var lv

let pp_stmt_core (ppf: Format.formatter) : core_statement -> unit = 
  function
  | Nop_stmt_core -> 
      Format.fprintf ppf "nop;"
  | Label_stmt_core l ->  
      Format.fprintf ppf "label %s;" l 
  | Assignment_core {call_rets=v; call_spec=spec; call_args=e}-> 
      Format.fprintf ppf "assign %a@ @[%a@]@[(%a)@];"
	(fun ppf v -> match v with [] -> () | _ -> Format.fprintf ppf "%a@ :=@ " variable_list2str v) v	
	specSet2str spec
	string_args_list e
  | Call_core _ -> failwith "todo"
  | Goto_stmt_core l ->
      Format.fprintf ppf 
	"goto %a;"  
	(Debug.list_format "," (fun ppf -> Format.fprintf ppf "%s")) l
  | End -> Format.fprintf ppf "end;"



