(********************************************************
   This file is part of coreStar
        src/symbexe/symexec.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)


open Cfg_core
open Core
open Format
open Misc
open Psyntax
open Sepprover
open Spec
open Specification
open Vars


type execType = Abduct | Check | SymExec

(* global variables *)

let exec_type : execType ref = ref SymExec
let curr_abduct_logic : Psyntax.logic ref = ref Psyntax.empty_logic
let curr_logic : Psyntax.logic ref = ref Psyntax.empty_logic
let curr_abs_rules : Psyntax.logic ref = ref Psyntax.empty_logic


(* ================  transition system ==================  *)
type ntype = Plain | Good | Error | Abs | UnExplored

type etype = ExecE | AbsE | ContE | ExitE

type id = int

let file = ref ""

let proof_succeeded = ref true

let set_group,grouped = let x = ref false in (fun y -> x := y),(fun () -> !x)

let fresh_node = let node_counter = ref 0 in fun () ->  let x = !node_counter in node_counter := x+1; x

let fresh_file = let file_id = ref 0 in fun () -> let x = !file_id in file_id := x+1;  Sys.getcwd() ^  "/" ^ !file ^ ".proof_file_"^(string_of_int x)^".txt"


type node = {
  mutable content : string;
  id : id;
  mutable ntype : ntype;
  mutable url : string;
  mutable outedges : edge list;
  mutable inedges : edge list;
  cfg : cfg_node option;
}
and edge = {
  label : string;
  clabel : string;
  etype : etype;
  src : node;
  dest : node;
  file : string option;
}


let graphe = ref []


let mk_node c id nt url oed ied cfg =
 { content = c;
   id = id;
   ntype = nt;
   url = url;
   outedges = oed;
   inedges = ied;
   cfg = cfg
 }

let node_get_content (n:node) : string =
  n.content

let node_get_idd (n:node) : id =
  n.id

let node_get_ntype (n:node) : ntype =
  n.ntype

let node_get_url (n:node) : string =
  n.url


module Idmap =
  Map.Make(struct
	     type t = int option
	     let compare = compare
	   end)

let graphn = ref  Idmap.empty
let startnodes : node list ref = ref []

let make_start_node node = startnodes := node::!startnodes

let pp_dotty_transition_system () =
  let foname = (!file) ^ ".execution_core.dot~" in
  let dotty_out = open_out foname in
  let dotty_outf = formatter_of_out_channel dotty_out in
  if Config.symb_debug() then printf "\n Writing transition system file execution_core.dot  \n";
  fprintf dotty_outf "digraph main { \nnode [shape=box,  labeljust=l];\n\n";
  Idmap.iter
    (fun cfg nodes -> (
      (* Print Abs nodes. *)
      (if grouped () then
        match cfg with Some cfg -> fprintf dotty_outf "subgraph cluster_cfg%i {\n"  cfg | _ -> ());
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=Dot.escape_for_label label in
	let url = if url = "" then "" else ", URL=\"file://" ^ url ^"\"" in
	match ty with
	| Plain -> ()
	| Good ->  ()
	| Error ->  ()
	| UnExplored -> ()
	| Abs ->  fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=yellow, style=filled%s]\n" id label url)
	nodes;
      if grouped () then match cfg with Some _ -> fprintf dotty_outf "\n}\n" | _ -> ());
      (* Print non-Abs nodes. *)
      List.iter (fun {content=label;id=id;ntype=ty;url=url;cfg=cfg} ->
	let label=Dot.escape_for_label label in
	let url = if url = "" then "" else ", URL=\"file://" ^ url ^"\"" in
	match ty with
	  Plain ->  fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l%s]\n" id label url
	| Good ->  fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=green, style=filled%s]\n" id label url
	| Error ->  fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=red, style=filled%s]\n" id label url
	| UnExplored ->  fprintf dotty_outf "\n state%i[label=\"%s\",labeljust=l, color=orange, style=filled%s]\n" id label url
	| Abs -> () )
	nodes;
    )
    !graphn;
  List.iter (fun edge ->
    let l = Dot.escape_for_label edge.label in
    let c = Dot.escape_for_label edge.clabel in
    fprintf dotty_outf "\n state%i -> state%i [label=\"%s\", tooltip=\"%s\"%s]" edge.src.id edge.dest.id l c
	    (match edge.file with
	      None -> ""
	    | Some f -> sprintf ", URL=\"file://%s\", fontcolor=blue" f))
    !graphe;
  fprintf dotty_outf "\n\n\n}@.";
  close_out dotty_out;
  let fname = (!file) ^ ".execution_core.dot" in
  if Sys.file_exists fname then Sys.remove fname;
  Sys.rename foname (!file ^ ".execution_core.dot")


let add_node (label : string) (ty : ntype) (cfg : cfg_node option) =
  let id = fresh_node () in
  let node = {content=label; id=id; ntype=ty;url=""; outedges=[]; inedges=[]; cfg =cfg} in
  let cfgid =
    match cfg with
      None -> None
    | Some cfg -> Some (cfg.sid) in
  graphn := Idmap.add cfgid (node::(try Idmap.find cfgid !graphn with Not_found -> [])) !graphn;
  node

let add_error_node label =
  proof_succeeded := false;
  add_node label Error None

let add_abs_node label cfg = add_node label Abs (Some cfg)
let add_good_node label = add_node label Good None
let add_node_unexplored label cfg = add_node label UnExplored (Some cfg)

(* Redefines [add_node]! *)
let add_node label cfg = add_node label UnExplored (Some cfg)
let explore_node src = if src.ntype = UnExplored then src.ntype <- Plain

let add_abs_heap_node cfg (heap : inner_form_af) =
  (match !exec_type with
  | Abduct ->
    Format.fprintf (Format.str_formatter) "%a" string_inner_form_af heap;
  | Check | SymExec ->
    Format.fprintf (Format.str_formatter) "%a" string_inner_form (inner_form_af_to_form heap););
  add_abs_node (Format.flush_str_formatter ()) cfg

let add_heap_node cfg (heap : inner_form_af) =
  (match !exec_type with
  | Abduct ->
    Format.fprintf (Format.str_formatter) "%a" string_inner_form_af heap;
  | Check | SymExec ->
    Format.fprintf (Format.str_formatter) "%a" string_inner_form (inner_form_af_to_form heap););
  add_node (Format.flush_str_formatter ()) cfg

let add_error_heap_node (heap : inner_form_af) =
  (match !exec_type with
  | Abduct ->
    Format.fprintf (Format.str_formatter) "%a" string_inner_form_af heap;
  | Check | SymExec ->
    Format.fprintf (Format.str_formatter) "%a" string_inner_form (inner_form_af_to_form heap););
  add_error_node (Format.flush_str_formatter ())

let add_edge_common src dst typ lbl f=
  let e = {label=lbl; clabel=""; etype=typ; src=src; dest=dst; file=f} in
  graphe := e :: !graphe;
  src.outedges <- e :: src.outedges;
  dst.inedges <- e :: dst.inedges;
  explore_node src;
  pp_dotty_transition_system ()

let add_edge
    (src : node)
    (dest : node)
    (typ : etype)
    (label : string)
    : unit =
  add_edge_common src dest typ label None

let add_edge_with_proof src dest typ label : string =
  let f = fresh_file() in
  let out = open_out f in
  let fmt = formatter_of_out_channel out in
  Sepprover.pprint_proof fmt;
  pp_print_flush fmt ();
  close_out out;
  add_edge_common src dest typ label (Some f);
  f

let add_url_to_node src proof =
  let f = fresh_file() in
  let out = open_out f in
  List.iter (output_string out) proof;
  close_out out;
  src.url <- f


let tabulate f = List.map (fun x -> (x, f x))

let add_id_formset cfg = tabulate (add_heap_node cfg)
let add_id_abs_formset cfg = tabulate (add_abs_heap_node cfg)

let add_id_formset_edge src label sheaps cfg =
  match sheaps with
    [] ->
      if Config.symb_debug() then printf "\n\nInconsistent heap. Skip it!\n%!";
      let idd = add_good_node "Inconsistent" in ignore (add_edge_with_proof src idd ExecE (label ^"\n Inconsistent"));
	[]
  | _ ->
  let sheaps_id = add_id_formset cfg sheaps in
  List.iter (fun dest -> ignore (add_edge_with_proof src (snd dest) ExecE label)) sheaps_id;
  sheaps_id




(* ================  work list algorithm ==================  *)

 (* this type has support for creating a transition system
   (inner_form_af, id)
   id is a unique identifier of the formula
 *)
type formset_entry = inner_form_af * node

(* eventually this should be a more efficient data structure than list*)
type formset = formset_entry list


type formset_hashtbl = (int, formset) Hashtbl.t

(* table associating a cfg node to a set of heaps *)
let formset_table : formset_hashtbl = Hashtbl.create 10007

let flush_cache () =
  Hashtbl.clear formset_table

let formset_table_add key s =
  Hashtbl.add formset_table key s

let formset_table_replace key s =
  Hashtbl.replace formset_table key s

let formset_table_mem key  =
  Hashtbl.mem formset_table key

let formset_table_find key =
  try
    Hashtbl.find formset_table key
  with Not_found ->
    []  (* Default case returns false, empty list of disjunctions *)


let remove_id_formset formset =
  fst (List.split formset)

let parameter = Format.sprintf "@@parameter%i:"

let param_sub il =
  let ps (cnt, sub) arg =
    (succ cnt, add (Vars.concretep_str (parameter cnt)) arg sub) in
  snd (List.fold_left ps (0, add Spec.ret_v1 (Arg_var Spec.ret_v1) empty) il)


let call_jsr_static (sheap,id) spec il node =
  let sub' = param_sub il in
  let sub'' = (*freshening_subs*) sub' in
  let spec' = Specification.sub_spec sub'' spec in
  let res =
    match !exec_type with
    | Abduct ->
      jsr !curr_abduct_logic sheap spec' true
    | Check | SymExec ->
      jsr !curr_logic sheap spec' false
  in
  (match !exec_type with
  | Abduct | SymExec ->
    (match res with
      None ->
        let idd = add_error_node "ERROR" in
        let proof_file = add_edge_with_proof id idd ExecE
          (fprintf str_formatter "@[%a:@\n %a@]"
            Pprinter_core.pp_stmt_core node.skind
            Sepprover.pprint_counter_example ();
            flush_str_formatter ())
        in
        printf "@[<2>@{<b>ERROR@}: While executing node %d:@\n%a@.%!"
          node.sid
          Pprinter_core.pp_stmt_core node.skind;
        Sepprover.print_counter_example ();
        printf "Proof file: %s@\n" proof_file;
        printf "%s(end of error)%s@.%!"
          System.terminal_red System.terminal_white;
        Printing.pp_json_node node.sid
          (sprintf "Error while executing %d." node.sid) (Sepprover.get_counter_example());
    | Some r -> ())
  | Check -> ());
  res


exception Contained


let check_postcondition (heaps : formset_entry list) (sheap : formset_entry) =
  let sheap_noid = fst sheap in
  let node = snd sheap in
  try
    let heap,id =
      List.find
        (fun (heap,id) ->
          (frame_inner !curr_logic (inner_form_af_to_form sheap_noid) (inner_form_af_to_form heap)) <> None)
        heaps in
    if Config.symb_debug() then
      printf "\n\nPost okay \n%!";
    (* let idd = add_good_node ("EXIT: "^(Pprinter.name2str m.name)) in *)
    ignore (add_edge_with_proof node id ExitE "exit");
    true
    (* add_edge id idd "";*)
  with Not_found ->
    (match !exec_type with
    | Abduct | SymExec ->
      (let et = "Cannot prove postcondition" in
      printf "@{<b>ERROR@}: %s.@.!" et;
      Sepprover.print_counter_example ();
      printf "@{<b>(end of error)@}@.%!";
      Printing.pp_json_node (match node.cfg with None -> -1 | Some x -> x.sid) et (Sepprover.get_counter_example());
      List.iter
        (fun (heap, id) ->
          let idd = add_error_heap_node heap in
          ignore (add_edge_with_proof node idd ExecE
            (Format.fprintf
              (Format.str_formatter) "ERROR EXIT: @\n %a"
              Sepprover.pprint_counter_example ();
              Format.flush_str_formatter ())))
         heaps;
      )
      | Check -> ());
    false


(* extract the return value into variable v *)
let eliminate_ret_var
      ( name_ret_var : string)
      ( v : Vars.var)
      ( h : inner_form_af ) : inner_form_af =
   let ret_var = Vars.concretep_str name_ret_var in
   let h = update_var_to_af v (Arg_var ret_var) h in
   kill_var_af ret_var h


(* extract return values called 'name_template' into variables vs *)
let eliminate_ret_vs
      ( name_template : string )
      ( vs : Vars.var list )
      ( h : inner_form_af ) : inner_form_af  =
  let vs_i = Misc.add_index vs 1 in
  List.fold_right (fun (v,i) -> eliminate_ret_var (name_template ^ string_of_int i) v) vs_i h


let heap_pprinter f h =
  match !exec_type with
  | Abduct -> string_inner_form_af f h
  | Check | SymExec -> string_inner_form f (inner_form_af_to_form h)


let rec exec (n : cfg_node) (sheap : formset_entry) =
  let sheap_noid = fst sheap in
  let sheap = (sheap_noid, snd sheap) in
(*  if Config.symb_debug() then
    Format.printf "Output to %i with heap@\n   %a@\n" (node_get_id n) (string_ts_form (Rterm.rao_create ())) sform_noid; *)
  execute_core_stmt n sheap


and execs_with_function
   (n : cfg_node)
   (sheaps : formset_entry list)
   (g : cfg_node -> cfg_node list)
   : formset_entry list =
  let rec f ls =
    match ls with
    | [] -> []
    | [s] -> List.flatten (List.map (exec s) sheaps)
    | s::ls' -> List.flatten(List.map (fun h -> exec s h) sheaps) @ (f ls')
  in
  let succs = g n in
  match succs with
    [] ->
      if Config.symb_debug() then printf "Exit node %i\n%!" (n.sid);
      sheaps
  |  _ -> f succs

and execs_one n sheaps =
	execs_with_function n sheaps (fun n -> if n.skind = End then [] else n.succs)

and execs n sheaps =
	execs_with_function n sheaps (fun n -> [n])



and execute_core_stmt
    (n : cfg_node)
    (sheap : formset_entry)
    : formset_entry list =
  let sheap_noid = fst sheap in
  if Config.symb_debug() then begin
    Format.printf "@\nExecuting statement:@ %a%!" Pprinter_core.pp_stmt_core n.skind;
    Format.printf "@\nwith heap :@\n    %a@\n@\n@.%!" heap_pprinter sheap_noid
  end;
  if Config.symb_debug() then
    (Format.printf "\nStarting execution of node %i \n%!" (n.sid);
    Format.printf "@\nExecuting statement:@ %a%!" Pprinter_core.pp_stmt_core n.skind;
    Format.printf "@\nwith heap :@\n    %a@\n@\n@.%!" heap_pprinter sheap_noid;);
  (match n.skind with
  | Label_stmt_core l ->
    (* Update the labels formset, if sheap already implied then fine, otherwise or it in. *)
    (let id = n.sid in
    try
      if Config.symb_debug() then
        Format.printf "@\nPre-abstraction heap:@\n    %a@.%!" heap_pprinter sheap_noid;
      (* TODO: Introduce curr_abduct_abs_rules? *)
      let frames_abs = Sepprover.abs !curr_abs_rules (inner_form_af_to_form sheap_noid) in
      let antiframes_abs = Sepprover.abs !curr_abs_rules (inner_form_af_to_af sheap_noid) in
      let antiframes_abs =
        if frames_abs != [] && antiframes_abs = [] then [ empty_inner_form ] else antiframes_abs in
      if Config.symb_debug() then
        (List.iter (fun heap -> Format.printf "@\nPost-abstraction heap:@\n    %a@.%!" string_inner_form heap) frames_abs;
        match !exec_type with
        | Abduct -> List.iter (fun saf -> Format.printf "@\nPost-abstraction antiheap:@\n    %a@.%!" string_inner_form saf) antiframes_abs;
        | _ -> ());
      (* Obtain abstract values of abstracted heaps using abstract interpretation *)
      let frames_abs = List.map (fun heap -> Sepprover.abstract_val heap) frames_abs in
      let antiframes_abs = List.map (fun heap -> Sepprover.abstract_val heap) antiframes_abs in
      if Config.symb_debug() then
        (List.iter (fun heap -> Format.printf "@\nPost-abstract_val heap:@\n    %a@.%!" string_inner_form heap) frames_abs;
        match !exec_type with
        | Abduct -> List.iter (fun saf -> Format.printf "@\nPost-abstract_val antiheap:@\n    %a@.%!" string_inner_form saf) antiframes_abs;
        | _ -> ());

      explore_node (snd sheap);
      let heaps_abs = List.map (fun (if1,if2) -> combine if1 if2) (cross_product frames_abs antiframes_abs) in
      let sheaps_abs = add_id_abs_formset n heaps_abs in
      List.iter
        (fun sheap2 ->
          ignore (add_edge_with_proof (snd sheap) (snd sheap2) AbsE
            ("Abstract@"^(Debug.toString Pprinter_core.pp_stmt_core n.skind))))
        sheaps_abs;

      if Config.symb_debug() then
        (Format.printf "\nAbstracted heaps before filtering: \n%!";
        List.iter (fun (heap, id) -> Format.printf "@\n    %a\n@.%!" heap_pprinter heap;) sheaps_abs;);
      let formset = (formset_table_find id) in
      if Config.symb_debug() then
        (Format.printf "\nPreviously abstracted heaps: \n%!";
        List.iter (fun (heap, id) -> Format.printf "@\n    %a\n@.%!" heap_pprinter heap;) formset;);
      let sheaps_abs = map_option
        (fun (sheap2,id2) ->
          (let s = ref [] in
            (if (List.for_all
              (fun (sheap1,id1) ->
                let sheap1_form = inner_form_af_to_form sheap1 in
                let sheap1_af = inner_form_af_to_af sheap1 in
                let sheap2_form = inner_form_af_to_form sheap2 in
                let sheap2_af = inner_form_af_to_af sheap2 in
                let sheap1_form,sheap2_form =
                  if Config.abs_int_join() then join_over_numeric sheap1_form sheap2_form
                  else sheap1_form,sheap2_form in
                let sheap1_af,sheap2_af =
                  if Config.abs_int_join() then join_over_numeric sheap1_af sheap2_af
                  else sheap1_af,sheap2_af in
                if ((frame_inner !curr_logic sheap2_form sheap1_form <> None) ||
                  (frame_inner !curr_logic sheap2_af sheap1_af <> None))
                then
                  (ignore (add_edge_with_proof id2 id1 ContE
                    ("Contains@"^(Debug.toString Pprinter_core.pp_stmt_core n.skind))); false)
                else (s := ("\n---------------------------------------------------------\n" ^
                  (string_of_proof ())) :: !s; true))
              formset)
            then
              (if !s <> [] then (add_url_to_node id2 !s);
              Some (sheap2,id2))
            else
              None)
          )
        )
        sheaps_abs in
      if Config.symb_debug() then
        (Format.printf "\nAbstracted heaps after filtering: \n%!";
        List.iter (fun (heap, id) -> Format.printf "@\n    %a\n@.%!" heap_pprinter heap;) sheaps_abs;);

      formset_table_replace id (sheaps_abs @ formset);
      execs_one n sheaps_abs
    with Contained ->
      if Config.symb_debug() then Format.printf "Formula contained.\n%!"; [])

  | Goto_stmt_core _ -> execs_one n [sheap]

  | Nop_stmt_core  -> execs_one n [sheap]

  | Call_core _ -> failwith "TODO, perhaps"
  | Assignment_core {asgn_rets=vl; asgn_spec=spec; asgn_args=il} ->
    (
      let spec = HashSet.choose spec in
      let hs = call_jsr_static sheap spec il n in
      let abort =
        match !exec_type with
        | Check ->
          (match hs with | None -> false | Some _ -> false)
        | _ -> false
      in
      if abort then
        [ (empty_inner_form_af, add_good_node "Abort") ]
      else
        let hs = match hs with | None -> [] | Some hs -> hs in
        let hs =
          match vl with
          | [] -> hs
          | vs -> List.map (eliminate_ret_vs "$ret_v" vs) hs
        in
        let hs = add_id_formset_edge (snd sheap) (Debug.toString Pprinter_core.pp_stmt_core n.skind) hs n in
        execs_one n hs
    )

  | End ->
    (match !exec_type with
    | Abduct ->
      ignore (add_edge_with_proof (snd sheap) (add_good_node ("Exit")) ExitE "exit")
    | _ -> ());
    execs_one n [sheap]
  )


(* TODO: a meaningful description of what this does *)
let verify
    (mname : string)
    (stmts : cfg_node list)
    (spec : spec)
    (lo : logic)
    (abs_rules : logic)
    : bool
    =
  flush_cache ();
  (* remove methods that are declared abstraction *)
  exec_type := SymExec;
  curr_logic := lo;
  curr_abs_rules := abs_rules;
  stmts_to_cfg stmts;
  match stmts with
  | [] -> failwith "Internal error: Method body shouldn't be empty."
  | s::_ ->
      let id = add_good_node ("Start "^mname) in
      make_start_node id;
      match Sepprover.convert (spec.pre) with
        None ->
          printf "@{<b>WARNING@}: %s has an unsatisfiable precondition@.%!" mname;
          false
      |	Some spec_pre ->
          proof_succeeded := true;
          let pre = lift_inner_form spec_pre in
          let posts = execute_core_stmt s (pre, id) in
          let post =
            match Sepprover.convert (spec.post) with
              None ->
                printf "@[@{<b>WARNING@}: %s has an unsatisfiable postcondition@.%!" mname;
                empty_inner_form_af
            | Some spec_post -> lift_inner_form spec_post
          in
          let id_exit = add_good_node ("Exit") in
          let ret = List.for_all (check_postcondition [(post, id_exit)]) posts in
          pp_dotty_transition_system ();
          (* TODO: the way verification failure is currently handled is stupid *)
          if !proof_succeeded then ret else false


let verify_ensures
     (name : string)
     (stmts: cfg_node list)
     (post : Psyntax.pform)
     conjoin_with_res_true
     (oldexp_frames : inner_form list list)
     (lo : logic)
     (abs_rules : logic)
     : unit
     =
  flush_cache ();
  (* construct the specification of the ensures clause *)
	let rec conjoin_disjunctions (d1 : inner_form list) (d2 : inner_form list) : inner_form list =
		match d1 with
			| [] -> []
			| d1first::d1rest ->
				List.append (
					List.map (fun d -> Sepprover.conjoin_inner d1first d) d2
				) (conjoin_disjunctions d1rest d2)
	in
	let oldexp_results = List.fold_left (fun acc oldexp_res -> conjoin_disjunctions oldexp_res acc) [Sepprover.inner_truth] oldexp_frames in
	  (* substitute $ret_var in the post! *)
	let post = subst_pform (add Spec.ret_v1 (Arg_var(Vars.concretep_str (name_ret_v1^"_post"))) empty) post in
	let ensures_preconds = List.map
    (fun oldexp_result -> lift_inner_form (Sepprover.conjoin post oldexp_result)) oldexp_results in
  let ensures_postcond =
    match Sepprover.convert (conjoin_with_res_true post) with
      None -> printf "@{<b>WARNING@}: %s has an unsatisfiable postcondition@.%!" name; empty_inner_form_af
    | Some post -> lift_inner_form post
  in
	(* now do the verification *)
  exec_type := SymExec;
	curr_logic := lo;
  curr_abs_rules := abs_rules;
  stmts_to_cfg stmts;
  match stmts with
    [] -> assert false
  | s::stmts ->
      let id = add_good_node ("Start "^name) in
      make_start_node id;
      let posts = execs s (List.map (fun pre -> (pre,id)) ensures_preconds) in
      let id_exit = add_good_node ("Exit") in
      ignore (List.map
        (fun post ->
          check_postcondition [(ensures_postcond,id_exit)] post) posts);
      pp_dotty_transition_system ()


let check_and_get_frame (pre_heap,id) post_sheap =
  let post_sheap_noid = fst post_sheap in
  let node = snd post_sheap in
  let frame = frame_inner !curr_logic (inner_form_af_to_form post_sheap_noid) (inner_form_af_to_form pre_heap) in
  match frame with
    Some frame ->
                 if Config.symb_debug() then
                        (printf "\n\nOld expression okay \n%!";
                        ignore (add_edge_with_proof node id ExitE "exit");
                        frame)
                 else
                        frame
  | None ->
      let et = "Cannot prove frame for old expression" in
      (printf "@{<b>ERROR:@} %s.@.%!" et;
      Sepprover.print_counter_example ();
      ignore (add_edge_with_proof
          node
          (add_error_heap_node pre_heap) ExitE
          (fprintf str_formatter "@[<2>ERROR EXIT:@\n%a@."
              Sepprover.pprint_counter_example ();
              flush_str_formatter ()));
      printf "@{<b>(end of error)@}@.%!";
      Printing.pp_json_node
        (match node.cfg with None -> -1 | Some x -> x.sid) et (Sepprover.get_counter_example());
      [])


(* TODO: Is this unused? What about the functions it calls? *)
let get_frame
     (stmts : cfg_node list)
     (pre : Psyntax.pform)
     (lo : logic)
     (abs_rules : logic)
     : inner_form list
     =
  flush_cache ();
  exec_type := SymExec;
  curr_logic := lo;
  curr_abs_rules := abs_rules;
  stmts_to_cfg stmts;
  match stmts with
    [] -> assert false
  | s::stmts ->
		  let id = add_good_node ("Start") in
      make_start_node id;
      let rlogic_pre = Sepprover.convert pre in
      match rlogic_pre with
        None -> printf "@{<b>WARNING:@} False precondition in spec.@.%!"; []
      |	Some rlogic_pre ->
        let pre = lift_inner_form rlogic_pre in
        let post =
          match execute_core_stmt s (pre, id) with
          | [p] -> p
          | [] -> assert false
          | _ -> assert false  (* an old expression is guaranteed to have only one exit point *)
        in
        let id_exit = add_good_node ("Exit") in
        check_and_get_frame (pre,id_exit) post

let verify_inner
    (mname : string)
    (stmts : cfg_node list)
    (spec_pre : inner_form)
    (spec_post : inner_form)
    (lo : logic)
    (abs_rules : logic)
    : bool
    =
  exec_type := Check;
  curr_logic := lo;
  curr_abs_rules := abs_rules;
  stmts_to_cfg stmts;
  match stmts with
  | [] -> failwith "Internal error: Method body shouldn't be empty."
  | s::_ ->
      let id = add_good_node ("Start "^mname) in
      make_start_node id;
      let pre = lift_inner_form spec_pre in
      let posts = execute_core_stmt s (pre, id) in
      let post = lift_inner_form spec_post in
      let id_exit = add_good_node ("Exit") in
      List.for_all (check_postcondition [(post, id_exit)]) posts


let bi_abduct
    (mname : string)
    (stmts : cfg_node list)
    (spec : spec)
    (lo : logic)
    (abduct_lo : logic)
    (abs_rules : logic)
    : (inner_form * inner_form) list
    =
  flush_cache ();
  curr_logic := lo;
  curr_abduct_logic := abduct_lo;
  curr_abs_rules := abs_rules;
  stmts_to_cfg stmts;
  match stmts with
  | [] -> []
  | s::_ ->
      match Sepprover.convert (spec.pre) with
        None -> printf "@{<b>WARNING@}: %s has an unsatisfiable precondition@.%!" mname; []
      |	Some pre ->
        if Config.symb_debug() then
          Printf.printf "\nStarting abduction...\n%!";
        exec_type := Abduct;
         let id = add_good_node ("Start "^mname) in
         make_start_node id;
        let posts = execute_core_stmt s (lift_inner_form pre, id) in
        (* build spec pre/post pairs *)
        let specs = List.map
          (fun (heap,_) -> (Sepprover.conjoin_inner pre (inner_form_af_to_af heap), inner_form_af_to_form heap))
          posts in
        if Config.symb_debug()
        then begin
          Format.printf "\nCandidate specs: \n%!";
          List.iter (fun (spec_pre, spec_post) ->
            Format.printf "@\nSpec pre:@\n    %a@.%!" string_inner_form spec_pre;
            Format.printf "@\nSpec post:@\n    %a@.%!" string_inner_form spec_post;
            ) specs;
        end;
        (* eliminate those for which the symbolic execution does not go through *)
        if Config.symb_debug() then
            Printf.printf "\nStarting symbolic execution...\n%!";
        let cnt = ref 0 in
        let specs' = List.filter (fun (spec_pre, spec_post) ->
          cnt := !cnt + 1;
          if Config.symb_debug()
          then begin
            Printf.printf "\nSymbolic execution for:\n%!";
            Format.printf "@\nSpec pre:@\n    %a@.%!" string_inner_form spec_pre;
            Format.printf "@\nSpec post:@\n    %a@.%!" string_inner_form spec_post;
          end;
          Hashtbl.clear formset_table;
          verify_inner (mname^".check("^(string_of_int !cnt)^")") stmts spec_pre spec_post lo abs_rules) specs in
        specs'
