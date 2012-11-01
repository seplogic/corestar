(********************************************************
   This file is part of coreStar
        src/prover_syntax/psyntax.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

(******************************************************************
    Syntax for Separation logic theorem prover
*******************************************************************)


(************************************************************
   The syntactic representation of terms.
*************************************************************)
open Debug
open Format
open Vars
(*F#
open Microsoft.FSharp.Compatibility
F#*)

exception Contradiction


(* Main terms *)
type args =
  | Arg_var of Vars.var
  | Arg_string of string
  | Arg_op of string * args list
  | Arg_cons of string * args list  (* Do not use *)
  | Arg_record of (string *  args) list (* Do not use *)



let mkArgRecord fldlist =
  Arg_record (List.sort (fun (a1,b1) (a2,b2) -> compare a1 a2) fldlist)

type fldlist = (string * args) list

(* Type for substitution on variables in programs *)
(*IF-OCAML*)
module VarSet =
  Set.Make(struct
    type t = var
    let compare = compare
  end)
type varset = VarSet.t
(*ENDIF-OCAML*)

(*F#
module VarSet = Set
type varset = var VarSet.t
F#*)

(* TODO(rgrig): Remove these. *)
let vs_mem = VarSet.mem
let vs_add = VarSet.add
let vs_empty = VarSet.empty
let vs_is_empty = VarSet.is_empty
let vs_fold = VarSet.fold
let vs_iter = VarSet.iter
let vs_union = VarSet.union
let vs_inter = VarSet.inter
let vs_diff = VarSet.diff
let vs_exists = VarSet.exists
let vs_for_all = VarSet.for_all

let vs_from_list vl = List.fold_right (fun vs v -> vs_add vs v) vl vs_empty


(*IF-OCAML*)
module VarMap =
  Map.Make(struct
    type t = Vars.var
    let compare = compare
  end)

type 'a varmap_t = 'a VarMap.t
(*ENDIF-OCAML*)

(*F#
module VarMap = Map
type 'a varmap_t = VarMap.t<Vars.var,'a>
F#*)

type varmapargs = args varmap_t

let vm_add = VarMap.add
let vm_empty = VarMap.empty
let vm_find = VarMap.find
let vm_mem = VarMap.mem
let vm_is_empty = VarMap.is_empty

(*IF-OCAML*)
module VarHash = Hashtbl.Make(struct
    type t = Vars.var
    let equal = (=)
    let hash = Hashtbl.hash
  end)
type varhashargs = args VarHash.t
type 'a varhash_t = 'a VarHash.t
(*ENDIF-OCAML*)

(*F#
module VarHash = Hashtbl
type 'a varhash_t = VarHash.t<Vars.var,'a>
type 'a varhashargs = ('a args) varhash_t
F#*)

let vh_create = VarHash.create
let vh_add = VarHash.add
let vh_find = VarHash.find



type varmap =
  | Plain of varmapargs
  | Freshen of varmapargs *  varhashargs


let find key (map : varmap) =
  match map with
    Plain map -> vm_find key map
  | Freshen (map,h) ->(
      try vm_find key map
      with Not_found ->
	try vh_find h key
	with Not_found ->
	  let newvar = Arg_var (freshen key) in
	  vh_add h key newvar;
	  newvar
     )

let add (key : Vars.var)  (v : args)  (map : varmap) : varmap =
  match map with
    Plain map -> Plain (vm_add key v map)
  | Freshen (map,h) -> Freshen((vm_add key v map),h)

let empty : varmap = Plain (vm_empty)


let freshening_subs subs : varmap =
    match subs with
      Plain subs -> Freshen (subs, vh_create 30 )
    | _ -> unsupported_s "freshening_subs applied to wrong argument type."



let subst_kill_vars_to_fresh_prog vars =
  Plain (vs_fold (fun ev vm -> vm_add  ev (Arg_var (freshp())) vm) vars vm_empty)

let subst_kill_vars_to_fresh_exist vars =
  Plain (vs_fold (fun ev vm -> vm_add  ev (Arg_var (freshe())) vm) vars vm_empty)

let subst_freshen_vars vars =
  Plain (vs_fold (fun ev vm -> vm_add  ev (Arg_var (freshen ev)) vm) vars vm_empty)


(* substitution code for formula *)
let subst_var subs v = (try find v subs with Not_found -> Arg_var v)

let rec subst_args subs arg : args=
  match arg with
  | Arg_var v -> (subst_var subs v)
  | Arg_string s -> Arg_string s
  | Arg_op (name,args) -> Arg_op(name,List.map (subst_args subs) args)
  | Arg_cons (name,args) -> Arg_cons(name,List.map (subst_args subs) args)
  | Arg_record fldlist -> Arg_record (List.map (fun (f,v) -> f,subst_args subs v) fldlist)

let rec string_args ppf arg =
  match arg with
  | Arg_var v -> Format.fprintf ppf "%s" (string_var v)
  | Arg_string s -> Format.fprintf ppf "\"%s\""  s
  | Arg_op ("builtin_plus",[a1;a2]) -> Format.fprintf ppf "(%a+%a)" string_args a1 string_args a2
  | Arg_op ("builtin_minus",[a1;a2]) -> Format.fprintf ppf "(%a-%a)" string_args a1 string_args a2
  | Arg_op ("builtin_mult",[a1;a2]) -> Format.fprintf ppf "(%a*%a)" string_args a1 string_args a2
  | Arg_op ("tuple",al) -> Format.fprintf ppf "(%a)" string_args_list al
  | Arg_op (name,args) -> Format.fprintf ppf "%s(%a)" name string_args_list args
  | Arg_cons (name,args) -> Format.fprintf ppf "%s(%a)" name string_args_list args
  | Arg_record fldlist ->
      Format.fprintf ppf "@[{%a}@]" string_args_fldlist fldlist
and string_args_list ppf argsl =
  match argsl with
    [] -> Format.fprintf ppf ""
  | [a] -> Format.fprintf ppf "%a" string_args a
  | a::al -> Format.fprintf ppf "%a,@ %a" string_args a string_args_list al
and string_args_fldlist ppf fdl =
  match fdl with
    [] -> Format.fprintf ppf ""
  | [(f,a)] -> Format.fprintf ppf "%s=%a" f string_args a
  | (f,a)::fdl -> Format.fprintf ppf "%s=%a;@ %a" f string_args a string_args_fldlist fdl


let rec get_vars arg : Vars.var list =
  match arg with
  | Arg_var v -> [v]
  | Arg_string s -> []
  | Arg_op (name, args) -> List.flatten (List.map get_vars args)
  | Arg_cons (name, args) -> List.flatten (List.map get_vars args)
  | Arg_record fldlist -> List.flatten (List.map (fun (f,a) -> get_vars a) fldlist)


let rec fv_args args set =
  match args with
    Arg_var var -> vs_add var set
  | Arg_string _ -> set
  | Arg_op (name,argsl) -> fv_args_list argsl set
  | Arg_cons (name,argsl) -> fv_args_list argsl set
  | Arg_record fldlist -> fv_fld_list fldlist set
and fv_args_list argsl set =
  match argsl with
    [] -> set
  | args::argsl -> fv_args_list argsl (fv_args args set)
and fv_fld_list fldlist set =
  match fldlist with
    [] -> set
  | (f,args)::fldlist -> fv_fld_list fldlist (fv_args args set)



let rec ev_args args set =
  match args with
    Arg_var var -> (match var with EVar _ -> vs_add var set | _ -> set )
  | Arg_string _ -> set
  | Arg_op (name,argsl) -> ev_args_list argsl set
  | Arg_cons (name,argsl) -> ev_args_list argsl set
  | Arg_record fldlist -> ev_fld_list fldlist set
and ev_args_list argsl set =
  match argsl with
    [] -> set
  | args::argsl -> ev_args_list argsl (ev_args args set)
and ev_fld_list fldlist set =
  match fldlist with
    [] -> set
  | (f,args)::fldlist -> ev_fld_list fldlist (ev_args args set)

(****************************************************************
   Formula
 ****************************************************************)

type pform_at =
  | P_EQ of args * args
  | P_NEQ of args * args
  | P_PPred of string * args list
  | P_SPred of string * args list
  | P_Wand of pform * pform
  | P_Or of pform * pform
  | P_Septract of pform * pform
  | P_False
and pform = pform_at list


let mkFalse = [P_False]

let isFalse f =
  match f with
    [P_False] -> true
  | _ -> false

let pconjunction (f1 : pform)  (f2 : pform) : pform =
 if isFalse f1 then f1 else if isFalse f2 then f2 else f1 @ f2

let (&&&) = pconjunction


let pwand f1 f2 = [P_Wand(f1,f2)]

let mkNEQ(a1,a2) = [P_NEQ(a1,a2)]

let mkEQ(a1,a2) = [P_EQ(a1,a2)]

let mkPPred(n,al) = [P_PPred(n,al)]
let mkSPred(n,al) = [P_SPred(n,al)]

let mkOr(f1,f2) =
  if isFalse f1 then f2
  else if isFalse f2 then f1
  else [P_Or(f1,f2)]

let mkWand(f1,f2) =
  [P_Wand(f1,f2)]

let mkSeptract(f1,f2) =
  if isFalse f1 then f1
  else if isFalse f2 then f2
  else [P_Septract(f1,f2)]

let mkEmpty = []


let rec subst_pform_at subs pa=
  match pa with
   | P_EQ(a1,a2) -> mkEQ(subst_args subs  a1, subst_args subs a2)
   | P_NEQ (a1,a2) ->
       let a1,a2 = subst_args subs a1, subst_args subs a2 in
       (*if a1=a2 then mkFalse else*) mkNEQ(a1,a2)
   | P_PPred(name,args) -> mkPPred(name,(List.map (subst_args subs) args))
   | P_SPred(name,args) -> mkSPred(name,(List.map (subst_args subs) args))
   | P_Or (f1,f2) -> mkOr(subst_pform subs f1,subst_pform subs f2)
   | P_Wand (f1,f2) -> mkWand(subst_pform subs f1,subst_pform subs f2)
   | P_Septract (f1,f2) -> mkSeptract(subst_pform subs f1,subst_pform subs f2)
   | P_False -> mkFalse
and subst_pform subs =
    List.fold_left (fun pf pa -> (subst_pform_at subs pa) &&& pf) []




(* pretty print *)
let rec string_varlist vl =
  match vl with
    [] -> ""
  | v::[] -> Printf.sprintf  "%s" (string_var v)
  | v::vl -> Printf.sprintf "%s,%s" (string_var v) (string_varlist vl)

let rec string_form_at ppf pa =
  match pa with
    P_NEQ(a1,a2) -> Format.fprintf ppf "%a != %a" string_args a1  string_args a2
  | P_EQ(a1,a2) -> Format.fprintf ppf "%a = %a" string_args a1  string_args a2
  | P_PPred(op,al) -> Format.fprintf ppf "!%s(%a)" op string_args_list al
  | P_SPred (s,al) -> Format.fprintf ppf "%s(%a)" s string_args_list al
  | P_Or(f1,f2) -> Format.fprintf ppf "(%a)@ || (%a)" string_form f1 string_form f2
  | P_Wand(f1,f2) -> Format.fprintf ppf "(%a)@ -* (%a)" string_form f1  string_form f2
  | P_Septract(f1,f2) -> Format.fprintf ppf "(%a)@ -o (%a)" string_form f1  string_form f2
  | P_False -> Format.fprintf ppf "False"
and string_form ppf pf =
  list_format "*" string_form_at ppf pf





let rec fv_form_at pa set =
  match pa with
    P_EQ(x,y) -> fv_args x (fv_args y set)
  | P_NEQ(x,y) -> fv_args x (fv_args y set)
  | P_PPred(name, argsl) -> fv_args_list argsl set
  | P_SPred(name, argsl) -> fv_args_list argsl set
  | P_Wand(f1,f2)
  | P_Septract(f1,f2)
  | P_Or(f1,f2) -> fv_form f1 (fv_form f2 set)
  | P_False -> set
and fv_form pf set =
 List.fold_left (fun set pa -> fv_form_at pa set) set pf


let closes subs p  =
  not (vs_exists (fun x -> not (vm_mem x subs)) (fv_form p vs_empty))



let rec ev_form_at pa set =
  match pa with
    P_EQ(x,y) -> ev_args x (ev_args y set)
  | P_NEQ(x,y) -> ev_args x (ev_args y set)
  | P_PPred(name, argsl) -> ev_args_list argsl set
  | P_SPred(name, argsl) -> ev_args_list argsl set
  | P_Wand(f1,f2)
  | P_Septract(f1,f2)
  | P_Or(f1,f2) -> ev_form f1 (ev_form f2 set)
  | P_False -> set
and ev_form pf set =
 List.fold_left (fun set pa -> ev_form_at pa set) set pf

type psequent = pform * pform * pform * pform


let fv_psequent (pff,pfl,pfr,pfa) =
  (fv_form pff (fv_form pfl (fv_form pfr vs_empty)))

let subst_psequent subst (pff,pfl,pfr,pfa) =
  (subst_pform subst pff, subst_pform subst pfl, subst_pform subst pfr)



let purify pal =
  List.map (
    fun x ->
      match x with
	P_EQ(_,_) | P_NEQ(_,_) -> x
      |	P_SPred(n,al) -> P_PPred(n,al)
      |	_ -> unsupported ()
	    ) pal



(* Determines whether given term contains only numerical subterms *)
let rec is_numerical_args (arg : args) : bool =
  let is_integer_const (s : string) : bool =
    let rxp = (Str.regexp "^\\(-?[0-9]+\\)") in
    Str.string_match rxp s 0
  in
  match arg with
  | Arg_var _ -> true
  | Arg_op ("numeric_const", [Arg_string (s)])
  | Arg_string s ->
    if is_integer_const s then true else false
  | Arg_op ("builtin_plus", [a1; a2])
  | Arg_op ("builtin_minus", [a1; a2])
  | Arg_op ("builtin_mult", [a1; a2]) ->
    (is_numerical_args a1) && (is_numerical_args a2)
  | Arg_op (_,_) -> false
  | _ -> assert false


(* Determines whether given formula represents a numerical constraint *)
let is_numerical_pform_at (pf_at : pform_at) : bool =
  match pf_at with
  | P_EQ (a1, a2)
(*  | P_NEQ (a1, a2) *)
  | P_PPred ("GT", [a1; a2]) | P_PPred ("GT", [Arg_op ("tuple",[a1; a2])])
  | P_PPred ("LT", [a1; a2]) | P_PPred ("LT", [Arg_op ("tuple",[a1; a2])])
  | P_PPred ("GE", [a1; a2]) | P_PPred ("GE", [Arg_op ("tuple",[a1; a2])])
  | P_PPred ("LE", [a1; a2]) | P_PPred ("LE", [Arg_op ("tuple",[a1; a2])]) ->
    (is_numerical_args a1) && (is_numerical_args a2)
  | _ -> false



(***************************************************
  Logic stuff - Rules etc
 ***************************************************)


type varterm =
    Var of varset

type where =
  | NotInContext of varterm
  | NotInTerm of varterm * args
  | PureGuard of pform

let string_vs ppf vs =
  vs_iter (fun v -> Format.fprintf ppf "%s" (string_var v)) vs

let string_where ppf where =
  match where with
    NotInContext (Var vs) ->
      Format.fprintf ppf "%a notincontext"
	string_vs vs
  | NotInTerm (Var vs, args) ->
      Format.fprintf ppf "%a notin %a"
	string_vs vs
	string_args args
  | PureGuard f ->
      Format.fprintf ppf "%a pureguard"
      string_form f




type sequent_rule =
   psequent *
   (psequent list list) *
   string *
   ((* without *) pform * pform) *
   (where list)

let pp_entailment f ((h, c) : pform * pform) =
  fprintf f "%a@ |- %a" string_form h string_form c

let pp_psequent f ((g,l,r,a) : psequent) =
  fprintf f "%a@ | %a -|@ %a" string_form g pp_entailment (l, r) string_form a

let pp_sequent_rule f ((c, hss, n, w, ss) : sequent_rule) =
  let p a b c = fprintf f "@\n@[<4>%s%a@]" a b c in
  fprintf f "@\n@[<2>rule %s:" n;
  p "" pp_psequent c;
  (match hss with
    | [] -> ()
    | x::xs ->
        let ps = list_format ";" pp_psequent in
        p "if " ps x; List.iter (p "or" ps) xs);
  p "without " pp_entailment w;
  if ss <> [] then
    p "where " (list_format ";" string_where) ss;
  fprintf f "@]"


type rewrite_guard =
    {
      without_form : pform;
      if_form : pform;
      rewrite_where : where list;
  }

type rewrite_rule =
  {
    function_name : string;
    arguments : args list;
    result : args;
    guard : rewrite_guard ;
    rewrite_name : string;
    saturate : bool;
  }



type equiv_rule = string * (pform) * (pform) * (pform) * (pform)


type rules =
  | SeqRule of sequent_rule
  | RewriteRule of rewrite_rule
  | EquivRule of equiv_rule
  | ConsDecl of string

type question =
  |  Implication of pform * pform
  |  Inconsistency of pform
  |  Frame of pform * pform
  |  Equal of pform * args * args
  |  Abs of pform
  |  Abduction of pform * pform


type test =
  |  TImplication of pform * pform * bool
  |  TInconsistency of pform * bool
  |  TFrame of pform * pform * pform
  |  TEqual of pform * args * args * bool
  |  TAbs of pform * pform


let expand_equiv_rules rules =
(*encode equiv rule as three rules *)
  let equiv_rule_to_seq_rule x list : rules list=
    match x with
      EquivRule(name, guard, leftform, rightform, without) ->
	(SeqRule((guard, leftform, [],mkEmpty), [[([],rightform,[],mkEmpty)]],name ^ "_left", (without,mkEmpty) , []))
	::
	  (SeqRule(([],[],guard&&&leftform,mkEmpty), [[([],[],guard&&&rightform,mkEmpty)]], name ^"_right", (mkEmpty, without), []))
	::
	  if(guard <> []) then
	    (SeqRule((guard, [], leftform, mkEmpty), [[([],[],rightform,mkEmpty)]], name ^ "_split", (mkEmpty, without), []))
	    ::
	      list
	  else
	    list
    | SeqRule _ | RewriteRule _ | ConsDecl _ -> x::list
  in
  List.fold_right equiv_rule_to_seq_rule rules []



    (*************************************
       Syntactic representation of terms
    **************************************)

    type var = Vars.var

    let prog_var (n : string) : var = (Vars.concretep_str n)

    let exists_var (n : string) : var = (Vars.concretee_str n)

    let fresh_exists_var () : var = (Vars.freshe ())

    let fresh_unify_var () : var = (Vars.fresha ())

    let fresh_prog_var () : var = (Vars.freshp ())

    let fresh_exists_var_str s : var = (Vars.freshe_str s)

    let fresh_prog_var_str s : var = (Vars.freshp_str s)

    (* Used in rules for pattern matching *)
    let unify_var (n : string) : var = (Vars.fresha_str n)

    type term = args

    let mkVar : var -> term = fun x -> Arg_var x

    let mkFun : string -> term list -> term = fun n tl -> Arg_op(n, tl)

    let mkString : string -> term = fun n -> Arg_string(n)

    (*************************************
       Syntactic representation of formula
    **************************************)
    type form  = pform

    (* False *)
    let mkFalse : form = mkFalse

    (* Inequality between two terms *)
    let mkNEQ : term * term -> form = fun (a1,a2) ->  mkNEQ(a1,a2)

    (* Equality between two terms *)
    let mkEQ : term * term -> form = fun (a1,a2) -> mkEQ(a1,a2)

    (* A pure predicate *)
    let mkPPred : string * term list -> form
        = fun (n,al) -> mkPPred(n, al)

    (* A spatial predicate *)
    let mkSPred : string * term list -> form
        = fun (n,al) ->  mkSPred(n, al)

    (* Disjunction of two formula *)
    let mkOr : form * form -> form  = fun (f1, f2) -> mkOr(f1,f2)

    (* Star conjunction of two formula *)
    let mkStar : form -> form -> form = fun f1 f2 -> pconjunction f1 f2

    (* Empty formula/heap*)
    let mkEmpty : form = mkEmpty


    (* returns the set of free variables  in the term *)
    let fv_form_acc f acc = fv_form f acc
    let fv_form f = fv_form f vs_empty


    (* returns the set of existential variables in the term *)
    let ev_form_acc f acc= ev_form f acc
    let ev_form f = ev_form f vs_empty



    (***************************************
     *  Pretty print functions
     ***************************************)

    let string_form : Format.formatter -> form -> unit
	= fun ppf form -> string_form ppf form


    (***************************************
     Substitution on formula
     ***************************************)

    (* Substitution on terms *)
    type variable_subst
      = varmap

    (* Creates the empty variable substitution *)
    let empty_subst : variable_subst
      = empty

    (* Adds a variable to a substitution *)
    let add_subst : var -> term -> variable_subst -> variable_subst
      = fun  v t vs -> add v t vs

    (* Makes a substitution freshen all variables it
       does have a substitution for *)
    let freshening_subst : variable_subst -> variable_subst = fun vs -> freshening_subs vs


    (* Builds a substitution which replaces each variable
       in the supplied set with a fresh program variable *)
    let subst_kill_vars_to_fresh_prog : varset -> variable_subst
      = fun vs -> subst_kill_vars_to_fresh_prog vs

    (* Builds a substitution which replaces each variable
       in the supplied set with a fresh exists variable *)
    let subst_kill_vars_to_fresh_exist : varset -> variable_subst
      = fun vs -> subst_kill_vars_to_fresh_exist vs

    (* Builds a substitution which replaces each variable
       in the supplied set with a fresh variable of the same sort*)
    let subst_freshen_vars : varset -> variable_subst
      = fun vs -> subst_freshen_vars vs

    (* Use a substitution on a formula *)
    let subst_form : variable_subst -> form -> form =
      fun vs form -> subst_pform vs form



    (*******************************************
        Logic operations
     ******************************************)


let mk_seq_rule (mat_seq,premises,name) : sequent_rule =
  mat_seq,premises,name,([],[]),[]


(* rules for simplifying septraction need defining as well *)


type logic = {
  seq_rules : sequent_rule list;
  rw_rules : rewrite_rule list;
  consdecl : string list;
  dummy : unit;
}

let empty_logic : logic = {
  seq_rules = [];
  rw_rules = [];
  consdecl = [];
  dummy = ();
}
