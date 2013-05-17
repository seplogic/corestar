(********************************************************
   This file is part of coreStar
        src/prover/cterm.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std
open Debug
open Format

(* TODO(rgrig): Don't open these. *)
open Congruence
open Printing
open Psyntax
open Vars

type term_handle = CC.constant

type pattern = CC.curry_term

type flattened_args =
  | FArg_var of Vars.var
  | FArg_string of string
  | FArg_op of string * term_handle list
  | FArg_cons of string * term_handle list
  | FArg_record of (string *  term_handle) list

module SMap = Map.Make(
    struct
      type t = string
      let compare = compare
    end)

module CMap = Map.Make(
    struct
      type t = CC.constant
      let compare = compare
    end)

type term_structure =
  {
    cc : CC.t;
    function_symbols : CC.constant SMap.t;
    strings : CC.constant SMap.t;
    pvars : CC.constant VarMap.t;
    apvars : CC.constant VarMap.t;
    evars : CC.constant VarMap.t;
    avars : CC.constant VarMap.t;
    aevars : CC.constant VarMap.t;
    record_labels : CC.constant SMap.t;
    record : CC.constant;
    exists : CC.constant;
    var : CC.constant;
    tuple : CC.constant;
    originals : flattened_args CMap.t;
  }

let new_ts () =
  let cc = CC.create () in
  let c,cc = CC.fresh cc in
  let c1,cc = CC.fresh cc in
  let c2,cc = CC.fresh cc in
  let c3,cc = CC.fresh cc in
  let cc = CC.make_constructor cc c in
  let cc = CC.make_constructor cc c3 in
  {
  cc = cc;
  function_symbols = SMap.empty;
  strings = SMap.empty;
  pvars = VarMap.empty;
  avars = VarMap.empty;
  apvars = VarMap.empty;
  evars = VarMap.empty;
  aevars = VarMap.empty;
  record_labels = SMap.empty;
  originals = CMap.empty;
  record = c;
  exists = c1;
  var = c2;
  tuple = c3;
}

let get_special_ids t = [ t.record; t.exists; t.var; t.tuple ]
let get_varmaps t = [ t.pvars; t.apvars; t.evars; t.avars; t.aevars ]
let get_smaps t = [ t.function_symbols; t.strings; t.record_labels ]

let get_id find get_maps t v =
  let rec f = function
    | [] -> raise Not_found
    | m :: ms -> (try find v m with Not_found -> f ms) in
  f (get_maps t)
let get_id_of_var = get_id VarMap.find get_varmaps
let get_id_of_str = get_id SMap.find get_smaps

let inv t = ()
  (* TODO(rgrig): This doesn't hold. What should?
  let wg get k = (try get t k with Not_found -> assert false) in
  let get_id_of_var = wg get_id_of_var in
  let get_id_of_str = wg get_id_of_str in
  let check_leaves c = function
    | FArg_var v -> assert (c = get_id_of_var v)
    | FArg_string s -> assert (c = get_id_of_str s)
    | _ -> () in
  CMap.iter check_leaves t.originals
  *)

(* helpers for [conjoin] *) (* {{{ *)

let term_size t = CC.size t.cc
  (* TODO: but, don't use [Map.cardinal]; for now, a heuristic *)

let c_mk_subst () = Hashtbl.create 0, Hashtbl.create 0
let c_subst_find_gen (only_t1, common) id =
  try (true, Hashtbl.find only_t1 id)
  with Not_found -> (false, Hashtbl.find common id)
let c_subst_find subst id = snd (c_subst_find_gen subst id)
let c_subst_is_new (only_t1, common) id =
  not (Hashtbl.mem only_t1 id || Hashtbl.mem common id)
let c_subst_union ((_, common) as subst) i1 i2 =
  assert (try c_subst_find subst i1 = i2 with Not_found -> true);
  Hashtbl.replace common i1 i2
let c_subst_fresh ((only_t1, _) as subst) i1 i2 =
  assert (c_subst_is_new subst i1);
  Hashtbl.add only_t1 i1 i2

let cmap_normalize cm =
  let norm_cm = ref CMap.empty in
  let termmap = Hashtbl.create 0 in
  let record id t =
    try Hashtbl.find termmap t
    with Not_found ->
      (Hashtbl.add termmap t id; norm_cm := CMap.add id t !norm_cm; id) in
  let normalize =
    let rep = Hashtbl.create 0 in
    let rec f id =
      (try Hashtbl.find rep id with Not_found -> begin
      let record = record id in
      let new_id = match CMap.find id cm with
        | FArg_var _ as t -> record t
        | FArg_string _ as t -> record t
        | FArg_op (name, ts) -> record (FArg_op (name, List.map f ts))
        | FArg_cons (name, ts) -> record (FArg_cons (name, List.map f ts))
        | FArg_record fs ->
            let field (name, t) = (name, f t) in
            record (FArg_record (List.map field fs)) in
      Hashtbl.add rep id new_id; new_id end) in
    f in
  CMap.iter (fun id _ -> ignore (normalize id)) cm;
  (!norm_cm, termmap)

(*      x    x   f(1)   f(2)
        1 -> 2    10  -> 20   *)
let compute_term_subst get_fresh subst cm1 cm2inv =
  let record id1 t =
    try
      let id2 = Hashtbl.find cm2inv t in
      c_subst_union subst id1 id2; id2
    with Not_found ->
      let id2 = get_fresh () in
      c_subst_fresh subst id1 id2; id2 in
  let rec f id1 =
    try c_subst_find subst id1 with Not_found -> begin
      let record = record id1 in
      match CMap.find id1 cm1 with
        | FArg_var _ as t -> record t
        | FArg_string _ as t -> record t
        | FArg_op (name, ts) -> record (FArg_op (name, List.map f ts))
        | FArg_cons (name, ts) -> record (FArg_cons (name, List.map f ts))
        | FArg_record fs ->
            let field (name, t) = (name, f t) in
            record (FArg_record (List.map field fs))
    end in
  CMap.iter (fun id1 _ -> ignore (f id1)) cm1

(* }}} *)

let conjoin t1 t2 =
  if safe then (inv t1; inv t2);
  let t1, t2 = if term_size t1 > term_size t2 then t2, t1 else t1, t2 in
  let cc = ref t2.cc in
  let subst = c_mk_subst () in
  let fresh_id () = let id, new_cc = CC.fresh !cc in cc := new_cc; id in
  let record get_id v i1 =
    (try c_subst_union subst i1 (get_id t2 v)
    with Not_found -> c_subst_fresh subst i1 (fresh_id ())) in
  List.iter (VarMap.iter (record get_id_of_var)) (get_varmaps t1);
  List.iter (SMap.iter (record get_id_of_str)) (get_smaps t1);
  List.iter2 (c_subst_union subst) (get_special_ids t1) (get_special_ids t2);
  let merge_sv_maps fold find add m1 m2 =
    let f s c1 m2 =
      let sub_c1 = (try c_subst_find subst c1 with Not_found -> assert false) in
      try let c2 = find s m2 in assert (sub_c1 = c2); m2
      with Not_found -> add s sub_c1 m2 in
    fold f m1 m2 in
  let merge_smaps = merge_sv_maps SMap.fold SMap.find SMap.add in
  let merge_varmaps = merge_sv_maps VarMap.fold VarMap.find VarMap.add in
  let merge_cmap cm1 cm2 =
    let cm2, cm2inv = cmap_normalize cm2 in
    compute_term_subst fresh_id subst cm1 cm2inv;
    let get_id id1 =
      (try c_subst_find subst id1 with Not_found -> assert false) in
    let f id1 term1 =
      let term2 = (match term1 with
        | FArg_var _ as t -> t
        | FArg_string _ as t -> t
        | FArg_op (name, ts) -> FArg_op (name, List.map get_id ts)
        | FArg_cons (name, ts) -> FArg_cons (name, List.map get_id ts)
        | FArg_record fs ->
            let field (name, t) = (name, get_id t) in
            FArg_record (List.map field fs)) in
      CMap.add (get_id id1) term2 in
    CMap.fold f cm1 cm2 in
  let originals = merge_cmap t1.originals t2.originals in
  let t = { cc =
      (try CC.merge_cc (c_subst_find_gen subst) t1.cc t2.cc
      with Not_found -> assert false)
  ; function_symbols = merge_smaps t1.function_symbols t2.function_symbols
  ; strings = merge_smaps t1.strings t2.strings
  ; pvars = merge_varmaps t1.pvars t2.pvars
  ; apvars = merge_varmaps t1.apvars t2.apvars
  ; evars = merge_varmaps t1.evars t2.evars
  ; avars = merge_varmaps t1.avars t2.avars
  ; aevars = merge_varmaps t1.aevars t2.aevars
  ; record_labels = merge_smaps t1.record_labels t2.record_labels
  ; record = t2.record
  ; exists = t2.exists
  ; var = t2.var
  ; tuple = t2.tuple
  ; originals } in
  if safe then inv t;
  t

let local_debug = false

let is_good_rep ts rep =
		 try
		   (match CMap.find rep ts.originals with
                   | FArg_var v when Vars.is_pvar v -> true
		   | FArg_op(_,[])
                   | FArg_cons(_,[])
                   | FArg_string _ -> true
                   | _ -> false )
                 with Not_found -> false

let is_evar ts rep =
		 try
		   (match CMap.find rep ts.originals with
                   | FArg_var v -> Vars.is_evar v
                   | _ -> false )
                 with Not_found -> false

let find_good_rep ts rep =
        if is_good_rep ts rep then rep else
        (try
            (List.find
              (is_good_rep ts)
	      (CC.others ts.cc rep))
         with Not_found ->
           try
            (List.find
              (is_evar ts)
	      (CC.others ts.cc rep))
           with Not_found ->
              rep
)

(* TODO(rgrig): DON'T do this while printing. Just have a separate simplify. *)
(* otherwise, pretty printing is useless for debug *)
let has_pp_c ts c : bool =
  try
    match CMap.find c ts.originals with
    | FArg_var v when Vars.is_avar v -> local_debug
    | FArg_var v when Vars.is_evar v -> find_good_rep ts c = c
    | FArg_var v when Vars.is_pvar v -> VarMap.mem v ts.pvars
    | FArg_op ("tuple",_)
    | FArg_record _
      -> false
    |  _
      -> true
  with Not_found ->
    false

(* TODO(rgrig): Oh, NO! Just have a separate simplify function and let the user
call it explicitly before printing, *if* desired. *)
(* Remove pattern match variables from pretty print where possible *)
let rec get_pargs norm ts rs rep : Psyntax.args =
  if List.mem rep rs then
    if rep = find_good_rep ts rep  || (List.mem (find_good_rep ts rep) rs) then
      (* TODO: Add topological sorting to avoid printing this if possible.
         If not possible should introduce a new variable. *)
     (let cname = Printf.sprintf "CYCLE%i" (CC.const_int rep ts.cc) in
      Arg_op (cname, []))
    else get_pargs norm ts (rep::rs) (find_good_rep ts rep)
  else
  try
    let fpt = CMap.find
         (if norm then find_good_rep ts rep
          else rep) ts.originals
    in
    let fpt = match fpt with
        | FArg_var v when Vars.is_evar v
            -> CMap.find (find_good_rep ts rep) ts.originals
        | _ -> fpt in
    match fpt with
    | FArg_var v ->
        if Vars.is_avar v then begin
            let nrep = if local_debug then rep else (CC.normalise ts.cc rep) in
            if nrep <> rep then
              get_pargs norm ts (rep :: rs) (CC.normalise ts.cc rep)
            else Arg_var v
        end else Arg_var v
    | FArg_op (n,ops) ->
	Arg_op(n, List.map (get_pargs true ts (rep::rs)) ops)
    | FArg_cons (n,ops) ->
	Arg_cons (n, List.map (get_pargs true ts (rep::rs)) ops)
    | FArg_string s ->
	Arg_string s
    | FArg_record fld ->
	let a = Arg_record
	  (List.map
	     (fun (n,r) ->
	       n, get_pargs true ts (rep::rs) r)
	     fld) in
	a
  with Not_found ->
     (let cname = Printf.sprintf "NOT_FOUND%i" (CC.const_int rep ts.cc) in
      Arg_var (Vars.freshe_str cname))


(* A version of get_pargs which hides records, for use in SMT *)
(* TODO: factor out both get_pargs into a single function *)
let rec get_pargs_norecs norm ts rs rep : Psyntax.args =
  if List.mem rep rs then
    if rep = find_good_rep ts rep || (List.mem (find_good_rep ts rep) rs)  then
      (* TODO: Add topological sorting to avoid printing this if possible.
         If not possible should introduce a new variable. *)
     (let cname = Printf.sprintf "CYCLE%i" (CC.const_int rep ts.cc) in
      Arg_op (cname, []))
    else get_pargs norm ts (rep::rs) (find_good_rep ts rep)
  else
  try
    let fpt = CMap.find
         (if norm then find_good_rep ts rep
          else rep) ts.originals
    in
    let fpt = match fpt with
        | FArg_var v when Vars.is_evar v
            -> CMap.find (find_good_rep ts rep) ts.originals
        | _ -> fpt in
    match fpt with
      FArg_var v ->
        if Vars.is_avar v then begin
            let nrep = if local_debug then rep else (CC.normalise ts.cc rep) in
            if nrep <> rep then
              get_pargs_norecs norm ts (rep :: rs) (CC.normalise ts.cc rep)
            else Arg_var v
        end else Arg_var v
    | FArg_op (n,ops) ->
	Arg_op(n, List.map (get_pargs_norecs true ts (rep::rs)) ops)
    | FArg_cons (n,ops) ->
	Arg_cons (n, List.map (get_pargs_norecs true ts (rep::rs)) ops)
    | FArg_string s ->
	Arg_string s
    | FArg_record fld ->
        (let rname = Printf.sprintf "RECORD%i" (CC.const_int rep ts.cc) in
         Arg_op (rname, []))
  with Not_found ->
     (let cname = Printf.sprintf "NOT_FOUND%i" (CC.const_int rep ts.cc) in
      Arg_var (Vars.freshe_str cname))

let reconstruct ts c =
  let get_arg h = CMap.find h ts.originals in
  let rec reconstruct_arg = function
  | FArg_var v -> Arg_var v
  | FArg_string s -> Arg_string s
  | FArg_op (s, hs) -> Arg_op (s, List.map reconstruct_handle hs)
  | FArg_cons (s, hs) -> Arg_cons (s, List.map reconstruct_handle hs)
  | FArg_record shs -> Arg_record (List.map (fun (s, h) -> (s, reconstruct_handle h)) shs)
  and reconstruct_handle h = reconstruct_arg (get_arg h) in
  reconstruct_arg (get_arg c)

let pp_c ts ppf c : unit =
  try
    Psyntax.string_args ppf (reconstruct ts c)
  with Not_found ->
    (* Should call has_pp_c to check it can be pretty printed *)
    Format.fprintf ppf "No PP" (*assert false*)

let pp_ts' pp ppf first ts =
  CC.pretty_print' (fun _ -> true) (pp_c ts) pp ppf first ts.cc

let pp_ts = pp_whole pp_ts' pp_star

let pp_c ts ppf c = CC.pp_c ts.cc (pp_c ts) ppf c


let rec add_term params pt ts : 'a * term_structure =
  let (unif : bool),
    (fresh : bool),
    (lift : term_handle -> 'a),
    (app : CC.t -> 'a -> 'a -> 'a * CC.t),
    register_op, register_rec = params in
(*  Format.printf "Adding term %a.@\n" string_args pt;*)
  let c,ts =
    match pt with
    | Arg_var v when Vars.is_avar v ->
        begin
          try
            lift(VarMap.find (v) ts.avars), ts
          with Not_found ->
            (*assert (unif);   FIX this later.*)
            (* if not add to ts, and return constant to it *)
            let c,cc = CC.fresh_unifiable ts.cc in
            lift(c), {ts with cc = cc; avars = VarMap.add (v) c ts.avars; originals = CMap.add c (FArg_var (Vars.freshen_exists v))  ts.originals }
        end
    | Arg_var v when Vars.is_pvar v ->
        (* Check if variable is in current map *)
        begin
          try
            lift(VarMap.find v (if fresh && Vars.is_fresh v then ts.apvars else ts.pvars)), ts
          with Not_found ->
            (* if not add to ts, and return constant to it *)
            let c,cc = CC.fresh ts.cc in
            (*let c,cc = app cc lift(ts.var) lift(c) in  *)
            if fresh && Vars.is_fresh v then
              lift c,{ts with cc = cc; apvars = VarMap.add (v) c ts.apvars; originals = CMap.add c (FArg_var (freshen_exists v))  ts.originals }
            else
              lift c, {ts with cc = cc; pvars = VarMap.add (v) c ts.pvars; originals = CMap.add c (FArg_var v)  ts.originals }
        end
    | Arg_var v when Vars.is_evar v ->
        (* Check if variable is in current map *)
        begin
          try
            lift (VarMap.find v (if fresh then ts.aevars else ts.evars)), ts
          with Not_found ->
            let c,cc =
              if unif then CC.fresh_unifiable_exists ts.cc
              else CC.fresh_exists ts.cc in
            if fresh then
              lift(c), {ts with cc = cc; aevars = VarMap.add v c ts.aevars; originals = CMap.add c (FArg_var (Vars.freshen_exists v))  ts.originals }
            else
              lift(c), {ts with cc = cc; evars = VarMap.add v c ts.evars; originals = CMap.add c (FArg_var v)  ts.originals }
        end
    | Arg_var _ -> failwith "The guarded cases above should have matched."
    | Arg_string s ->
	begin
	  try
	    lift(SMap.find s ts.strings), ts
	  with Not_found ->
	    let c,cc = CC.fresh ts.cc in
            let cc = CC.make_constructor cc c in
	    lift(c), {ts with cc = cc; strings = SMap.add s c ts.strings; originals = CMap.add c (FArg_string s)  ts.originals }
	end
    | Arg_op (f,args) | Arg_cons (f,args) ->
	let c,ts =
	  try
	    SMap.find f ts.function_symbols, ts
	  with Not_found ->
	    let c,cc = CC.fresh ts.cc in
	    let cc = match pt with Arg_cons _ -> CC.make_constructor cc c | _ -> cc in
	    c, {ts with cc = cc; function_symbols = SMap.add f c ts.function_symbols}
	in
	let c2,ts =
	  match args with
	    [] ->
	      let c,cc = CC.add_app ts.cc c ts.tuple in
	      lift c,
                  if CMap.mem c ts.originals then
                     {ts with cc=cc}
                  else
                     {ts with cc=cc;
                      originals =
                          CMap.add c (FArg_op(f,[])) ts.originals}
	  | _ ->
	      let c2,ts,cl = add_term_list params args (lift c,ts) [] in
	      c2, register_op c2 (f, List.rev cl) ts
	in
	c2,ts
    | Arg_record fldl ->
	(* Assume fields are sorted *)
	let c,ts,lrl = add_field_list params fldl (lift ts.record, ts) [] in
	let ts = register_rec c (List.rev lrl) ts in
	c,ts
  in
  c,ts

and add_term_list params ptl (c,ts) cl =
  let _,_,_,(app : CC.t -> 'a -> 'a -> 'a * CC.t),_,_ = params in
  match ptl with
    [] -> c,ts, cl
  |  p::ptl ->
      let c2,ts = add_term params p ts in
      let c,cc = app ts.cc c c2 in
      add_term_list params ptl (c,{ts with cc = cc}) (c2::cl)

and add_field_list params fldl (c,ts) lrl =
  let _,_,lift,(app : CC.t -> 'a -> 'a -> 'a * CC.t),_,_ = params in
  match fldl with
    [] -> c,ts,lrl
  |  (lab,term)::fldl ->
      (* Add next term *)
      let ct,ts = add_term params term ts in
      (* Lookup label *)
      let cl,ts =
        try
	  SMap.find lab ts.record_labels, ts
	with Not_found ->
	  (* Add label as it doesn't already exists *)
	  let cl,cc = CC.fresh ts.cc in
	  let cc = CC.make_constructor cc cl in
	  cl, {ts with cc=cc;record_labels = SMap.add lab cl ts.record_labels}
      in
      (* Add labelled term *)
      let clt,cc = app ts.cc (lift cl) ct in
      (* Append to record *)
      let c,cc = app cc c clt in
      (* Recurse *)
      add_field_list params fldl (c,{ts with cc = cc}) ((lab,ct)::lrl)

let params_pattern =
  (true,
   true,
   (fun x-> CC.Constant x),
   (fun cc x y -> CC.App(x,y), cc),
   (fun _ _ x -> x),
   (fun _ _ x -> x))

let params_term fresh =
  (false,
   fresh,
   (fun x-> x),
   (fun cc x y -> CC.add_app cc x y),
   (fun c (fn,cl) ts ->
     if CMap.mem c ts.originals then ts else
     {ts with originals = CMap.add c (FArg_op(fn,cl)) ts.originals}),
   (fun c rl ts -> {ts with originals = CMap.add c (FArg_record(rl)) ts.originals}))

let params_pattern_to_term =
  (true,
   true,
   (fun x-> x),
   (fun cc x y -> CC.add_app cc x y),
   (fun c (fn,cl) ts ->
     if CMap.mem c ts.originals then ts else
     {ts with originals = CMap.add c (FArg_op(fn,cl)) ts.originals}),
   (fun c rl ts -> {ts with originals = CMap.add c (FArg_record(rl)) ts.originals}))

let add_pattern term ts =
  (* Add new term *)
  let c,ts = add_term params_pattern term ts in
  c,ts


let ground_pattern (pattern : args) (ts : term_structure) : term_handle * term_structure =
  let c,ts = add_term params_pattern_to_term pattern ts in
  c, ts


let ground_pattern_tuple (ptl : args list) (ts : term_structure) : term_handle * term_structure =
  let c,ts,cl = add_term_list (params_pattern_to_term) ptl (ts.tuple,ts) [] in
  let ts = {ts with originals = CMap.add c (FArg_op("tuple",List.rev cl)) ts.originals} in
  c,ts

let add_term fresh term ts =
  (* Add new term *)
  let c,ts = add_term (params_term fresh) term ts in
  c,ts




let add_tuple fresh ptl ts =
  let c,ts,cl = add_term_list (params_term fresh) ptl (ts.tuple,ts) [] in
  let ts = {ts with originals = CMap.add c (FArg_op("tuple",List.rev cl)) ts.originals} in
  c,ts

let make_tuple_pattern ptl ts =
  let c,ts,cl = add_term_list params_pattern ptl ((CC.Constant ts.tuple),ts) [] in
  c,ts


let unifies (ts : term_structure) (pt : pattern) (con : CC.constant) (cont : term_structure -> 'a) : 'a
    =
  CC.unifies ts.cc pt con (fun cc -> cont {ts with cc = cc})

let determined_exists ts cl c1 c2 : term_structure * (term_handle * term_handle) list
    =
  let cc,cp1 = CC.determined_exists ts.cc cl c1 c2 in
  {ts with cc=cc}, cp1



let equal ts c1 c2 =
  CC.rep_eq ts.cc c1 c2

let not_equal ts c1 c2 =
  CC.rep_uneq ts.cc c1 c2

let make_equal ts c1 c2 =
  {ts with cc=  CC.make_equal ts.cc c1 c2 }

let make_not_equal ts c1 c2 =
  {ts with cc=  CC.make_not_equal ts.cc c1 c2 }


let make_equal_t fresh ts t1 t2 =
  let c1,ts = add_term fresh t1 ts  in
  let c2,ts = add_term fresh t2 ts  in
  make_equal ts c1 c2

let make_not_equal_t fresh ts t1 t2 =
  let c1,ts = add_term fresh t1 ts  in
  let c2,ts = add_term fresh t2 ts  in
  make_not_equal ts c1 c2


let make_list_equal
    (ts : term_structure)
    (xs : term_handle list)
    : term_structure =
  match xs with
  | x::xs -> List.fold_left (fun ts' y -> make_equal ts' x y) ts xs
  | [] -> ts


let compress ts =
  (* TODO: This does not correctly update the originals, some will be
     lost by overwriting.  Should refactor to make the originals a
     list, and filter out pointless ones on compression. *)
  let cc,map = CC.compress_full ts.cc in
  {
  cc = cc;
  function_symbols = SMap.map map ts.function_symbols;
  strings = SMap.map map ts.strings;
  pvars = VarMap.map map ts.pvars;
  apvars = VarMap.map map ts.apvars;
  avars = VarMap.empty;
  aevars = VarMap.empty;
  evars = VarMap.map map ts.evars;
  record_labels = SMap.map map ts.record_labels;
  record = map ts.record;
  exists = map ts.exists;
   var = map ts.var;
   tuple = map ts.tuple;
  originals = CMap.fold (fun key v pp -> CMap.add (map key) v pp) ts.originals CMap.empty;
}, map


let blank_pattern_vars ts =
  {ts with
   avars = VarMap.empty;
   aevars = VarMap.empty;
   apvars = VarMap.empty
 }


let normalise ts r =
  CC.normalise ts.cc r



let get_eqs ts : (Psyntax.args * Psyntax.args ) list =
  let mask = has_pp_c ts in
  let map = fun c -> get_pargs false ts [] c in
  CC.get_eqs mask map ts.cc


let get_neqs ts : (Psyntax.args * Psyntax.args ) list =
  let mask = has_pp_c ts in
  let map = fun c -> get_pargs false ts [] c in
  CC.get_neqs mask map ts.cc

(* TODO: temporary until the bug in has_pp_c gets resolved *)
let get_eqs_all ts : (Psyntax.args * Psyntax.args ) list =
  let mask = fun _ -> true in
  let map = fun c -> get_pargs false ts [] c in
  CC.get_eqs mask map ts.cc

let get_neqs_all ts : (Psyntax.args * Psyntax.args ) list =
  let mask = fun _ -> true in
  let map = fun c -> get_pargs false ts [] c in
  CC.get_neqs mask map ts.cc

(* Versions of get_eqs and get_neqs that hide records *)
let get_eqs_norecs ts : (Psyntax.args * Psyntax.args ) list =
  let mask = has_pp_c ts in
  let map = fun c -> get_pargs_norecs false ts [] c in
  CC.get_eqs mask map ts.cc

let get_neqs_norecs ts : (Psyntax.args * Psyntax.args ) list =
  let mask = has_pp_c ts in
  let map = fun c -> get_pargs_norecs false ts [] c in
  CC.get_neqs mask map ts.cc


let get_args_rep
    (ts : term_structure)
    : (term_handle * Psyntax.args) list =
  let mask = has_pp_c ts in
  let map = fun c -> (c, get_pargs_norecs false ts [] c) in
  CC.get_reps mask map ts.cc

let get_args_all
    (ts : term_structure)
    : Psyntax.args list =
  List.map (get_pargs_norecs false ts []) (CC.get_consts ts.cc)

let get_term ts r : Psyntax.args =
  get_pargs false ts [] r

let kill_var ts v =
  try
    let r = VarMap.find v ts.pvars in
    let cc = CC.delete ts.cc r in
    let pvars = VarMap.remove v ts.pvars in
    let pp_term = CMap.find r ts.originals in
    let originals = CMap.remove r ts.originals in
    let originals =
      match pp_term with
      | FArg_var v' when Vars.is_pvar v' && v' = v
	   -> CMap.add r (FArg_var (Vars.freshen_exists v)) originals
      |  _ -> originals (* RLP: Should this raise an exception? *)
      in
    {ts with pvars = pvars; cc=cc; originals=originals}
  with Not_found ->
    ts

let update_var_to ts v e =
  let c,ts = add_term false e ts in
  let ts = kill_var ts v in
  let c2,ts = add_term false (Arg_var v) ts in
  let ts = make_equal ts c c2 in
  ts


let rewrite (ts : term_structure) (rm : rewrite_rule list) (query : term_structure * rewrite_guard -> bool) : term_structure =
  let rec rwgo rm ts =
    match rm with
      [] -> raise Backtrack.No_match
    | r::rm ->
	try
	  let t = Arg_op (r.function_name, r.arguments) in
(*	  Format.printf "Trying: %s for matches %a@\n" r.rewrite_name string_args t; *)
	  let c,ts = add_pattern t ts in
(*	  Format.printf "Pattern %a@\n" (pp_c ts) c; *)
	  CC.unifies_any ts.cc c
	    (fun (cc,c) ->
(*	      Format.printf "Applying: %s to %a@\n" r.rewrite_name (pp_c ts) c; *)
	      let x,ts = add_term true r.result {ts with cc=cc} in
(*	      Format.printf "Adding term %a = %a@\n to %a@\n" (pp_c ts) x (pp_c ts) c  pp_ts ts;*)
	      if equal ts x c || not (query (ts,r.guard)) then
		begin
(*		  Format.printf "Already matched. @\n";*)
		  raise Backtrack.No_match
		end
	      else
		Format.fprintf !(Debug.proof_dump) "Making %a = %a using %s@\n"
		  (pp_c ts) c (pp_c ts) x r.rewrite_name;
(*	        CC.print ts.cc;*)
		let ts = make_equal ts x c in
(*		Format.printf "After make equal";*)
		ts
	      )
	with Backtrack.No_match ->
	  rwgo rm ts
  in
  let rec repeat ts =
    try
      let ts = blank_pattern_vars ts in
      let ts = rwgo rm ts in
(*      Format.printf "Next go:@ %a@\n" pp_ts ts;*)
(*      CC.print ts.cc;*)
      repeat ts
    with Backtrack.No_match
	-> ts
  in
  try
    repeat ts
  with Backtrack.No_match -> assert false

let unify_patterns ts x y cont =
  try
    if CC.eq_term ts.cc x y then
      cont ts
    else
      raise Backtrack.No_match
  with Backtrack.No_match ->
    CC.unifies_any ts.cc x
      (fun (cc,c) -> CC.unifies cc y c
	  (fun cc -> cont {ts with cc=cc}))

let unify_not_equal_pattern ts x y cont =
  if CC.neq_term ts.cc x y then
    cont ts
  else raise Backtrack.No_match

let ts_eq ts1 ts2 =
  (* Would like to check ts1 = ts2, but this would be expensive.  Due
      to the operations we perform, checking pointer equality on the
      contained structure is good enough in practice.*)
  ts1.cc == ts2.cc


let var_not_used_in ts var reps : bool =
  if Vars.is_evar var then begin
	try
	  CC.rep_not_used_in ts.cc (VarMap.find var ts.aevars) reps
	with Not_found ->
	  (* TODO Check that returning false is sensible.
	     Printf.printf "Could not find existential! Impossible!";
	    assert false *)
	  false
  end else begin
      Printf.printf "Don't use non-existential variables in notincontext stuff.";
      assert false
  end

let var_not_used_in_term ts var term : bool =
  (* TODO: This ts is not return, potentially dangerous. Further review required. *)
  let pat,ts = add_pattern term ts in
  let rec pat_to_const pat reps =
     match pat with
     | CC.Constant c -> c::reps
     | CC.App (c1,c2) -> pat_to_const c1 (pat_to_const c2 reps) in
  let reps = pat_to_const pat [] in
  var_not_used_in ts var reps

let add_constructor
    (fn : string)
    (ts : term_structure)
    : term_structure  =
  try
    begin
      let c = SMap.find fn ts.function_symbols in
      let cc =  CC.make_constructor ts.cc c in
      {ts with cc = cc}
    end
  with Not_found ->
    begin
      let c,cc = CC.fresh ts.cc in
      let cc =  CC.make_constructor cc c in
      {ts with cc = cc; function_symbols = SMap.add fn c ts.function_symbols}
    end

(* could we use rep_not_used_in? *)
let is_pvar_free ts c =
  let is_pvar v = VarMap.mem v ts.pvars in
  let get_arg h = CMap.find h ts.originals in
  let forall_handles p hs = List.for_all p (List.map get_arg hs) in 
  let rec ok_arg = function
  | FArg_var v -> not (is_pvar v)
  | FArg_string _ -> true
  | FArg_op (_, hs) -> forall_handles ok_arg hs
  | FArg_cons (_, hs) -> forall_handles ok_arg hs
  | FArg_record shs -> List.for_all (fun (_,h) -> ok_arg (get_arg h)) shs in
  ok_arg (get_arg c)

let get_equals_pvar_free ts pvar =
  try
    let pvar_c = VarMap.find pvar ts.pvars in
    let equal_cs = CC.others ts.cc pvar_c in
    let pvar_free_equals = List.filter (is_pvar_free ts) equal_cs in
    List.map (reconstruct ts) pvar_free_equals
  with Not_found -> []

let get_pvars ts =
  VarMap.fold (fun k _ ks -> k :: ks) ts.pvars []
