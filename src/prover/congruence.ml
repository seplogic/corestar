(********************************************************
   This file is part of coreStar
        src/prover/congruence.ml
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

(* TODO(rgrig): don't open these *)
open Backtrack
open Misc
open Printing
open Psyntax

module PA = Persistentarray

(*  Implementation of paper:
    Fast congruence closure and extensions
    R. Nieuwenhuis, A. Oliveras / Information and Computation 205 (2007) 557–580

   Using persisent arrays from
      Union Find algorithm
*)

let cc_debug = ref false


module type PCC =
    sig
      type t
      type constant

      type term =
	| TConstant of constant
	| Func of constant * term list

      type curry_term =
	Constant of constant
      | App of curry_term * curry_term


      type pattern =
	Hole of constant
      |	PConstant of constant
      |	PFunc of constant * pattern list

      (* New blank ts *)
      val create : unit -> t

      val size : t -> int

      (* Add a term to the structure *)
      val add_term : t -> term -> (constant * t)

      (* Add application to the structure *)
      val add_app : t -> constant -> constant -> (constant * t)

      (* Get a fresh representative *)
      val fresh : t -> (constant * t)
      (* Get a fresh representative, that can be unified *)
      val fresh_unifiable : t -> (constant * t)
      val fresh_exists : t -> (constant * t)
      val fresh_unifiable_exists : t -> (constant * t)

      (* [merge_cc subst cc1 cc2] applies [subst] to [cc1] and merges the result
      into [cc2]. NOTE: [cc2] is supposed to already know about all the
      constants in the image of [subst] *)
      val merge_cc : (constant -> bool * constant) -> t -> t -> t

      (* make_equal will raise a Contradiction if making the this equality invalidates a inequality *)
      val make_equal : t -> constant -> constant -> t

      val rep_eq : t -> constant -> constant -> bool
      val rep_uneq : t -> constant -> constant -> bool

      (*  Used for abstraction to deal with whether variables
	 are still live. *)
      val rep_not_used_in : t -> constant -> constant list -> bool

      val rep_self_cons : t -> constant -> bool	

      (* make_not_equal will raise a Contradiction if making this inequality invalidates an equality *)
      val make_not_equal : t -> constant -> constant -> t

      (* make_constructor will make the supplied constant treated constructorly, that is
            * different from any other constructor constant
            * When used on the left of an application the application will be considered constructor in its right argument
	 For example, if c and d are constructor and distinct then
	   rep_uneq  c d
	 will hold.

  	 The following
	    app(c,e) = app(d, f)
	 requires
	    c=d and f=e
	 If c and d are considerd constructor.

	 If c is constructor, then so is app(c,h) for any h.

	 So we can represent a datatype like lists as Two constructor constants
	    nil
	    cons
	 From above, we automatically know
	    nil != app((app(cons,x),y)
	 and
	    app((app(cons,x),y) = app((app(cons,x2),y2)  <==>  x2=x /\ y=y2
      *)
      val make_constructor : t -> constant -> t

      val normalise : t -> constant -> constant
      val others : t -> constant -> constant list
      val eq_term : t -> curry_term -> curry_term -> bool
      val neq_term : t -> curry_term -> curry_term -> bool

      val unifies : t -> curry_term -> constant -> (t -> 'a) -> 'a
      val unifies_any : t -> curry_term -> (t * constant -> 'a) -> 'a

      (* Unifies two constants, if there is only one possible way to unify them *)
      val determined_exists : t -> (constant list) -> constant -> constant -> t * ((constant * constant) list)

      (*  Make a congruence closure structure that is equivalent in content,
	 but each constant is a representative.
         Also returns a map for the updates to each constant*)
      val compress_full : t -> t*(constant -> constant)

      (* {{{  Debug stuff *)
      val print : t -> unit

      (** Like [pretty_print'], but uses * as separator (so that
       * arguments [pp_sep] and [first] are mising). *)
      val pretty_print :
        (constant -> bool) ->
        (formatter -> constant -> unit) -> formatter -> t -> unit

      (** [pretty_print' has_pp pp_c pp_sep ppf first cc] prints to [ppf]
       * the information in the congruence closure [cc]. Constants involved
       * in equalities/inequalities are printed using [pp_c], but only when
       * [has_pp] says that both constants can be handled by [pp_c], otherwise
       * that particular equality/inequality is omitted. The function [pp_sep]
       * is used to print separators. The module [Printing] explains how
       * [first] is used and what the result means. *)
      val pretty_print' :
        (constant -> bool) ->
        (formatter -> constant -> unit) ->
        sep_wrapper ->
        formatter ->
        bool ->
        t ->
        bool

      val pp_c : t -> (formatter -> constant -> unit) -> (formatter -> constant -> unit)

      val get_eqs : (constant -> bool) -> (constant -> 'a) -> t -> ('a * 'a) list
      val get_neqs : (constant -> bool) -> (constant -> 'a) -> t -> ('a * 'a) list

      val get_consts : t -> constant list
      val get_reps : (constant -> bool) -> (constant -> 'a) -> t -> 'a list
      val get_self_constructors : t -> constant list

      (* surjective mapping from constants to integers *)
      val const_int : constant -> t -> int

      val test : unit -> unit

      val delete : t -> constant -> t

      (* Forget eqs and neqs *)
      val forget_qs : t -> t

      val invariant : t -> bool
      (* }}} *)
    end

module CC : PCC =
  struct

    type constant = int

    type term =
      | TConstant of constant
      | Func of constant * term list

    type curry_term =
	Constant of constant
      | App of curry_term * curry_term

    type inj_term =
	Not
      |	Self
      |	IApp of constant * constant

    type pattern =
	Hole of constant
      |	PConstant of constant
      |	PFunc of constant * pattern list

    let rec curry (t : term)
	=
      match t with
	TConstant c -> Constant c
      | Func (c,tl) -> List.fold_left (fun ct t -> App (ct,(curry t))) (Constant c) tl

    type complex_eq = (* a *)constant * (* b *)constant * (* c *)constant  (* app(a,b) = c *)

    type flat_eq =
      |  Complex of complex_eq

    type use =
	Complex_eq of complex_eq
      |	Not_equal of constant


    module CCMap = Map.Make(
      struct
	type t = constant * constant
	let compare = compare
      end
	)


    type var_type =
      |	Unifiable
      |	Exists
      |	UnifiableExists
      |	Standard
      |	Deleted

(*
   UseList  :  constant ->  use list
   Representative : constant -> constant
   Class List : constant -> constant list
   Lookup : constant -> constant -> complex_eq option
 *)

    module Auselist = PA.Make (struct type elt = use list let create _ = [] end)
    module Arepresentative = PA.Make (struct type elt = constant let create i = i end)
    module Aclasslist = PA.Make (struct type elt = int list let create i = [i] end)
    module Arev_lookup = PA.Make (struct type elt = ((constant * constant) list) let create _ = [] end)
    module Aconstructor = PA.Make (struct type elt = inj_term let create _ = Not end)
    module Aunifiable = PA.Make (struct type elt = var_type let create _ = Standard end)

(* Intuitively:

  representative - mapping from constant to represntative constant.

  classlist - mapping from represenative constants to the class of represented.

*)
    type t =
	{ uselist : Auselist.t;
	  representative : Arepresentative.t;
	  classlist : Aclasslist.t;
          lookup : complex_eq CCMap.t; (* TODO: change to [constant CCMap.t]. *)
	  rev_lookup : Arev_lookup.t;
	  not_equal : unit CCMap.t;
	  constructor : Aconstructor.t;
	  unifiable : Aunifiable.t;
	}

    let create () =
      {
       uselist = Auselist.create ();
       representative = Arepresentative.create ();
       classlist = Aclasslist.create ();
       lookup = CCMap.empty;
       rev_lookup = Arev_lookup.create ();
       not_equal = CCMap.empty;
       constructor = Aconstructor.create ();
       unifiable = Aunifiable.create ();
     }

    let size cc = Auselist.size cc.uselist

    let get_uselist cc = Auselist.get cc.uselist
    let set_uselist cc i v = { cc with uselist = Auselist.set cc.uselist i v }
    let reset_uselist cc i = { cc with uselist = Auselist.reset cc.uselist i }
    let get_representative cc = Arepresentative.get cc.representative
    let set_representative cc i v = { cc with representative = Arepresentative.set cc.representative i v }
    let get_classlist cc = Aclasslist.get cc.classlist
    let set_classlist cc i v = { cc with classlist = Aclasslist.set cc.classlist i v }
    let reset_classlist cc i = { cc with classlist = Aclasslist.reset cc.classlist i }
    let get_rev_lookup cc = Arev_lookup.get cc.rev_lookup
    let set_rev_lookup cc i v = { cc with rev_lookup = Arev_lookup.set cc.rev_lookup i v }
    let reset_rev_lookup cc i = { cc with rev_lookup = Arev_lookup.reset cc.rev_lookup i }
    let get_constructor cc = Aconstructor.get cc.constructor
    let set_constructor cc i v = { cc with constructor = Aconstructor.set cc.constructor i v }
    let reset_constructor cc i = { cc with constructor = Aconstructor.reset cc.constructor i }
    let get_unifiable cc = Aunifiable.get cc.unifiable
    let set_unifiable cc i v = { cc with unifiable = Aunifiable.set cc.unifiable i v }
    let reset_unifiable cc i = { cc with unifiable = Aunifiable.reset cc.unifiable i }

    (* deprecate *)
    let rep = get_representative
    let set_rep = set_representative

    let rep_eq (ts : t) (c : constant) (c2 : constant) : bool =
      rep ts c = rep ts c2

    let rec rep_uneq (ts : t) (c : constant) (c2 : constant) : bool =
      let c = rep ts c in
      let c2 = rep ts c2 in
      if c <> c2 then
	match Aconstructor.get ts.constructor c, Aconstructor.get ts.constructor c2 with
	  Not, _
	| _, Not  (* At least one rep is not constructor, check if we have explicit neq.*)
	| IApp _,IApp _  (* Don't recurse, just do simple test here, later redefine to find contradictions *)
	  ->
	  let (c,c2) = if c < c2 then (c,c2) else (c2,c) in
	  CCMap.mem (c,c2) ts.not_equal
	| Self, _
	| _, Self ->
	    (* Self,Self or Self,IApp are not equal *)
	    true
      else
	(* Same rep, therefore not not equal. *)
	false

    let lookup ts (a,b) =
      try
	Some (CCMap.find ((rep ts a),(rep ts b)) ts.lookup )
      with Not_found -> None

    let invariant (ts : t) : bool = not safe || begin
      let n = size ts - 1 in
      (* Check reps have class list *)
      for i = 0 to n do
	let r = Arepresentative.get ts.representative i in
	let cl = Aclasslist.get ts.classlist r in
        if not (List.exists ((=) i) cl) then begin
          eprintf "@[<2>INTERNAL: bad union-find, see %d@\nrep:" i;
          for i = 0 to n do eprintf "@ %d" (get_representative ts i) done;
          eprintf "@\ncls: ";
          for i = 0 to n do
            eprintf "@ [%d: %a]" i (pp_list_sep " " pp_int) (get_classlist ts i)
          done;
          eprintf "@\n@]@?";
          assert false
        end;
	assert (List.exists ((=) i) cl)
      done;
      (* check class list has reps *)
      for i = 0 to n do
	let cl = Aclasslist.get ts.classlist i in
	assert (List.for_all (fun c -> get_representative ts c = i) cl)
      done;
      (* check lookup has appropriate rev_lookup and uses *)
      CCMap.iter
	(fun (a,b) (c,d,e) ->
	  let rl = Arev_lookup.get ts.rev_lookup (get_representative ts e) in
	  assert (rep_eq ts a c);
	  assert (rep_eq ts b d);
	  (* Check reverse map exists *)
	  assert (List.exists (fun (r1,r2) -> rep_eq ts a r1 && rep_eq ts b r2) rl);
	  (* Check there exists a use for "a" *)
	  let ula = Auselist.get ts.uselist (rep ts a) in
	  assert (List.exists
		    (function
			Complex_eq (r1,r2,r3) ->
			  rep_eq ts r3 e &&
			  rep_eq ts r1 a &&
			  rep_eq ts r2 b
		      |	 _ -> false)
		     ula);
	  let ulb = Auselist.get ts.uselist (rep ts b) in
	  assert (List.exists
		    (function
			Complex_eq (r1,r2,r3) ->
			  rep_eq ts r3 e &&
			  rep_eq ts r1 a &&
			  rep_eq ts r2 b
		      |	 _ -> false)
		     ulb);

	  ) ts.lookup;
      (* check rev_lookup has appropriate lookup *)
      for cc = 0 to n do
	let rs = Arev_lookup.get ts.rev_lookup cc in
        let check_pair (aa, bb) = match lookup ts (aa, bb) with
	  | Some (a,b,c) ->
              assert (rep_eq ts cc c && rep_eq ts aa a && rep_eq ts bb b)
	  | None -> assert false in
	List.iter check_pair rs
      done;
      true
    end

    let sort_pair ((a, b) as p) =
      if a <= b then p else (b, a)

    (*
    Asserts the following, in this order:
      - All constants appearing within fields of [cc] with the exception of
        [classlist] are class representants. A constant [c] is a class
        representant when [representatives[c]=c]. In particular, this implies
        that [representatives] is idempotent.
      - The entries of [classlist] that correspond to constants that are not
        representatives have value empty list.
      - The entries of [unifiable], [constructor] that correspond to constants
        that are not representatives have default values.
      - All lists are actually representing sets, so they must have no repeats.
        In addition, they are strictly increasing.
      - Pairs in [not_equal] are strictly increasing.
      - The [uselist] contains exactly the aparitions in [lookup] and
        [not_equal].
      - The [rev_lookup] is the reverse of [lookup].
      - The [classlist] is the reverse of [representatives].
      - Constructors are distinct, injective and disjoint even when curried.
        - If constructor[c]<>IApp(_,_) and (a,b)∊rev_lookup[c],
          then constructor[a]=Not.
        - If constructor[c]=IApp(d,e) and (a,b)∊rev_lookup[c],
          then constructor[d]<>Not, and (a,b)=(d,e) or constructor[a]=Not.
        - If constructor[c]=IApp(d,e) then (d,e)∊rev_lookup[c].
        - If constructor[f]=Self, constructor[g]<>Not, and f<>g,
          then (f,g)∊not_equal.
          (NOTE: representative[f]=f and representative[g]=g)
          (NOTE: It is inefficient to maintain this part of the invariant with
          the current data structure. Fixing it is TODO.)
      - Closure under propagation of disequalities:
        - If {f(a)=c, f(b)=d}∊lookup and (c,d)∊not_equal,
          then (a,b)∊not_equal
        - If (a, b)∊not_equal, f constructor, and {f(a)=c, f(b)=d}⊆lookup,
          then (c, d)∊not_equal.

    NOTE: The checks above imply closure under propagation of equalities:
      - (a=b --> f(a)=f(b)) because there are only reps in [lookup]
      - (f cons --> f(a)=f(b) --> a=b)
        because [rev_lookup] doesn't repeat constructors
    NOTE: The checks above also imply that no two constants are known to be
      both equal and not equal, because pairs of [not_equal] are strictly
      increasing, and contain only representatives.
    *)
    let strict_invariant cc =
      let n = size cc in
      let reps = HashSet.create 0 in
      for c = 0 to n - 1 do
        if get_representative cc c = c then HashSet.add reps c
      done;
      let chk_rep c = assert (HashSet.mem reps c) in
      let chk_rep2 (a, b) = chk_rep a; chk_rep b in
      let chk_rep3 (a, b, c) = chk_rep a; chk_rep b; chk_rep c in
      let chk_use_rep = function
        | Complex_eq (a, b, c) -> chk_rep3 (a, b, c)
        | Not_equal c -> chk_rep c in
      let chk_lkp_rep ((a, b) as p) ((c, d, _) as t) =
        chk_rep2 p; chk_rep3 t;
        assert (a = c);
        assert (b = d) in
      let chk_cons_rep = function IApp (a, b) -> chk_rep2 (a, b) | _ -> () in
      let chk_neq_rep neq () = chk_rep2 neq in
      for c = 0 to n - 1 do begin
        List.iter chk_use_rep (get_uselist cc c);
        chk_rep (get_representative cc c);
        List.iter chk_rep2 (get_rev_lookup cc c);
        chk_cons_rep (get_constructor cc c);
      end done;
      CCMap.iter chk_lkp_rep cc.lookup;
      CCMap.iter chk_neq_rep cc.not_equal;

      for c = 0 to n - 1 do
        if not (HashSet.mem reps c) then begin
          assert (get_classlist cc c = []);
          assert (get_constructor cc c = Not);
          assert (get_unifiable cc c = Standard)
        end
      done;

      let chk_set xs = assert (xs = Misc.remove_duplicates compare xs) in
      for c = 0 to n - 1 do begin
        chk_set (get_uselist cc c);
        chk_set (get_classlist cc c);
        chk_set (get_rev_lookup cc c);
      end done;

      CCMap.iter (fun (a, b) () -> assert (a < b)) cc.not_equal;

      let use_cnt = ref 0 in
      let chk_use_eq a (c, d, e) =
        assert (List.mem (Complex_eq (c, d, e)) (get_uselist cc a)) in
      let chk_use_neq a u = assert (List.mem u (get_uselist cc a)) in
      let record_eq (a, b) cde =
        incr use_cnt; chk_use_eq a cde;
        if b <> a then (incr use_cnt; chk_use_eq b cde) in
      let record_neq (a, b) () =
        incr use_cnt; chk_use_neq a (Not_equal b);
        incr use_cnt; chk_use_neq b (Not_equal a) in
      CCMap.iter record_eq cc.lookup;
      CCMap.iter record_neq cc.not_equal;
      for c = 0 to n - 1 do
        use_cnt := !use_cnt - List.length (get_uselist cc c)
      done;
      assert (!use_cnt = 0);

      let eq_cnt = ref 0 in
      let chk_rev_lkp a b c =
        try assert (CCMap.find (a, b) cc.lookup = (a, b, c))
        with Not_found -> assert false in
      let record_rev_lkp c (a, b) = incr eq_cnt; chk_rev_lkp a b c in
      for c = 0 to n - 1 do
        List.iter (record_rev_lkp c) (get_rev_lookup cc c)
      done;
      assert (!eq_cnt = CCMap.cardinal cc.lookup);

      let rep_cnt = ref 0 in
      let chk_clsrep c b = incr rep_cnt; assert (get_representative cc b = c) in
      for c = 0 to n - 1 do List.iter (chk_clsrep c) (get_classlist cc c) done;
      assert (!rep_cnt = n);

      let chk_rev_lkp_cons cons (a, b) = match cons with
        | IApp (d, e) ->
            assert (get_constructor cc d <> Not);
            assert ((a, b) = (d, e) || get_constructor cc a = Not)
        | _ -> assert (get_constructor cc a = Not) in
      for c = 0 to n - 1 do
        let cons = get_constructor cc c in
        List.iter (chk_rev_lkp_cons cons) (get_rev_lookup cc c);
        match cons with
          | IApp (d, e) -> assert (List.mem (d, e) (get_rev_lookup cc c))
          | _ -> ()
      done;

      for c = 0 to n - 1 do if get_constructor cc c = Self then
        for d = 0 to n - 1 do if get_constructor cc d <> Not then
          assert (c = d || CCMap.mem (sort_pair (c, d)) cc.not_equal)
        done
      done;

      let chk_neq_fixed_fun f =
        let f_is_cons = get_constructor cc f <> Not in
        let get_f_app =
          function Complex_eq (g, a, b) when g = f -> Some (a, b) | _ -> None in
        let xs = map_option get_f_app (get_uselist cc f) in
        let chk_pair (a, c) (b, d) =
          let a_neq_b = CCMap.mem (a, b) cc.not_equal in
          let c_neq_d = CCMap.mem (c, d) cc.not_equal in
          assert (not c_neq_d || a_neq_b);
          assert (not f_is_cons || not a_neq_b || c_neq_d) in
        Misc.iter_all_pairs chk_pair xs in
      HashSet.iter chk_neq_fixed_fun reps;

      assert (invariant cc)
      (* END of [strict_invariant] check *)

    (* TODO(rgrig): Why is this not commutative? *)
    let merge_unify u1 u2 = match u1, u2 with
      | Unifiable, Unifiable -> Unifiable
      | Unifiable, UnifiableExists
      | UnifiableExists, Unifiable
      | UnifiableExists, UnifiableExists -> UnifiableExists
      | _, Unifiable
      | _, UnifiableExists -> Deleted
      | _, a -> a

    (* TODO: Maintain these counts, so that [get_weight] takes O(1) time. *)
    let get_weight cc c =
      List.length (get_uselist cc c)
      + List.length (get_classlist cc c)
      + List.length (get_rev_lookup cc c)

    (* See [work_list] below. *)
    type work_unit =
      | WU_add_eq of constant * constant
      | WU_add_neq of constant * constant
      | WU_mk_cons of constant * constant * constant

    let mk_wu_add_eq (a, b) = WU_add_eq (a, b)
    let mk_wu_add_neq (a, b) = WU_add_neq (a, b)
    let mk_wu_mk_cons (a, b, c) = WU_mk_cons (a, b, c)

    let pairs xs ys =
      List.flatten (List.map (fun y -> List.map (fun x -> (x, y)) xs) ys)

    (* TODO: This must be done faster. Maintain set of self constructors? *)
    let get_all_constructors cc =
      Aconstructor.find_indices ((<>) Not) cc.constructor
    let get_self_constructors cc =
      Aconstructor.find_indices ((=) Self) cc.constructor

    let remove_complex_eq (x, y, z) cc =
      let lookup = CCMap.remove (x, y) cc.lookup in
      let cc = set_rev_lookup cc z
        (List.filter ((<>) (x, y)) (get_rev_lookup cc z)) in (* SLOW *)
      let cc = set_uselist cc x
        (List.filter ((<>) (Complex_eq (x, y, z))) (get_uselist cc x)) in (* SLOW *)
      let cc = set_uselist cc y
        (List.filter ((<>) (Complex_eq (x, y, z))) (get_uselist cc y)) in (* SLOW *)
      { cc with lookup }

    let add_complex_eq (x, y, z) cc =
      try
        let xx, yy, zz = CCMap.find (x, y) cc.lookup in
        assert (xx = x && yy = y);
        ([z, zz], cc)
      with Not_found ->
        let lookup = CCMap.add (x, y) (x, y, z) cc.lookup in
        let cc = set_rev_lookup cc z
          (Misc.insert_sorted (x, y) (get_rev_lookup cc z)) in (* SLOW *)
        let cc = set_uselist cc x
          (Misc.insert_sorted (Complex_eq (x, y, z)) (get_uselist cc x)) in (* SLOW *)
        let cc = set_uselist cc y
          (Misc.insert_sorted (Complex_eq (x, y, z)) (get_uselist cc y)) in (* SLOW *)
        ([], { cc with lookup })

    let add_neq (a, b) cc =
      (* the check below is necessary for termination *)
      let a, b = sort_pair (get_representative cc a, get_representative cc b) in
      if a = b then raise Contradiction;
      if CCMap.mem (a, b) cc.not_equal then ([], cc) else begin
        let not_equal = CCMap.add (a, b) () cc.not_equal in
        let cc = set_uselist cc a
          (Misc.insert_sorted (Not_equal b) (get_uselist cc a)) in
        let cc = set_uselist cc b
          (Misc.insert_sorted (Not_equal a) (get_uselist cc b)) in

        let rec acc_neq get_f get_x neqs xs ys = match xs, ys with
          | [], _ | _, [] -> neqs
          | (x :: xs as xxs), (y :: ys as yys) ->
              let h = min (get_f x) (get_f y) in
              let p z = h = get_f z in
              let xs1, xs2 = ListH.span p xxs in
              let ys1, ys2 = ListH.span p yys in
              let xs1 = List.map get_x xs1 in
              let ys1 = List.map get_x ys1 in
              acc_neq get_f get_x (pairs xs1 ys1 @ neqs) xs2 ys2 in

        (* f(x)!=f(y)  →  x!=y *)
        let acc_neq_fun = acc_neq fst snd in
        let neqs = acc_neq_fun [] (get_rev_lookup cc a) (get_rev_lookup cc b) in

        (* x!=y ∧ f cons  →  f(x)!=f(y) *)
        let acc_neq_cons =
          acc_neq (function (a,_,_)->a) (function (_,_,c)->c) in
        let get_cons_app x =
          let p = function
            | Complex_eq (u, v, w) when v = x && get_constructor cc u <> Not ->
                Some (u, v, w)
            | _ -> None in
          map_option p (get_uselist cc x) in
        let neqs = acc_neq_cons neqs (get_cons_app a) (get_cons_app b) in

        let cc = { cc with not_equal } in
        let ws = List.map mk_wu_add_neq neqs in
        (ws, cc)
      end

    let get_image cc c =
      let f acc = function
        | Complex_eq (x, y, z) when x = c -> (x, y, z) :: acc
        | _ -> acc in
      List.fold_left f [] (get_uselist cc c)

    let mk_cons (a, b, c) cc =
      if safe then begin
        try
          let _, _, d = CCMap.find (a, b) cc.lookup in
          assert (c = d)
        with Not_found -> assert false
      end;
      (match get_constructor cc c with
        | Self -> raise Contradiction
        | IApp (aa, bb) -> ([mk_wu_add_eq (aa, a); mk_wu_add_eq (bb, b)], cc)
        | Not ->
            let f d = mk_wu_add_neq (c, d) in
            let ws = List.map f (get_self_constructors cc) in
            let cc = set_constructor cc c (IApp (a, b)) in
            let ws = List.map mk_wu_mk_cons (get_image cc c) @ ws in
            (ws, cc))

    (* TODO: Turn lists into sets. See SLOW below. *)
    let add_eq (a, b) cc =
      let a, b = get_representative cc a, get_representative cc b in
      if a = b then ([], cc) else begin
        let a, b = if get_weight cc a < get_weight cc b then b, a else a, b in
        (* NOTE: This function should use O(get_weight cc b) time, not counting
        the work done for marking constants as constructors. *)

        (* merge [b] (small) into [a] (big) *)
        let cs = get_classlist cc b in
        let cc = List.fold_left (fun cc c -> set_representative cc c a) cc cs in
        let cc = set_classlist cc a (Misc.merge_lists (get_classlist cc a) cs) in (* SLOW *)
        let cc = set_classlist cc b [] in

        (* merge constructor[a] with constructor[b] *)
        let ws, cons_a = match get_constructor cc a, get_constructor cc b with
          (* NOTE: for reps, once a constructor, always a constructor *)
          | Not, cons | cons, Not -> ([], cons)
          | IApp (x1, y1) as cons, IApp (x2, y2) ->
              ([mk_wu_add_eq (x1, x2); mk_wu_add_eq (y1, y2)], cons)
          | _ -> raise Contradiction in
        let cc = set_constructor cc a cons_a in
        let cc = reset_constructor cc b in

        let sub x = if x = b then a else x in
        let sub3 (x, y, z) = (sub x, sub y, sub z) in

        (* (x y = z)[a/b], and also IApp(x, y)[a/b] *)
        (* assumes constructor[a] is already merged *)
        let iapps_to_update =
          let f acc = function
            | Complex_eq (_, _, z) -> IntSet.add (sub z) acc
            | _ -> acc in
          List.fold_left f IntSet.empty (get_uselist cc b) in
        let bs_eqs =
          let get_eq = function
            | Complex_eq (x, y, z) -> Some (x, y, z)
            | _ -> None in
          let lhs = map_option get_eq (get_uselist cc b) in
          let rhs = List.map (fun (x, y) -> (x, y, b)) (get_rev_lookup cc b) in
          remove_duplicates compare (lhs @ rhs) in
        let cc = List.fold_right remove_complex_eq bs_eqs cc in
        let as_eqs = List.map sub3 bs_eqs in
        let eqs, cc =
          let f c_eq (eqs2, cc) =
            let eqs1, cc = add_complex_eq c_eq cc in (eqs1 @ eqs2, cc) in
          List.fold_right f as_eqs ([], cc) in
        let update_cons c cc = match get_constructor cc c with
          | IApp (x, y) -> set_constructor cc c (IApp (sub x, sub y))
          | _ -> cc in
        let cc = IntSet.fold update_cons iapps_to_update cc in

        (* Ensure not_equal mentions only reps. *)
        let update_neq cc = function
          | Complex_eq (x, y, z)  -> cc
          | Not_equal x ->
              if x = a then raise Contradiction; (* we knew before that a!=b *)
              let not_equal =
                CCMap.remove (sort_pair (b, x)) cc.not_equal in
              let cc = set_uselist cc x
                (List.filter ((<>) (Not_equal b)) (get_uselist cc x)) in
              let not_equal =
                CCMap.add (sort_pair (a, x)) () not_equal in
              let cc = { cc with not_equal } in
              let cc = set_uselist cc a
                (Misc.insert_sorted (Not_equal x) (get_uselist cc a)) in
              let cc = set_uselist cc x
                (Misc.insert_sorted (Not_equal a) (get_uselist cc x)) in
              cc in
        let cc = List.fold_left update_neq cc (get_uselist cc b) in

        let cc = set_unifiable cc a
          (merge_unify (get_unifiable cc a) (get_unifiable cc b)) in
        let cc = reset_unifiable cc b in
        let ws = List.map mk_wu_add_eq eqs @ ws in
        let ws = if get_constructor cc a = Not
          then ws
          else List.map mk_wu_mk_cons (get_image cc a) @ ws in
        (ws, cc)
      end (* of add_eq *)

    let work j cc = match j with
      | WU_add_eq (a, b) -> add_eq (a, b) cc
      | WU_add_neq (a, b) -> add_neq (a, b) cc
      | WU_mk_cons (a, b, c) -> mk_cons (a, b, c) cc

    let rec unsafe_work_list js cc = match js with
      | [] -> cc
      | j :: js -> let is, cc = work j cc in unsafe_work_list (is @ js) cc

    (* Maintains [strict_invariant].  Unfortunately, it seems a bit expensive
    to maintain [strict_invariant] for each work unit. *)
    let work_list js cc =
      if safe then strict_invariant cc;
      let cc = unsafe_work_list js cc in
      if safe then strict_invariant cc;
      cc

    let mk_self cc c =
      if safe then strict_invariant cc;
      let c = get_representative cc c in
      if get_constructor cc c = Self then cc else begin
        assert (get_constructor cc c = Not);
        let cc = set_constructor cc c Self in
        let ds = List.filter ((<>) c) (get_all_constructors cc) in
        let mk_neq d = mk_wu_add_neq (c, d) in
        let ws = List.map mk_neq ds in
        let ws = List.map mk_wu_mk_cons (get_image cc c) @ ws in
        let cc = unsafe_work_list ws cc in
        if safe then strict_invariant cc;
        cc
      end

    let grow n ts =
      { ts with
        uselist = Auselist.grow ts.uselist n
      ; representative = Arepresentative.grow ts.representative n
      ; classlist = Aclasslist.grow ts.classlist n
      ; rev_lookup = Arev_lookup.grow ts.rev_lookup n
      ; constructor = Aconstructor.grow ts.constructor n
      ; unifiable = Aunifiable.grow ts.unifiable n }

    let fresh ts : int * t =
      assert (invariant ts);
      let c = size ts in
      let ts = grow 1 ts in
      assert (invariant ts);
      (c, ts)


    let fresh_unifiable ts : int * t =
      let c,ts = fresh ts in
      let ts = {ts with unifiable = Aunifiable.set ts.unifiable c Unifiable} in
      assert (invariant ts);
      (c, ts)

    let fresh_unifiable_exists ts : int * t =
      let c,ts = fresh ts in
      let ts =
        {ts with unifiable = Aunifiable.set ts.unifiable c UnifiableExists} in
      assert (invariant ts);
      (c, ts)

    let fresh_exists ts : int * t =
      let c,ts = fresh ts in
      let ts = {ts with unifiable = Aunifiable.set ts.unifiable c Exists} in
      assert (invariant ts);
      (c, ts)

    (* POST: does path compresion *)
    let rec get_rep_root cc i =
      let j = get_representative cc i in
      if i = j then (i, cc)
      else begin
        let j, cc = get_rep_root cc j in
        (j, set_representative cc i j)
      end

    (* Establish [strict_invariant].
      - make fresh cc of same size
      - copy *unifiable* information
      - copy over complex equalities:
        iterate thru *lookup* and call add_complex_eq (should not schedule eqs)
      - copy over self constructors:
        iterate *self* cons and (1) set self, (2) mk_cons for all complex_eq
      - copy over equalities:
        iterate thru *represenatives* and call add_eq
      - copy over disequalities:
        iterate thru *not_equal* and call add_neq
    May raise [Contradiction]. *)
    let sanitize cc =
      let n = size cc in
      let sane_cc = grow n (create ()) in
      if safe then strict_invariant sane_cc;
      let sane_cc = { sane_cc with unifiable = cc.unifiable } in
      if safe then strict_invariant sane_cc;
      let ace _ c_eq acc =
        let eqs, acc = add_complex_eq c_eq acc in
        assert (eqs = []);
        acc in
      let sane_cc = CCMap.fold ace cc.lookup sane_cc in
      if safe then strict_invariant sane_cc;
      let copy_self c cons acc = match cons with
        | Self -> mk_self acc c
        | _ -> acc in
      let sane_cc = Aconstructor.foldi copy_self cc.constructor sane_cc in
      if safe then strict_invariant sane_cc;
      let copy_eq a b = work_list [mk_wu_add_eq (a, b)] in
      let sane_cc = Arepresentative.foldi copy_eq cc.representative sane_cc in
      if safe then strict_invariant sane_cc;
      let copy_neq neq () = work_list [mk_wu_add_neq neq] in
      let sane_cc = CCMap.fold copy_neq cc.not_equal sane_cc in
      if safe then strict_invariant sane_cc;
      sane_cc

    let merge_cc subst cc1 cc2 =
      if safe then assert (invariant cc1 && invariant cc2);
      let n1, n2 = size cc1, size cc2 in
      let cc1, cc2 = ref cc1, ref cc2 in   (* DANGER *)
      let subst =
        let extra = Hashtbl.create 0 in
        fun c1 -> begin
          try (true, Hashtbl.find extra c1)
          with Not_found -> begin
            try subst c1
            with Not_found -> begin
              let c2 = let id, new_cc = fresh !cc2 in cc2 := new_cc; id in
              Hashtbl.add extra c1 c2; (true, c2)
            end
          end
        end in
      let sub = snd @@ subst in
      for i = 0 to n1 - 1 do ignore (sub i) done;
      let ws set cc i v = cc := set !cc i v in
(*       let set_uselist = ws set_uselist in *)
      let set_representative = ws set_representative in
(*       let set_classlist = ws set_classlist in *)
(*       let set_rev_lookup = ws set_rev_lookup in *)
      let set_constructor = ws set_constructor in
      let set_unifiable = ws set_unifiable in
      (* helper for merging arrays *)
      let merge_array f get set =
        for c1 = 0 to n1 - 1 do
          let is_fresh, c2 = subst c1 in
          let v1 = get !cc1 c1 in
          let v2 = if is_fresh then v1 else f v1 (get !cc2 c2) in
          set cc2 c2 v2
        done in
      (* union-find, randomized, with path compression *)
      let rec rep cc c =
        let r = get_representative !cc c in
        if r = c then r else begin
          let r' = rep cc r in
          assert (cc <> cc1 || r = r'); (* shouldn't change cc1 *)
          set_representative cc c r'; r'
        end in
      let union c1 c2 =
        let c1, c2 = if Random.bool () then c1, c2 else c2, c1 in
        set_representative cc2 (rep cc2 c1) (rep cc2 c2) in
      (* add equalities *)
      for i = 0 to n1 - 1 do union (sub i) (sub (rep cc1 i)) done;
      (* update lookup *)
      let app (a1, b1) (_, _, c1) lookup =
        let a2, b2, c2 = sub a1, sub b1, sub c1 in
        try
          let _, _, c2' = CCMap.find (a2, b2) lookup in
	  union c2 c2'; (* XXX *)
(*
          assert (rep cc2 c2 = rep cc2 c2'); (* TODO: OK to *make* them equal? *)
*)
          lookup
        with Not_found -> CCMap.add (a2, b2) (a2, b2, c2) lookup in
      cc2 := { !cc2 with lookup = CCMap.fold app !cc1.lookup !cc2.lookup };
      (* NOTE: reps should not be changed below; e.g., don't call [union] *)
      (* update constructor, unifiable *)
      let merge_cons cons1 cons2 = match cons1, cons2 with
        | Not, Not -> Not
        | Self, Self -> Self
        | IApp (a, b), (IApp (aa, bb) as r) ->
            assert (rep cc2 (sub a) = rep cc2 aa);
            assert (rep cc2 (sub b) = rep cc2 bb);
            r
        (* TODO: Do something sensible here. *)
(*         | _ -> failwith "INTERNAL: Should this raise Contradiction?" in *)
        | _ -> raise Contradiction in
      merge_array merge_cons get_constructor set_constructor;
      merge_array merge_unify get_unifiable set_unifiable;
      sanitize !cc2

    let pp_c ts pp ppf i =
       (*if true then pp ppf i else fprintf ppf "{%a}_%i" pp i i*)
      pp ppf i (*(rep ts i)*)

    let for_each_rep ts (f : constant -> unit) =
      let n = Arepresentative.size ts.representative in
      for i = 0 to n-1 do
	if Arepresentative.get ts.representative i = i then
	  f i
      done

    let get_eqs mask map ts =
      let acc = ref [] in
      for_each_rep ts
	(fun rep  ->
          if mask rep then
	  let rp = map rep in
	  List.iter
	    (fun i -> if mask i && rep <> i then acc := (rp,map i)::!acc)
	    (Aclasslist.get ts.classlist rep)
	  ) ;
      !acc

    let get_neqs mask map ts =
      let r = Hashtbl.create 13 in (* to take care of duplicates *)
      CCMap.iter
        (fun (a,b) () ->
          let a = rep ts a in
          let b = rep ts b in
          if mask a && mask b then
          Hashtbl.add r (map (min a b), map (max a b)) ())
        ts.not_equal;
      Hashtbl.fold (fun x _ xs -> x::xs) r []

    let pretty_print' has_pp pp_term pp ppf first ts =
      let eqs = get_eqs has_pp (fun x->x) ts in
      let neqs = get_neqs (fun _ -> true) (fun x->x) ts in
      let first =
        List.fold_left (pp.separator (pp_eq pp_term) ppf) first eqs in
      List.fold_left (pp.separator (pp_neq pp_term) ppf) first neqs

    let pretty_print has_pp pp_term =
      pp_whole (pretty_print' has_pp pp_term) pp_star

    let print (ts:t) : unit =
      let rs = ts.representative in
      let n = Arepresentative.size rs - 1 in
      printf "Rep (%d)\n   " n;
      for i = 0 to n do
	if i <> (Arepresentative.get rs i) then
	  printf "%n|->%n  " i (Arepresentative.get rs i)
      done ;

(*
      printf "\nUses";
      for i = 0 to n do
	if (A.get (ts.uselist) i) <> [] then
	  begin
	    printf "\n%n  |-> " i;
	    List.iter
	      (function
		  Complex_eq (a,b,c) ->
		    printf "app(%n,%n)=%n   " a b c
		| Not_equal a ->
		    printf "%n != %n   " i a
		    )
	      (A.get (ts.uselist) i)
	  end
      done;
*)
(*
      printf "\nClass list\n";
      for i = 0 to n do
	if (A.get (ts.classlist) i) <> [i] then
	  begin
	    printf "%n |->  " i;
	    List.iter
	      (fun c -> printf "%n " c)
	      (A.get (ts.classlist) i);
	    printf ";\n"
	  end
      done;
*)
      printf "\nNot equal\n";
      CCMap.iter  (fun (a,b) () -> printf "  %n!=%n;\n" a b) ts.not_equal;

      printf "\nLookup\n";
      CCMap.iter  (fun (a,b) (x,y,z) -> printf "  app(%n,%n) |-> (%n,%n,%n);\n" a b x y z) ts.lookup;

      printf "\nRev lookup";
      for i = 0 to n do
	if (Arev_lookup.get ts.rev_lookup i) <> [] then
	  begin
	    printf "\n %n" i;
	    List.iter
	      (fun (a,b) ->
		printf " = app(%n,%n)" a b )
	      (Arev_lookup.get ts.rev_lookup i)
	  end
      done;

      printf "Injective info:\n";
      for i = 0 to n do
	match Aconstructor.get ts.constructor i with
	  Not -> ()
	| Self -> printf "  inj(%i)\n" i
	| IApp(a,b) -> printf "  inj(%i) by app(%i,%i)\n" i a b
      done;
      printf "\n\n"


    let add_lookup ts (a,b,c) =
      { ts with
	lookup = CCMap.add ((rep ts a),(rep ts b)) (a,b,c) ts.lookup
      ; rev_lookup =
          Arev_lookup.set
            ts.rev_lookup
            (rep ts c)
            ((a,b)::Arev_lookup.get ts.rev_lookup (rep ts c)) }

    let add_use ts a fe : t =
      let a = rep ts a in
      let oldul = Auselist.get ts.uselist a in
      {ts with uselist = Auselist.set ts.uselist a (fe::oldul)}

    let clear_uselist ts r =
	{ts with uselist = Auselist.set ts.uselist r [] }

    let append_cl cc c cs =
      set_classlist cc c (cs @ get_classlist cc c)

    let make_not_equal (ts : t) (a : constant) (b : constant) : t =
      let a,b = rep ts a, rep ts b in
      if a=b then raise Contradiction;
      let (a,b) = if a<b then (a,b) else (b,a) in
      let ula = get_uselist ts a in
      let ulb = get_uselist ts b in
      let ula = if List.exists (fun a -> a=(Not_equal b)) ula then ula else (Not_equal b)::ula in
      let ulb = if List.exists (fun b -> b=(Not_equal a)) ulb then ulb else (Not_equal a)::ulb in
      {ts with
	not_equal = CCMap.add (a,b) () ts.not_equal;
	uselist = Auselist.set (Auselist.set ts.uselist a ula) b ulb}


    let rec make_use_constructor d (ts,pending) use =
      match use with
         (* Only deal where it is a use on the left of an application *)
      | Complex_eq (a,b,c) when (rep_eq ts a d) ->
          begin
            let r = rep ts c in
            match Aconstructor.get ts.constructor r with
          (* Can't make it an IApp, is already an constructor *)
              Self -> raise Contradiction
          (* Can make it an constructor *)
            | Not -> make_uses_constructor r ({ts with constructor = Aconstructor.set ts.constructor r (IApp(a,b))},pending)
          (* Already constructor, okay assuming we can make subterms equal *)
            | IApp(r1,r2) -> ts, (a,r1)::(b,r2)::pending
          end
      | _ ->
          (ts,pending)
    and make_uses_constructor d (cc, pending) =
      List.fold_left (make_use_constructor d) (cc, pending) (get_uselist cc d)

    (* merges the constructor details,
       and potentially returns a list of equalities to make,
       b should be the new representive that is the target of the merge.
    *)
    let constructor_merge ts a b pending : t * ((constant * constant) list) =
    (* Should only call this with something that is an App *)
      match Aconstructor.get ts.constructor a , Aconstructor.get ts.constructor b with
	Not, Not -> ts, pending
      |	Not, i -> make_uses_constructor a (ts,pending)
      |	i, Not ->
	  let (ts,pending) = make_uses_constructor b (ts,pending) in
	  {ts with constructor = Aconstructor.set ts.constructor b i}, pending
      |	IApp(a,b), IApp(c,d) ->
	  ts, (a,c)::(b,d)::pending
      |	_,_ ->
	  (* Other options are a contradiction
	     and should have already been removed *)
	  assert false

    let no_live ts nr =
	List.for_all
	  (fun x -> match (Aunifiable.get ts.unifiable x) with Standard -> false | _ -> true)
	  (Aclasslist.get ts.classlist (rep ts nr))


    (* deprecated *)
    let unifiable_merge cc a b =
      let vt = merge_unify (get_unifiable cc a) (get_unifiable cc b) in
      set_unifiable cc b vt

    let rec propagate (ts : t) (pending : (constant * constant) list) : t =
      match pending with
	  [] -> ts
	| (a,b)::pending ->
	    if !cc_debug then
	      begin
		printf "Making %i=%i " a b;
		if pending <> [] then
		  begin
		    printf "with pending ";
		    List.iter (fun (a,b) -> printf "(%i,%i) " a b) pending;
		  end;
		printf " in \n";
		print ts;
	      end;
	    begin
	      if rep_uneq ts a b then
		raise Contradiction
	      else if rep_eq ts a b then
		propagate ts pending
	      else
		let old_repa = rep ts a in
		let repb = rep ts b in
		let rl =
                  (Arev_lookup.get ts.rev_lookup old_repa)
                  @ (Arev_lookup.get ts.rev_lookup repb) in
		let ts = {ts with rev_lookup = Arev_lookup.set ts.rev_lookup repb rl} in
		let ts,pending = constructor_merge ts old_repa repb pending in
		let cl = get_classlist ts old_repa in
		let ts = append_cl ts repb cl in
		let ts = List.fold_left (fun ts c -> set_rep ts c repb)  ts cl in
                let ts = set_classlist ts old_repa [] in
		let ts = unifiable_merge ts old_repa repb in
		let ul = get_uselist ts old_repa in
		let (pending,ts) = List.fold_left
		    (fun (pending,ts) ->
		      function
			  Complex_eq (c1,c2,c) ->
			    begin
			      match lookup ts (c1,c2) with
				None ->
				  let ts = add_lookup ts (c1,c2,c) in
				  (pending, add_use ts repb (Complex_eq (c1,c2,c)))
			      | Some (d1,d2,d) ->
				  ((c,d)::pending, ts)
			    end
			| Not_equal c1 ->
			    let ts = make_not_equal ts repb c1 in
			    (pending, ts)
		      )
		    (pending,ts)
		    ul in
		let ts = clear_uselist ts old_repa in
                if safe && !cc_debug then begin
                  printf "@\nresulting in@\n"; print ts;
                  printf "@\n with %d pending@\n" (List.length pending);
                end;
		propagate ts pending
	    end



    let rec rep_not_used_in (ts : t) ( a : constant) (b : constant list) (visited : constant list) : bool =
(*      printf "Looking for %i in @\n" a;
      print ts;
      printf "Entry points:@ ";
      List.iter (printf "%i @ ") b;
      printf "@\n";*)
      if List.mem a visited then
	begin
	  printf "Cycle in ts@\n";
	  print ts;
	  printf "Visited@\n @[";
	  List.iter (printf "%i@ ") visited;
	  printf "@]@\n";
          true
	end
      else if List.mem a b then
	begin
(*	  printf "Foo";*)
	  false
	end
      else
	List.for_all
	  (function
	    | Not_equal _ -> true
	    | Complex_eq (c1,c2,c) ->
		rep_not_used_in ts (rep ts c) b (a::visited)
	) (get_uselist ts a)

    let rep_not_used_in (ts : t) ( a : constant) (b : constant list) : bool =
	  rep_not_used_in ts (rep ts a) (List.map (rep ts) b) []

    let rep_self_cons cc c = get_constructor cc c = Self

    let make_equal (ts : t) (a : constant)  (b : constant) : t =
      assert (invariant ts);
      let ts = propagate ts [(a,b)] in
      assert (invariant ts);
      ts

    let make_constructor (ts : t) (a : constant) : t =
      (*assert (A.get ts.constructor (rep ts a) = Not);*)  (* FIXME: is this needed? *)
      assert (invariant ts);
      let ts = {ts with constructor = Aconstructor.set ts.constructor (rep ts a) Self} in
      let ts,p = make_uses_constructor a (ts,[]) in
      let ts = propagate ts p in
      assert (invariant ts);
      ts

    let merge (ts : t) (fe : flat_eq) : t =
      match fe with
      | Complex (a,b,c) ->
	  begin
	    match lookup ts (a,b) with
	      None ->
		let ts = add_lookup ts (a,b,c) in
		let ts = add_use ts a (Complex_eq (a,b,c)) in
		let ts = add_use ts b (Complex_eq (a,b,c)) in
		(* If a is constructor, then so should c be. *)
		if Aconstructor.get ts.constructor (rep ts a) <> Not then
		  let ts,pending = make_use_constructor a (ts,[]) (Complex_eq (a,b,c)) in
		  propagate ts pending
		else
		  ts
	    | Some (e,f,g) -> propagate ts [(c,g)]
	  end


    let rec normalize (ts  : t) (term1 : curry_term) : curry_term =
      match term1 with
	Constant c -> Constant (rep ts c)
      |	App (terml,termr) ->
	  let terml = normalize ts terml in
	  let termr = normalize ts termr in
	  match terml,termr with
	    Constant c1, Constant c2 ->
	      begin
		match lookup ts (c1,c2) with
		  None -> App (terml,termr)
		| Some (e,f,g) -> Constant (rep ts g)
	      end
	  | _ ->  App(terml,termr)


    let add_app (ts : t) (c1 : constant ) (c2 : constant) : constant * t =
      assert (invariant ts);
      let c, ts = (match lookup ts (c1,c2) with
	None ->
	  let c, ts = fresh ts in
	  let ts = merge ts (Complex (c1,c2,c)) in
	  c, ts
      | Some (e,f,g) -> rep ts g, ts) in
      assert (invariant ts);
      (c, ts)


    let rec add_curry_term (ts  : t) (term1 : curry_term) : constant * t  =
      match term1 with
	Constant c -> rep ts c, ts
      |	App (terml,termr) ->
	  let c1,ts = add_curry_term ts terml in
	  let c2,ts = add_curry_term ts termr in
	  add_app ts c1 c2

    let add_term (ts:t) (term : term) : constant * t =
      let c,ts = add_curry_term ts (curry term) in
      assert (invariant ts);
      c,ts


    let compress ts cs : (t * (constant -> constant)) =
      let n = Auselist.size ts.uselist in
	   (* The set of currently visible constants *)
      let set = Array.init n (fun _ -> false) in
	   (* The mapping from old constant to new *)
      let map = Array.init n (fun _ -> 0) in
	   (* The inverse mapping from new constant to old *)
      let inv = Array.init n (fun _ -> 0) in
	   (* index of next constant to map to *)
      let i = ref 0 in
	   (* creates mapping for the next constant *)
      let add_map x =
	let r = rep ts x in
	if Array.get set r then () else
	begin
          Array.set set r true ;
	  Array.set map r !i;
	  Array.set inv !i r;
	  i := !i + 1;
	end in
	   (* Check if considered live *)
      let live r = Array.get set (rep ts r) in
	   (* Get new representative for constant *)
      let newrep r = Array.get map (rep ts r) in
	   (* Add mapping for all the externally live constants *)
      List.iter add_map cs;
      let j = ref 0 in
	   (* For each live constant add sub terms that are live *)
	   (*  Using while rule as !i could be increased
	      by body of loop *)
      while (!j < !i) do
	let ul =  Auselist.get ts.uselist (Array.get inv !j) in
	List.iter
	  (function
	      Complex_eq (e,f,g) ->
		if live e && live f then add_map g
	    | Not_equal _ -> ())
	  ul;
	j := !j + 1
      done;
	   (* Now we should have a mapping for all live constants,
	      build compressed version. *)
      let look = ref CCMap.empty in
      let neq = ref CCMap.empty in
      let reps = Array.init !i (fun i -> i) in
      let clas = Array.init !i (fun i -> [i]) in
      let constructor = Array.init !i
	  (fun i ->
	    match Aconstructor.get ts.constructor (Array.get inv i) with
	      Not -> Not
	    | Self -> Self
	    | IApp (a,b) -> IApp (newrep a, newrep b)
	      ) in
      let unifiable = Array.init !i
	  (fun i -> (Aunifiable.get ts.unifiable (Array.get inv i))) in
(* Build new reverse lookup map *)
      let revl = Array.init !i
	  (fun i ->
	    remove_duplicates compare
	      (map_option
		 (fun (a,b) ->
		   if live  a && live b then
		     Some (newrep a, newrep b)
		   else
		     None
		       ) (Arev_lookup.get ts.rev_lookup (Array.get inv i)))) in
(* Create new uselist *)
      let usel = Array.init !i
	  (fun i ->
	    let oi = Array.get inv i in
	    let ul = map_option
		(function
		    Complex_eq(e,f,g) ->
		      if live e && live f then
			begin
			  if newrep e = i then
			    look := CCMap.add (newrep e, newrep f) (newrep e, newrep f, newrep g) !look;
			  Some (Complex_eq(newrep e,newrep f, newrep g))
			end
		      else
			None
		  | Not_equal(a) ->
		      if live a then
			begin
			  if newrep a < i then
			    neq := CCMap.add (a,i) () !neq;
			  Some (Not_equal(newrep a))
			end
		      else None
			  )
		(get_uselist ts oi) in
	    remove_duplicates compare ul) in
      let ts= {
	uselist = Auselist.unsafe_create usel;
	representative = Arepresentative.unsafe_create reps;
	classlist = Aclasslist.unsafe_create clas;
	lookup = !look;
	rev_lookup = Arev_lookup.unsafe_create revl;
	not_equal = !neq;
	constructor = Aconstructor.unsafe_create constructor;
	unifiable = Aunifiable.unsafe_create unifiable;
      } in
      assert (invariant ts);
      (ts, Array.get map)

    let compress_full ts =
      let cs = ref [] in
      for_each_rep ts
	(fun i -> cs := i::!cs);
      compress ts !cs

    let test debug =
      let print_constant ts c =
	printf "Constant %n has rep %n\n" c (rep ts c) in
      let nth r1 r2 n =
	let rec f n =
	  match n with
	    0 -> TConstant r2
	  | n -> Func (r1, [f (n-1)])  in
	f n in
      let ts = create () in
      let r1,ts = fresh ts in
      let r2,ts = fresh ts in
      let t0 = nth r1 r2 0 in
      let t1 = nth r1 r2 1 in
      let t2 = nth r1 r2 2 in
      let t3 = nth r1 r2 3 in
      let t4 = nth r1 r2 4 in
      let c1,ts = add_term ts t1 in
      let c0,ts = add_term ts t0 in
      let c2,ts = add_term ts t2 in
      let c3,ts = add_term ts t3 in
      let c4,ts = add_term ts t4 in
      let _ =
	let ts = make_equal ts c0 c2 in
	let ts = make_equal ts c1 c4 in
	if rep_eq ts c1 c2 && rep_eq ts c0 c1 && rep_eq ts c1 c2 && rep_eq ts c2 c3 && rep_eq ts c3 c4
	then printf "Correct Test 1.\n"
	else
	  begin
	    printf "Test 1 fails!";
	    print_constant ts c1;
	    print_constant ts c2;
	    print_constant ts c3;
	    print_constant ts c4;
	    print ts
	  end in
      let _ =
	 if rep_eq ts c1 c2 || rep_eq ts c0 c1 || rep_eq ts c1 c2 || rep_eq ts c2 c3 || rep_eq ts c3 c4
	 then
	   begin
	     printf "Test 2 fails!";
	     print_constant ts c1;
	     print_constant ts c2;
	     print_constant ts c3;
	     print_constant ts c4;
	     print ts
	   end
	 else
	   printf "Correct Test 2.\n" in
       let _ =
	 let ts = make_equal ts c0 c1 in
	 if rep_eq ts c1 c2 && rep_eq ts c0 c1 && rep_eq ts c1 c2 && rep_eq ts c2 c3 && rep_eq ts c3 c4 (* RLP: why rep_eq c1 c2 twice? *)
	 then printf "Correct Test 3.\n"
	 else
	   begin
	     printf "Test 3 fails!";
	     print_constant ts c1;
	     print_constant ts c2;
	     print_constant ts c3;
	     print_constant ts c4;
	     print ts
	   end;
       in
       let _ =
	 let ts = make_equal ts c0 c2 in
	 if rep_eq ts c1 c3 && rep_eq ts c2 c4 &&
	   (not (rep_eq ts c1 c2)) && (not (rep_eq ts c2 c3)) && (not (rep_eq ts c3 c4)) (* RLP: why not also test c0=c2? *)
	 then printf "Correct Test 4. \n"
	 else
	   begin
	     printf "Test 4 fails!";
	     print_constant ts c1;
	     print_constant ts c2;
	     print_constant ts c3;
	     print_constant ts c4;
	     print ts
	   end in
       let _ =
	 try
	   let ts = make_not_equal ts c0 c2 in
	   let ts = make_equal ts c0 c1 in
	   begin
	     printf "Test 5 fails!";
	     print_constant ts c1;
	     print_constant ts c2;
	     print_constant ts c3;
	     print_constant ts c4;
	     print ts
	   end
	 with Contradiction ->
	   printf "Correct Test 5. \n"
       in
       let _ =
	 try
	   let ts = make_not_equal ts c0 c1 in
	   let _ = make_equal ts c0 c2 in
	   printf "Correct Test 6. \n"
	 with Contradiction ->
	   begin
	     printf "Test 6 fails!";
	   end
       in
(* This test is hard to automatically check.  Approximate by checking a size *)
       let _ =
	 try
	   let ts = make_equal ts c0 c2 in
	   let ts2,map = compress ts [r1;r2] in
	   if Arepresentative.size ts2.representative = 3
	   then printf "Correct Test 7 a\n"
	   else
	     begin
	       printf "Failed Test 7 a\n";
	       print ts2
	     end;
	   let ts2 = make_not_equal ts c0 c1 in
	   let ts2,map = compress ts2 [r1;r2] in
	   if Arepresentative.size ts2.representative = 3
	   then printf "Correct Test 7 b\n"
	   else
	     begin
	       printf "Failed Test 7 b\n";
	       print ts2
	     end;
	   let ts2 = make_equal ts c0 c1 in
	   let ts2,map = compress ts2 [r1;r2] in
	   if Arepresentative.size ts2.representative = 2
	   then printf "Correct Test 7 c\n"
	   else
	     begin
	       printf "Failed Test 7 c\n";
	       print ts2
	     end
	 with Contradiction ->
	   begin
	     printf "Test 7 fails!\n";
	   end
       in
       let _ =
	 let cons,ts = fresh (create ()) in
	 let nil,ts = fresh ts in
	 let x1,ts = fresh ts in
	 let x2,ts = fresh ts in
	 let y1,ts = fresh ts in
	 let y2,ts = fresh ts in
	 let ts = make_constructor ts cons in
	 let ts = make_constructor ts nil in
	 let tnil,ts = add_term ts (Func(nil,[])) in
	 let tcons1, ts = add_term ts (Func(nil, [TConstant x1;TConstant x2])) in
	 let tcons2, ts = add_term ts (Func(nil, [TConstant y1;TConstant y2])) in
	 let tcons3, ts = add_term ts (Func(nil, [TConstant y1;TConstant x2])) in
	 begin
	   (* Test 8 *)
	   if rep_uneq ts tcons1 tnil then
	     printf "Test 8 Passed!\n"
	   else
	     begin
	       printf "Test 8 Failed!\n";
	       print ts;
	     end
	       ;
	   (* Test 9 *)
	   let ts2 = make_equal ts tcons1 tcons2 in
	   if rep_eq ts2 x1 y1 then
	     printf "Test 9a Passed!\n"
	   else
	     printf "Test 9a Failed!\n";
	   if rep_eq ts2 x2 y2 then
	     printf "Test 9b Passed!\n"
	   else
	     begin
	       printf "Test 9b Failed!\n Assuming %i=%i, could not prove %i=%i\n" tcons1 tcons2 x2 y2;
	       print ts2;
	       let ts,m= compress_full ts2 in
	       print ts
	     end;
	   if rep_eq ts2 x1 x2 then
	     printf "Test 9c Failed!\n"
	   else
	     printf "Test 9c Passed!\n";
	   if rep_eq ts2 y1 y2 then
	     printf "Test 9d Failed!\n"
	   else
	     printf "Test 9d Passed!\n"
	       ;
	   let ts3 = make_equal ts tcons3 tcons1 in
	   let ts3 = make_equal ts3 tcons2 tcons1 in
	   if rep_eq ts3 y1 x1 then
	     printf "Test 10a Passed!\n"
	   else
	     printf "Test 10a Failed!\n"
	 end
       in

       (* test propagation of disequalities *)
       (* If f(a)=c, f(b)=d and c!=d then a!=b *)
       let _ =
	 let a,ts = fresh (create ()) in
	 let b,ts = fresh ts in
	 let f,ts = fresh ts in
	 let c,ts = add_term ts (Func(f,[TConstant a])) in
	 let d,ts = add_term ts (Func(f,[TConstant b])) in

	 let ts = make_constructor ts c in
	 let ts = make_constructor ts d in
	 begin
	   if rep_uneq ts a b then
	     printf "Test 10b (propagating disequalities) Passed!\n"
	   else
	     printf "Test 10b (propagating disequalities) Failed!\n"
	 end
       in
       (* test conjoin *)
       let cc = create () in
       let nil,cc = fresh cc in
       let cons,cc = fresh cc in
       let t0 = nth cons nil 0 in
       let t1 = nth cons nil 1 in
       let t2 = nth cons nil 2 in
       let l0,cc = add_term cc t0 in
       let l1,cc = add_term cc t1 in
       let l2,cc = add_term cc t2 in

       if rep_eq cc l0 nil then printf "Correct Test 11a. \n"
	 else
	   begin
	     printf "Test 11a fails!";
	     print_constant cc nil;
	     print_constant cc cons;
	     print_constant cc l1;
	     print_constant cc l2;
	     print cc
	   end;

       let cc = make_equal cc l0 l2 in

       if rep_eq cc l0 l2 && rep_eq cc l0 nil &&
	   (not (rep_eq cc l1 l2)) && (not (rep_eq cc l0 l1))
	 then printf "Correct Test 11b. \n"
	 else
	   begin
	     printf "Test 11b fails!";
	     print_constant cc nil;
	     print_constant cc cons;
	     print_constant cc l1;
	     print_constant cc l2;
	     print cc
	   end;

       let subst_list = [cons, r1; nil, r2; l0, c0; l1, c1; l2, c2] in

       let subst x = let y = List.assoc x subst_list in (false, y) in

       let ccts = merge_cc subst cc ts in

       if rep_eq ccts c0 c2 && rep_eq ccts c1 c3 && rep_eq ccts c2 c4 &&
	   (not (rep_eq ccts c1 c2)) && (not (rep_eq ccts c2 c3)) && (not (rep_eq ccts c3 c4))
	 then printf "Correct Test 11c. \n"
	 else
	   begin
	     printf "Test 11c fails!";
	     printf "@[<2>Attempted to merge cc:@\n";
	     print cc;
	     printf "@]@[<2>into ts:@\n";
	     print ts;
	     printf "@]@[<2>using substitution:@\n[%a]@\n"
	       (pp_list_sep ", " (fun f (a,b) -> fprintf f "%d->%d" a b)) subst_list;
	     printf "@]@[<2>obtaining ccts:@\n";
	     print ccts;
	     printf "@]@?";
	   end;
       ()

(*
(* Can probably remove pattern match by using unifiable variables in terms.*)
    let rec patternmatch_inner pattern con ts (cont : t -> 'a) : 'a =
      match pattern with
	CHole c -> cont (try make_equal ts c con with Contradiction -> raise No_match)
      |	CPConstant c -> if rep_eq ts c con then cont ts else raise No_match
      |	CPApp (p1,p2) ->
	  let cl = Arev_lookup.get ts.rev_lookup (rep ts con) in
          Backtrack.tryall
            (fun (c1,c2) ->
              Backtrack.chain
                [ patternmatch_inner p1 c1; patternmatch_inner p2 c2 ]
                ts cont)
            cl
*)

    let rec patternmatch_inner pattern con ts (cont : t -> 'a) : 'a =
      match pattern with
      |	Constant c ->
	  if rep_eq ts c con then
	    cont ts
	  else
	    begin
	      match Aunifiable.get ts.unifiable (rep ts c), Aunifiable.get ts.unifiable (rep ts con) with
	      Unifiable, _
	    | UnifiableExists, Exists ->
		cont (try make_equal ts c con with Contradiction -> raise No_match)
	    | UnifiableExists, _ ->
	        if no_live ts (rep ts con) then
		    (* If not live accesses treat as an exists *)
		    cont (try make_equal ts c con with Contradiction -> raise No_match)
		else
                  (* Needs to be an exists, so fail*)
		  raise No_match
	    | Exists,_
	    | Standard, _ -> raise No_match
	    | Deleted, _ -> raise No_match
	    end
      |	App (p1,p2) ->
	  let cl = Arev_lookup.get ts.rev_lookup (rep ts con) in
	  Backtrack.tryall
             (fun (c1,c2) ->
               Backtrack.chain
                 [ patternmatch_inner p1 c1; patternmatch_inner p2 c2 ]
                 ts cont)
             cl
    let patternmatch ts pattern constant (cont : t -> 'a) : 'a =
      patternmatch_inner pattern constant ts cont

    let unifies = patternmatch


    let unifies_any ts c1 cont =
      (* Very naive code, should do something clever like e-matching, but will do for now. *)
      let rec f n =
	if n = Auselist.size ts.uselist then
	  raise No_match
	else
	    if n <> rep ts n then f (n+1)
	    else
	      try
		unifies ts c1 n (fun ts -> cont (ts,n))
	      with No_match
		  -> f (n+1)
      in f 0


    let rec determined_exists ts cl c1 c2 : t * ((constant * constant) list) =
      if rep_eq ts c1 c2 then
      (* They are equal *)
	ts, []
      else if rep_uneq ts c1 c2 then
	raise Contradiction
      else if no_live ts c1 && rep_not_used_in ts c1 cl then
	begin
          (* They can be made equal *)
	  (* TODO Add occurs check *)
	  (make_equal ts c1 c2), []
	end
      else if no_live ts c2 && rep_not_used_in ts c2 cl then
	begin
          (* They can be made equal *)
	  (* TODO Add occurs check *)
	  (make_equal ts c2 c1), []
	end
      else
	match Aconstructor.get ts.constructor (rep ts c1), Aconstructor.get ts.constructor (rep ts c2) with
	  IApp(a,b), IApp(c,d) ->
	    begin
	      let ts, cp1 = determined_exists ts cl a c in
	      let ts, cp2 = determined_exists ts cl b d in
	      ts,(cp1 @ cp2)
	    end
	| _ -> ts, [c1,c2]



    let normalise ts c =
      rep ts c
    let others ts c =
      Aclasslist.get ts.classlist (rep ts c)

   let rec inter_list (i : int) (j : int) : int list =  if i > j then [] else (i :: inter_list (i+1) j)

    let get_consts ts = inter_list 0 (Arepresentative.size ts.representative - 1)

    let get_reps mask map ts =
      List.map map
         (List.filter (fun i -> Arepresentative.get ts.representative i = i && mask i)
                      (inter_list 0 (Arepresentative.size ts.representative - 1)))


    (* TODO: Is it intended to export this one rather than the earlier one? *)
    let rep_uneq ts c d =
      try
	ignore (make_equal ts c d); false
      with Contradiction -> true


    let const_int const ts = const


    let eq_term (ts : t) (term1 : curry_term) (term2 : curry_term) : bool =
      normalize ts term1 = normalize ts term2
    let neq_term (ts : t) (term1 : curry_term) (term2 : curry_term) : bool =
      match normalize ts term1, normalize ts term2 with
	Constant c1, Constant c2 -> rep_uneq ts c1 c2
      |	t1,t2 ->
	  let c1,ts = add_curry_term ts t1 in
	  let c2,ts = add_curry_term ts t2 in
	  rep_uneq ts c1 c2

    let delete ts r =
      let current_sort = Aunifiable.get ts.unifiable r in
      match current_sort with
	Unifiable
      |	UnifiableExists
      |	Exists ->
	  {ts with unifiable = Aunifiable.set ts.unifiable r Deleted}
      | Deleted ->
          (* Double dispose *)
	  ts (*assert false*)
      |	Standard ->
	  {ts with unifiable = Aunifiable.set ts.unifiable r Deleted}

	    
    let forget_qs cc =
      assert (invariant cc);
      let n = size cc in
      let r = grow n (create ()) in
      let r =
	{ r with
	  constructor = cc.constructor
	; unifiable = cc.unifiable } in
(*
      let reset reset_i = for i = 0 to n do reset_i i done in
      let r =
      { cc with
        uselist = reset (reset_uselist cc)
      ; representative = reset (reset_representative cc)
      ; classlist = reset (reset_classlist cc)
      ; lookup = CCMap.empty
      ; rev_lookup = reset (reset_rev_lookup cc)
      ; not_equal = CCmap.empty } in
*)
      assert (invariant r);
      r

  end

(* DBG
let _ = CC.test ()
*)
