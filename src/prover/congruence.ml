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

      type pattern_curry =
	  CHole of constant
	| CPConstant of constant
	| CPApp of pattern_curry * pattern_curry

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

      (* Qeury if two terms are equal. *)
(*      val eq : t -> term -> term -> bool*)

      val normalise : t -> constant -> constant
      val others : t -> constant -> constant list
      val eq_term : t -> curry_term -> curry_term -> bool
      val neq_term : t -> curry_term -> curry_term -> bool

      (* Pattern match, takes pattern and representative,
	 and continuation and backtracks in continuation raises No_match  *)
      val patternmatch : t -> curry_term -> constant -> (t -> 'a) -> 'a

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

      (* surjective mapping from constants to integers *)
      val const_int : constant -> t -> int

      val test : unit -> unit

      val delete : t -> constant -> t

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

    type pattern_curry =
	CHole of constant
      |	CPConstant of constant
      |	CPApp of pattern_curry * pattern_curry

    let rec curry (t : term)
	=
      match t with
	TConstant c -> Constant c
      | Func (c,tl) -> List.fold_left (fun ct t -> App (ct,(curry t))) (Constant c) tl


    let rec currypattern (t : pattern)  : pattern_curry
	=
      match t with
	Hole c -> CHole c
      |	PConstant c -> CPConstant c
      | PFunc (c,tl) -> List.fold_left (fun ct t -> CPApp (ct,(currypattern t))) (CPConstant c) tl




    type complex_eq = (* a *)constant * (* b *)constant * (* c *)constant  (* app(a,b) = c *)

    type flat_eq =
      |  Complex of complex_eq

    type use =
	Complex_eq of complex_eq
      |	Not_equal of constant


    module CCMap = Map.Make(
      struct
	type t = constant * constant
	let compare = intcmp2
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
	  lookup : complex_eq CCMap.t;
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
    let get_representative cc = Arepresentative.get cc.representative
    let set_representative cc i v = { cc with representative = Arepresentative.set cc.representative i v }
    let get_classlist cc = Aclasslist.get cc.classlist
    let set_classlist cc i v = { cc with classlist = Aclasslist.set cc.classlist i v }
    let get_rev_lookup cc = Arev_lookup.get cc.rev_lookup
    let set_rev_lookup cc i v = { cc with rev_lookup = Arev_lookup.set cc.rev_lookup i v }
    let get_constructor cc = Aconstructor.get cc.constructor
    let set_constructor cc i v = { cc with constructor = Aconstructor.set cc.constructor i v }
    let get_unifiable cc = Aunifiable.get cc.unifiable
    let set_unifiable cc i v = { cc with unifiable = Aunifiable.set cc.unifiable i v }

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

    (* XXX: Update, so it checks everything [sanitize] does. *)
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

    (* Asserts the following, in this order:
      - All constants appearing within fields of [cc] with the exception of
        [classlist] are class representants. A constant [c] is a class
        representant when [representatives[c]=c]. In particular, this implies
        that [representatives] is idempotent.
      - The entries of [unifiable], [constructor] and [classlist] that
        correspond to constants that are not representatives have default
        values.
      - All lists are actually representing sets, so they must have no repeats.
        In addition, they are strictly increasing. (TODO: Change the data type
        to [Set]?)
      - Pairs in [not_equal] are strictly increasing.
      - The [uselist] contains exactly the aparitions in [lookup] and
        [not_equal].
      - The [rev_lookup] is the reverse of [lookup].
      - The [rev_lookup] contains no repeats of the first component, if it is a
        constructor.
      - The [classlist] is the reverse of [representatives].
      - Closure under propagation of disequalities:
        - If (a, b)∊not_equal, f constructor, and {f(a)=c, f(b)=d}⊆lookup,
          then (c, d)∊not_equal.
        - If {f(a)=c, f(b)=d}∊lookup and (c,d)∊not_equal,
          then (a,b)∊not_equal
      - If f and g are constructors and rep(f)!=rep(g), then (f,g)∊not_equal.
        (NOTE&TODO: This is currently *not* true, but simulated by [rep_uneq].
        It may be less risky and not much slower to explicitly use [not_equal].)

    NOTE: The checks above imply closure under propagation of equalities:
      - (a=b --> f(a)=f(b)) because there are only reps in [lookup]
      - (f cons --> f(a)=f(b) --> a=b)
        because [rev_lookup] doesn't repeat constructors
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

      let chk_rev_lkp_cons (a, _) (b, _) =
        assert (a <> b || get_constructor cc a = Not) in
      for c = 0 to n - 1 do
        Misc.iter_pairs chk_rev_lkp_cons (get_rev_lookup cc c)
      done;

      let rep_cnt = ref 0 in
      let chk_clsrep c b = incr rep_cnt; assert (get_representative cc b = c) in
      for c = 0 to n - 1 do List.iter (chk_clsrep c) (get_classlist cc c) done;
      assert (!rep_cnt = n);

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

      for c = 0 to n - 1 do if get_constructor cc c <> Not then
        for d = c + 1 to n - 1 do if get_constructor cc d <> Not then
          assert (CCMap.mem (c, d) cc.not_equal)
        done
      done
      (* END of [strict_invariant] check *)

    (* TODO: Maintain these counts, so that [get_weight] takes O(1) time. *)
    let get_weight cc c =
      List.length (get_uselist cc c) + List.length (get_classlist cc c)

    let rec work_list f cc = function
      | [] -> cc
      | j :: js -> let is, cc = f j cc in work_list f cc (is @ js)

    (* Maintains [strict_invariant]. *)
    let add_eq (a, b) cc =
      if safe then strict_invariant cc;
      let a, b = get_representative cc a, get_representative cc b in
      let a, b = if get_weight cc a < get_weight cc b then b, a else a, b in
      let cs = get_classlist cc b in
      let cc = List.fold_left (fun cc c -> set_representative cc c a) cc cs in
      let cc = set_classlist cc a (Misc.merge_lists (get_classlist cc a) cs) in
      let cc = set_classlist cc b [] in
      let update_use (eqs, cc) = function
        | Complex_eq (x, y, z) as use ->
            let lookup = CCMap.remove (x, y) cc.lookup in
            let cc = set_rev_lookup cc z (* TODO: make it a Set *)
                (List.filter ((<>) (x, y)) (get_rev_lookup cc z)) in
            let d = if x = b then y else x in
            let cc =
              set_uselist cc d (List.filter ((<>) use) (get_uselist cc d)) in
            let x, y = let f c = if c = b then a else c in (f x, f y) in
            (try
              let _, _, zz = CCMap.find (x, y) lookup in
              ((z, zz) :: eqs, { cc with lookup })
            with Not_found ->
              let cc = set_uselist cc d
                (Misc.insert_sorted (Complex_eq (x, y, z)) (get_uselist cc d)) in
              let cc = set_rev_lookup cc z
                (Misc.insert_sorted (x, y) (get_rev_lookup cc z)) in
              (eqs, { cc with lookup = CCMap.add (x, y) (x, y, z) lookup }))
        | Not_equal x ->
            if x = a then raise Contradiction;
            let not_equal =
              CCMap.remove (if b < x then b, x else x, b) cc.not_equal in
            let cc = set_uselist cc x
              (List.filter ((<>) (Not_equal b)) (get_uselist cc x)) in
            let not_equal =
              CCMap.add (if a < x then a, x else x, a) () not_equal in
            let cc = { cc with not_equal } in
            let cc = set_uselist cc a
              (Misc.insert_sorted (Not_equal x) (get_uselist cc a)) in
            let cc = set_uselist cc x
              (Misc.insert_sorted (Not_equal a) (get_uselist cc x)) in
            (eqs, cc) in
      let eqs, cc = List.fold_left update_use ([], cc) (get_uselist cc b) in
      let cc = set_uselist cc b [] in
      (* XXX: unifiable/constructor *)
      if safe then strict_invariant cc;
      (eqs, cc)

    (* Maintains [strict_invariant]. *)
    let add_neq _ = failwith "XXX"

    let fresh ts : int * t =
      assert (invariant ts);
      let c = size ts in
      let ts =
        {ts with
          uselist = Auselist.grow ts.uselist 1;
          representative = Arepresentative.grow ts.representative 1;
          classlist = Aclasslist.grow ts.classlist 1;
          rev_lookup = Arev_lookup.grow ts.rev_lookup 1;
          constructor = Aconstructor.grow ts.constructor 1;
          unifiable = Aunifiable.grow ts.unifiable 1;
        } in
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

    (* TODO(rgrig): Why is this not commutative? *)
    let merge_unify u1 u2 = match u1, u2 with
      | Unifiable, Unifiable -> Unifiable
      | Unifiable, UnifiableExists
      | UnifiableExists, Unifiable
      | UnifiableExists, UnifiableExists -> UnifiableExists
      | _, Unifiable
      | _, UnifiableExists -> Deleted
      | _, a -> a

    (* POST: does path compresion *)
    let rec get_rep_root cc i =
      let j = get_representative cc i in
      if i = j then (i, cc)
      else begin
        let j, cc = get_rep_root cc j in
        (j, set_representative cc i j)
      end

    (* Establish the invariant by:
      - making [representative] idempotent, so parent(x)==root(x)
      - recomputing [uselist], [classlist] and [rev_lookup], out of the others
      - infering extra equalities & disequalities
        - a == b --> f(a) == f(b), for all functions f
        - a != b --> f(a) != f(b), when f is a constructor
        - and converses of the above
      - makes sure that [uselist], [classlist], [lookup], [rev_lookup],
        [not_equal] are normalized as follows
        - they mention only representatives
        - they have no duplicates, and are sorted
        - pairs in [not_equal] are sorted (because the represent sets)
    May raise [Contradiction]. *)
    (* XXX: Completely wrong and unusable at the moment. *)
    let sanitize cc =
      let n = size cc in
      let mapi f cc =
        let rec g cc i = if i = n then cc else f i cc in
        g cc 0 in

      (* reset fields to be recomputed *)
      let cc = { cc with uselist = Auselist.grow (Auselist.create ()) n } in
      let cc = { cc with classlist = Aclasslist.grow (Aclasslist.create ()) n } in
      let cc = { cc with rev_lookup = Arev_lookup.grow (Arev_lookup.create ()) n } in

      (* recompute [rev_lookup] *)

      (* propagate equalities, then disequalities *)

      (* recompute [classlist], and make [representative] idempotent *)
      let update_class c cc =
        let d, cc = get_rep_root cc c in
        let cs = get_classlist cc d in
        set_classlist cc d (c :: cs) in
      let cc = mapi update_class cc in
      cc


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
      let set_rev_lookup = ws set_rev_lookup in
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
      (* update lookup and rev_lookup *)
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
      let rev_app (a2, b2) (_, _, c2) =
        let c2rep = rep cc2 c2 in
        let ab2reps = (rep cc2 a2, rep cc2 b2) in
        let olds = get_rev_lookup !cc2 c2rep in
        set_rev_lookup cc2 c2rep (ab2reps :: olds) in
      for i = 0 to n2 - 1 do set_rev_lookup cc2 i [] done;
      CCMap.iter rev_app !cc2.lookup;
      for i = 0 to n2 - 1 do
        set_rev_lookup cc2 i (get_rev_lookup !cc2 (rep cc2 i))
      done;
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
      (*
      (* update classes *)
      for i = 0 to n2 - 1 do set_classlist cc2 i [] done;
      for i = 0 to n2 - 1 do
        let r = rep cc2 i in set_classlist cc2 r (i :: get_classlist !cc2 r)
      done;
      (* add disequalities *)
      let add_neq (a, b) () =
        cc2 :=
          { !cc2 with
          not_equal = CCMap.add (sub a, sub b) () !cc2.not_equal } in
      CCMap.iter add_neq !cc1.not_equal;
      (* check for contradictions; NOTE: must be at the end! *)
      let check_contradiction (a, b) () =
        if rep cc2 a <> rep cc2 b then raise Contradiction in
      CCMap.iter check_contradiction !cc2.not_equal;
      (* update uselist; *)
      let lookup_use (a, b) eq =
        let a, b = (rep cc2 a, rep cc2 b) in
        let f a =
          let olds = get_uselist !cc2 a in
          set_uselist cc2 a (Complex_eq eq :: olds) in
        f a; f b in
      for i = 0 to n2 - 1 do set_uselist cc2 i [] done;
      CCMap.iter lookup_use !cc2.lookup;
      let neq_use (a, b) () =
        let a, b = rep cc2 a, rep cc2 b in
        let f a b = set_uselist cc2 a (Not_equal b :: get_uselist !cc2 a) in
        f a b; f b a in
      CCMap.iter neq_use !cc2.not_equal;
      let trim_list l =
	let f l x = match l with
	  | [] -> [x]
	  | (x'::l') when x = x' -> l'
	  | l' -> x::l' in
	List.fold_left f [] (List.sort compare l) in
      for i = 0 to n2 - 1 do set_uselist cc2 i (trim_list (get_uselist !cc2 i)) done;
      if safe then assert (invariant !cc2);
      !cc2
      *)

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
	    let r =  rep ts c in
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
    and make_uses_constructor d (ts,pending) =
      let ul = get_uselist ts d in
      match ul with
	[] -> ts,pending
      | _ -> List.fold_left (make_use_constructor d) (ts,pending) ul

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


    let unifiable_merge ts a b : t =
      let vt =
        merge_unify
          (Aunifiable.get ts.unifiable a)
          (Aunifiable.get ts.unifiable b) in
      {ts with unifiable = Aunifiable.set ts.unifiable b vt}

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
	    remove_duplicates intcmp2
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
	    remove_duplicates (intcmp) ul
	      ) in
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
	     printf "Test 10 Passed!\n"
	   else
	     printf "Test 10 Failed!\n"
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

       let subst x = let y = List.assoc x subst_list in (true, y) in

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

  end

let _ = CC.test ()
