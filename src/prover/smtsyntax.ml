(********************************************************
   This file is part of coreStar
	src/prover/smtsyntax.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Format
open List
open Corestar_std
open Debug
open Psyntax

type smt_response =
  | Unsupported
  | Error of string
  | Sat
  | Unsat
  | Unknown

module Regexp = struct type t = Str.regexp let compare = compare end
module RegexpSet = Set.Make (Regexp)

let predeclared = ref RegexpSet.empty

let is_predeclared id =
  RegexpSet.exists (fun r -> Str.string_match r id 0) !predeclared

(* This function should be used below to munge all symbols (usually known as
  identifiers). See Section 3.1 of SMT-LIB standard for allowed symbols. *)
(* TODO: Munge keywords such as par, NUMERAL, _, as, let. *)
let id_munge =
  let ok_char = Array.make 256 false in
  let range_ok a z =
    for c = Char.code a to Char.code z do ok_char.(c) <- true done in
  range_ok 'a' 'z'; range_ok 'A' 'Z'; range_ok '0' '9';
  String.iter (fun c -> ok_char.(Char.code c) <- true) "~!@$^&*_+=<>?/-";
  fun s ->
    let n = String.length s in
    let rec ok i = i = n || (ok_char.(Char.code s.[i]) && ok (succ i)) in
    if ok 0 then s else begin
      let r = Buffer.create (n + 2) in
      Buffer.add_char r '|';
      String.iter
        (function '|' -> Buffer.add_string r "PIPE" | c -> Buffer.add_char r c)
        s;
      Buffer.add_char r '|';
      Buffer.contents r
    end


(** Datatype to hold smt type annotations *)
type smt_type =
| SType_var of int (** type variable *)
| SType_elastic_bv of int (** bitvector of unknown size with a type id *)
| SType_bv of string (** bitvector of known size *)
| SType_bool (** boolean sort *)
| SType_int (** mathematical integer sort *)
| SType_type of string (** user-defined type *)
| SType_fun of smt_type list * smt_type (** function type *)
(* I don't think SMT-LIB does higher-order but hopefully it won't show up... *)

exception Type_mismatch of smt_type * smt_type

let rec pp_smt_type f = function
| SType_var i -> fprintf f "tvar%d" i
| SType_elastic_bv i -> fprintf f "(_ BitVec bvar%d)" i
| SType_bv sz -> fprintf f "(_ BitVec %s)" sz
| SType_bool -> fprintf f "Bool"
| SType_int -> fprintf f "Int"
| SType_type s -> fprintf f "%s" s
| SType_fun (stl,rt) ->
  fprintf f "(%a) -> %a" (list_format "" pp_smt_type) stl pp_smt_type rt

let rec refines ta tb =
  match (ta, tb) with
  | (SType_var i, SType_var j) -> j <= i
  | (_, SType_var _) -> true
  | (SType_elastic_bv i, SType_elastic_bv j) -> j <= i
  | (SType_bv _, SType_elastic_bv _) -> true
  | (SType_elastic_bv _, SType_bv _) -> false
  | (SType_int, SType_int) | (SType_bool, SType_bool) -> true
  | (SType_bv i, SType_bv j) when i = j -> true
  | (SType_type s1, SType_type s2) when s1 = s2 -> true
  | (SType_fun (lt1,rt1), SType_fun (lt2, rt2)) when length lt1 = length lt2 ->
    List.for_all2 refines (rt1::lt1) (rt2::lt2)
  | (SType_var _, _) -> false
  | _ -> false

let compatible ta tb =
  refines ta tb or refines tb ta

let rec compatible_list tla tlb =
  match (tla, tlb) with
  | ([], []) -> true
  | (ta::tla, tb::tlb) -> compatible ta tb && (compatible_list tla tlb)
  | _ -> raise (Invalid_argument "mismatching list lengths in compatible_list")

(*** naive implementation of a union-find structure *)
let uf = Hashtbl.create 256
let uf_find i =
  let rec lookup i = try lookup (Hashtbl.find uf i) with Not_found -> i in
  lookup i
let uf_union i j =
  if i <> j then
    let ri = uf_find i in
    let rj = uf_find j in
    if ri <> rj then
      if refines ri rj then Hashtbl.add uf rj ri
      else Hashtbl.add uf ri rj

(** pick the most precise representative of [s] *)
let rec final_type s =
  let t = uf_find s in
  match t with
  | SType_fun (ll,r) ->
    SType_fun (List.map final_type ll, final_type r)
  | _ -> t

(** unification of types *)
and unify ta tb =
  let ta = uf_find ta in
  let tb = uf_find tb in
  if ta <> tb then
    match (ta, tb) with
    | (SType_var _, _) | (_, SType_var _)
    | (SType_elastic_bv _, SType_elastic_bv _)
    | (SType_elastic_bv _, SType_bv _) | (SType_bv _, SType_elastic_bv _) ->
      uf_union ta tb
    | (SType_bv s1, SType_bv s2) when s1 = s2 -> ()
    | (SType_type s1, SType_type s2) when s1 = s2 -> ()
    | (SType_int, SType_int) | (SType_bool, SType_bool) -> ()
    | (SType_fun (l1,r1), SType_fun (l2,r2)) when length l1 = length l2 ->
      iter2 unify (r1::l1) (r2::l2)
    | _ -> raise (Type_mismatch (ta, tb))

let rec unify_list = function
  | a::b::tl -> unify a b; unify_list (b::tl)
  | _::[] | [] -> ()

(** next fresh index for type variables and elastic bitvectors *)
let __typeindex = ref 0
let fresh_type_index () =
  __typeindex := !__typeindex +1;
  !__typeindex -1

let rec mk_final_type s =
  match final_type s with
  | SType_bool
  | SType_int 
  | SType_type _
  | SType_bv _ -> ()
  | SType_elastic_bv i ->
    (* if we don't know the size of the bit-vector at this point, we
       have to pick one. 64 is as good a size as any I guess... *)
    unify (SType_bv "64") (SType_elastic_bv i)
  | SType_var i ->
    (* same as above *)
    unify (SType_bv "64") (SType_var i)
  | SType_fun (lt,rt) ->
    List.iter mk_final_type (rt::lt)

(** typing context *)
let typing_context : (string, smt_type) Hashtbl.t = Hashtbl.create 256
let lookup_type id =
  try final_type (Hashtbl.find typing_context id)
  with Not_found ->
    let t = SType_var (fresh_type_index ()) in    
    Hashtbl.add typing_context id t;
    t

let complete_all_types () =
  Hashtbl.iter
    (fun id t -> mk_final_type t)
    typing_context

let reset_typing_context () =
  Hashtbl.clear typing_context

let dump_typing_context () =
  Hashtbl.iter (fun id t -> fprintf logf "%s: %a@ " id pp_smt_type (final_type t)) typing_context

(*** final translation into SMT expressions *)

let sexp_of_sort s =
  match final_type s with
  | SType_bool -> "Bool"
  | SType_int -> "Int"
  | SType_type s -> s
  | SType_bv sz ->
    Printf.sprintf "(_ BitVec %s)" sz
  | SType_elastic_bv i
  | SType_var i ->
    (* shouldn't get here! make sure that complete_all_types has run
       before calling this function! *)
    assert false
  | SType_fun _ -> raise (Invalid_argument "Unexpected function type")

let rec sexp_of_sort_list = function
  | [] -> ""
  | t::tl -> " " ^ (sexp_of_sort t) ^ (sexp_of_sort_list tl)


(*** translate coreStar predicates into native SMT functions *)

let smtname_and_type_of_op :
    (string -> Psyntax.args list -> (string * smt_type * Psyntax.args list)) ref
    = ref (fun name args -> (id_munge ("op_"^name), lookup_type ("op_"^name), args))

(** bitvector operations *)
let add_native_bitvector_ops () =
  (* bit-vector operations in SMT-LIB are polymorphic in the size of
     the bit-vectors. The type of a bit-vector operation is that both
     arguments and the result are bit-vectors of the same size *)
  let translate_bin_bvop f bop name args =
    let r = Str.regexp (Printf.sprintf "%s.\\([0-9]+\\)" bop) in
    if Str.string_match r name 0 then
      let sz = Str.matched_group 1 name in
      let t = SType_bv sz in
      (bop, SType_fun ([t; t], t), args)
    else f name args in
  List.iter
    (fun s -> smtname_and_type_of_op := translate_bin_bvop !smtname_and_type_of_op s)
    ["bvand"; "bvor"; "bvadd"; "bvmul"; "bvudiv"; "bvurem"; "bvshl"; "bvlshr";
     (* the operations below are not in official SMT-LIB2, but z3
	knows about them. TODO: provide macros for them? *)
     "bvsdiv"; "bvsrem"; "bvashr"; "bvxor";
    ];
  let translate_un_bvop f bop name args =
    let r = Str.regexp (Printf.sprintf "%s.\\([0-9]+\\)" bop) in
    if Str.string_match r name 0 then
      let sz = Str.matched_group 1 name in
      let t = SType_bv sz in
      (bop, SType_fun ([t], t), args)
    else f name args in
  List.iter
    (fun s -> smtname_and_type_of_op := translate_un_bvop !smtname_and_type_of_op s)
    ["bvnot"; "bvneg"];
  let translate_concat f name args =
    let r = Str.regexp "concat.\\([0-9]+\\).\\([0-9]+\\)" in
    if Str.string_match r name 0 then
      let sz1 = Str.matched_group 1 name in
      let sz2 = Str.matched_group 2 name in
      let sz3 = string_of_int (int_of_string sz1 + int_of_string sz2) in
      ("concat", SType_fun ([SType_bv sz1; SType_bv sz2], SType_bv sz3), args)
    else f name args in
  smtname_and_type_of_op := translate_concat !smtname_and_type_of_op;
  let translate_extract f name args =
    let r = Str.regexp "extract.\\([0-9]+\\)" in
    if Str.string_match r name 0 then
      let szarg = Str.matched_group 1 name in
      match args with
	Arg_op("numeric_const",[Arg_string i])::Arg_op("numeric_const",[Arg_string j])::args
      | Arg_string i::Arg_string j::args ->
	(try
	   (Printf.sprintf "(_ extract %s %s)" i j,
	    SType_fun ([SType_bv szarg], SType_bv
	      (string_of_int (int_of_string i - int_of_string j + 1))),
	    args)
	 with | Failure _ -> f name args)
      | _ -> f name args
    else f name args in
  smtname_and_type_of_op := translate_extract !smtname_and_type_of_op

(** mathematical integer operations *)
let add_native_int_ops () =
  let iop_to_smtiop =
    [("builtin_add", "+");
     ("builtin_sub", "-");
     ("builtin_mul", "*");
     ("builtin_div", "/");
    ] in
  let translate_bin_iop f name args =
    try
      (List.assoc name iop_to_smtiop,
       SType_fun ([SType_int; SType_int], SType_int), args)
    with Not_found -> f name args in
  smtname_and_type_of_op := translate_bin_iop !smtname_and_type_of_op

let add_native_int_rels () =
  let irel_to_smtiop =
    [("GT", ">");
     ("builtin_gt", ">");
     ("GE", ">=");
     ("builtin_ge", ">=");
     ("LT", "<");
     ("builtin_lt", "<");
     ("LE", "<=");
     ("builtin_le", "<=");
    ] in
  let translate_bin_rel f name args =
    try
      (List.assoc name irel_to_smtiop,
       SType_fun ([SType_int; SType_int], SType_bool), args)
    with Not_found -> f name args in
  smtname_and_type_of_op := translate_bin_rel !smtname_and_type_of_op

let add_native_false () =
  let add_false f name args =
    if name = "@False" then ("false", SType_bool, args)
    else f name args in
  smtname_and_type_of_op := add_false !smtname_and_type_of_op
