(********************************************************
   This file is part of coreStar
        src/utils/vars.ml
   Release
        $Release$
   Version
        $Rev$
   $Copyright$

   coreStar is distributed under a BSD license,  see,
      LICENSE.txt
 ********************************************************)

open Corestar_std
open Format

type var =
  | PVar of int * string
  | EVar of int * string
  | AnyVar of int * string

let is_avar = function AnyVar _ -> true | _ -> false
let is_evar = function EVar _ -> true | _ -> false
let is_pvar = function PVar _ -> true | _ -> false

let check_name s = if s = "" then invalid_arg "empty var name"

let mk_pvar i s = check_name s; PVar (i, s)
let mk_evar i s = check_name s; EVar (i, s)
let mk_anyvar i s = check_name s; AnyVar (i, s)

let gensym = ref 0
let fresh mk s = incr gensym; mk !gensym s
let freshp_str = fresh mk_pvar
let freshe_str = fresh mk_evar
let fresha_str = fresh mk_anyvar
let freshp () = freshp_str "v"
let freshe () = freshe_str "v"
let fresha () = fresha_str "v"

let is_fresh = function PVar (n, _) | EVar (n, _) | AnyVar (n, _) -> n <> 0

module StrVarHash =
  Hashtbl.Make(struct
    type t = string
    let equal = (=)
    let hash = Hashtbl.hash
  end)

let hashcons = StrVarHash.create 1000

let concrete mk vn =
  try StrVarHash.find hashcons vn
  with Not_found ->
    let r = mk 0 vn in
    StrVarHash.add hashcons vn r;
    r

let concretep_str = concrete mk_pvar
let concretee_str = concrete mk_evar
let concretea_str = concrete mk_anyvar

let freshen = function
  | PVar (_,v) -> freshp_str v
  | EVar (_,v) -> freshe_str v
  | AnyVar (_,v) -> fresha_str v

let freshen_exists = function
  | PVar (_,v)
  | AnyVar (_,v)
  | EVar (_,v) -> freshe_str v



let pp_var f =
  let p = function 0 -> "" | n -> sprintf "_%d" n in
  function
    | PVar (n,vn) -> fprintf f "%s%s" vn (p n)
    | EVar (n,vn) -> fprintf f "_%s%s" vn (p n)
    | AnyVar (n,vn) -> fprintf f "a_%s%s" vn (p n)

let string_var = string_of pp_var
