(* Automatically generated file *)

(** The native (raw) interface to the dynamic Z3 library. *)

open Z3enums

(**/**)
type ptr
and z3_symbol = ptr
and z3_config = ptr
and z3_context = ptr
and z3_ast = ptr
and z3_app = ptr
and z3_sort = ptr
and z3_func_decl = ptr
and z3_pattern = ptr
and z3_model = ptr
and z3_literals = ptr
and z3_constructor = ptr
and z3_constructor_list = ptr
and z3_theory = ptr
and z3_theory_data = ptr
and z3_solver = ptr
and z3_goal = ptr
and z3_tactic = ptr
and z3_params = ptr
and z3_probe = ptr
and z3_stats = ptr
and z3_ast_vector = ptr
and z3_ast_map = ptr
and z3_apply_result = ptr
and z3_func_interp = ptr
and z3_func_entry = ptr
and z3_fixedpoint = ptr
and z3_param_descrs = ptr
and z3_rcf_num = ptr

external is_null : ptr -> bool
  = "n_is_null"

external mk_null : unit -> ptr
  = "n_mk_null"

external set_internal_error_handler : ptr -> unit
  = "n_set_internal_error_handler"

exception Exception of string

module ML2C = struct

    external n_global_param_set : string -> string -> unit
      = "n_global_param_set"

    external n_global_param_reset_all :  unit -> unit
      = "n_global_param_reset_all"

    external n_global_param_get : string -> (bool * string)
      = "n_global_param_get"

    external n_mk_config :  unit -> z3_config
      = "n_mk_config"

    external n_del_config : z3_config -> unit
      = "n_del_config"

    external n_set_param_value : z3_config -> string -> string -> unit
      = "n_set_param_value"

    external n_mk_context : z3_config -> z3_context
      = "n_mk_context"

    external n_mk_context_rc : z3_config -> z3_context
      = "n_mk_context_rc"

    external n_del_context : z3_context -> unit
      = "n_del_context"

    external n_inc_ref : z3_context -> z3_ast -> unit
      = "n_inc_ref"

    external n_dec_ref : z3_context -> z3_ast -> unit
      = "n_dec_ref"

    external n_update_param_value : z3_context -> string -> string -> unit
      = "n_update_param_value"

    external n_get_param_value : z3_context -> string -> (bool * string)
      = "n_get_param_value"

    external n_interrupt : z3_context -> unit
      = "n_interrupt"

    external n_mk_params : z3_context -> z3_params
      = "n_mk_params"

    external n_params_inc_ref : z3_context -> z3_params -> unit
      = "n_params_inc_ref"

    external n_params_dec_ref : z3_context -> z3_params -> unit
      = "n_params_dec_ref"

    external n_params_set_bool : z3_context -> z3_params -> z3_symbol -> bool -> unit
      = "n_params_set_bool"

    external n_params_set_uint : z3_context -> z3_params -> z3_symbol -> int -> unit
      = "n_params_set_uint"

    external n_params_set_double : z3_context -> z3_params -> z3_symbol -> float -> unit
      = "n_params_set_double"

    external n_params_set_symbol : z3_context -> z3_params -> z3_symbol -> z3_symbol -> unit
      = "n_params_set_symbol"

    external n_params_to_string : z3_context -> z3_params -> string
      = "n_params_to_string"

    external n_params_validate : z3_context -> z3_params -> z3_param_descrs -> unit
      = "n_params_validate"

    external n_param_descrs_inc_ref : z3_context -> z3_param_descrs -> unit
      = "n_param_descrs_inc_ref"

    external n_param_descrs_dec_ref : z3_context -> z3_param_descrs -> unit
      = "n_param_descrs_dec_ref"

    external n_param_descrs_get_kind : z3_context -> z3_param_descrs -> z3_symbol -> int
      = "n_param_descrs_get_kind"

    external n_param_descrs_size : z3_context -> z3_param_descrs -> int
      = "n_param_descrs_size"

    external n_param_descrs_get_name : z3_context -> z3_param_descrs -> int -> z3_symbol
      = "n_param_descrs_get_name"

    external n_param_descrs_to_string : z3_context -> z3_param_descrs -> string
      = "n_param_descrs_to_string"

    external n_mk_int_symbol : z3_context -> int -> z3_symbol
      = "n_mk_int_symbol"

    external n_mk_string_symbol : z3_context -> string -> z3_symbol
      = "n_mk_string_symbol"

    external n_mk_uninterpreted_sort : z3_context -> z3_symbol -> z3_sort
      = "n_mk_uninterpreted_sort"

    external n_mk_bool_sort : z3_context -> z3_sort
      = "n_mk_bool_sort"

    external n_mk_int_sort : z3_context -> z3_sort
      = "n_mk_int_sort"

    external n_mk_real_sort : z3_context -> z3_sort
      = "n_mk_real_sort"

    external n_mk_bv_sort : z3_context -> int -> z3_sort
      = "n_mk_bv_sort"

    external n_mk_finite_domain_sort : z3_context -> z3_symbol -> int -> z3_sort
      = "n_mk_finite_domain_sort"

    external n_mk_array_sort : z3_context -> z3_sort -> z3_sort -> z3_sort
      = "n_mk_array_sort"

    external n_mk_tuple_sort : z3_context -> z3_symbol -> int -> z3_symbol array -> z3_sort array -> (z3_sort * ptr * z3_func_decl array)
      = "n_mk_tuple_sort"

    external n_mk_enumeration_sort : z3_context -> z3_symbol -> int -> z3_symbol array -> (z3_sort * z3_func_decl array * z3_func_decl array)
      = "n_mk_enumeration_sort"

    external n_mk_list_sort : z3_context -> z3_symbol -> z3_sort -> (z3_sort * ptr * ptr * ptr * ptr * ptr * ptr)
      = "n_mk_list_sort"

    external n_mk_constructor : z3_context -> z3_symbol -> z3_symbol -> int -> z3_symbol array -> z3_sort array -> int array -> z3_constructor
      = "n_mk_constructor_bytecode"
        "n_mk_constructor"

    external n_del_constructor : z3_context -> z3_constructor -> unit
      = "n_del_constructor"

    external n_mk_datatype : z3_context -> z3_symbol -> int -> z3_constructor array -> (z3_sort * z3_constructor array)
      = "n_mk_datatype"

    external n_mk_constructor_list : z3_context -> int -> z3_constructor array -> z3_constructor_list
      = "n_mk_constructor_list"

    external n_del_constructor_list : z3_context -> z3_constructor_list -> unit
      = "n_del_constructor_list"

    external n_mk_datatypes : z3_context -> int -> z3_symbol array -> z3_constructor_list array -> (z3_sort array * z3_constructor_list array)
      = "n_mk_datatypes"

    external n_query_constructor : z3_context -> z3_constructor -> int -> (ptr * ptr * z3_func_decl array)
      = "n_query_constructor"

    external n_mk_func_decl : z3_context -> z3_symbol -> int -> z3_sort array -> z3_sort -> z3_func_decl
      = "n_mk_func_decl"

    external n_mk_app : z3_context -> z3_func_decl -> int -> z3_ast array -> z3_ast
      = "n_mk_app"

    external n_mk_const : z3_context -> z3_symbol -> z3_sort -> z3_ast
      = "n_mk_const"

    external n_mk_fresh_func_decl : z3_context -> string -> int -> z3_sort array -> z3_sort -> z3_func_decl
      = "n_mk_fresh_func_decl"

    external n_mk_fresh_const : z3_context -> string -> z3_sort -> z3_ast
      = "n_mk_fresh_const"

    external n_mk_true : z3_context -> z3_ast
      = "n_mk_true"

    external n_mk_false : z3_context -> z3_ast
      = "n_mk_false"

    external n_mk_eq : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_eq"

    external n_mk_distinct : z3_context -> int -> z3_ast array -> z3_ast
      = "n_mk_distinct"

    external n_mk_not : z3_context -> z3_ast -> z3_ast
      = "n_mk_not"

    external n_mk_interp : z3_context -> z3_ast -> z3_ast
      = "n_mk_interp"

    external n_mk_ite : z3_context -> z3_ast -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_ite"

    external n_mk_iff : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_iff"

    external n_mk_implies : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_implies"

    external n_mk_xor : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_xor"

    external n_mk_and : z3_context -> int -> z3_ast array -> z3_ast
      = "n_mk_and"

    external n_mk_or : z3_context -> int -> z3_ast array -> z3_ast
      = "n_mk_or"

    external n_mk_add : z3_context -> int -> z3_ast array -> z3_ast
      = "n_mk_add"

    external n_mk_mul : z3_context -> int -> z3_ast array -> z3_ast
      = "n_mk_mul"

    external n_mk_sub : z3_context -> int -> z3_ast array -> z3_ast
      = "n_mk_sub"

    external n_mk_unary_minus : z3_context -> z3_ast -> z3_ast
      = "n_mk_unary_minus"

    external n_mk_div : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_div"

    external n_mk_mod : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_mod"

    external n_mk_rem : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_rem"

    external n_mk_power : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_power"

    external n_mk_lt : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_lt"

    external n_mk_le : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_le"

    external n_mk_gt : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_gt"

    external n_mk_ge : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_ge"

    external n_mk_int2real : z3_context -> z3_ast -> z3_ast
      = "n_mk_int2real"

    external n_mk_real2int : z3_context -> z3_ast -> z3_ast
      = "n_mk_real2int"

    external n_mk_is_int : z3_context -> z3_ast -> z3_ast
      = "n_mk_is_int"

    external n_mk_bvnot : z3_context -> z3_ast -> z3_ast
      = "n_mk_bvnot"

    external n_mk_bvredand : z3_context -> z3_ast -> z3_ast
      = "n_mk_bvredand"

    external n_mk_bvredor : z3_context -> z3_ast -> z3_ast
      = "n_mk_bvredor"

    external n_mk_bvand : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvand"

    external n_mk_bvor : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvor"

    external n_mk_bvxor : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvxor"

    external n_mk_bvnand : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvnand"

    external n_mk_bvnor : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvnor"

    external n_mk_bvxnor : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvxnor"

    external n_mk_bvneg : z3_context -> z3_ast -> z3_ast
      = "n_mk_bvneg"

    external n_mk_bvadd : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvadd"

    external n_mk_bvsub : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvsub"

    external n_mk_bvmul : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvmul"

    external n_mk_bvudiv : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvudiv"

    external n_mk_bvsdiv : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvsdiv"

    external n_mk_bvurem : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvurem"

    external n_mk_bvsrem : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvsrem"

    external n_mk_bvsmod : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvsmod"

    external n_mk_bvult : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvult"

    external n_mk_bvslt : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvslt"

    external n_mk_bvule : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvule"

    external n_mk_bvsle : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvsle"

    external n_mk_bvuge : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvuge"

    external n_mk_bvsge : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvsge"

    external n_mk_bvugt : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvugt"

    external n_mk_bvsgt : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvsgt"

    external n_mk_concat : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_concat"

    external n_mk_extract : z3_context -> int -> int -> z3_ast -> z3_ast
      = "n_mk_extract"

    external n_mk_sign_ext : z3_context -> int -> z3_ast -> z3_ast
      = "n_mk_sign_ext"

    external n_mk_zero_ext : z3_context -> int -> z3_ast -> z3_ast
      = "n_mk_zero_ext"

    external n_mk_repeat : z3_context -> int -> z3_ast -> z3_ast
      = "n_mk_repeat"

    external n_mk_bvshl : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvshl"

    external n_mk_bvlshr : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvlshr"

    external n_mk_bvashr : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvashr"

    external n_mk_rotate_left : z3_context -> int -> z3_ast -> z3_ast
      = "n_mk_rotate_left"

    external n_mk_rotate_right : z3_context -> int -> z3_ast -> z3_ast
      = "n_mk_rotate_right"

    external n_mk_ext_rotate_left : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_ext_rotate_left"

    external n_mk_ext_rotate_right : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_ext_rotate_right"

    external n_mk_int2bv : z3_context -> int -> z3_ast -> z3_ast
      = "n_mk_int2bv"

    external n_mk_bv2int : z3_context -> z3_ast -> bool -> z3_ast
      = "n_mk_bv2int"

    external n_mk_bvadd_no_overflow : z3_context -> z3_ast -> z3_ast -> bool -> z3_ast
      = "n_mk_bvadd_no_overflow"

    external n_mk_bvadd_no_underflow : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvadd_no_underflow"

    external n_mk_bvsub_no_overflow : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvsub_no_overflow"

    external n_mk_bvsub_no_underflow : z3_context -> z3_ast -> z3_ast -> bool -> z3_ast
      = "n_mk_bvsub_no_underflow"

    external n_mk_bvsdiv_no_overflow : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvsdiv_no_overflow"

    external n_mk_bvneg_no_overflow : z3_context -> z3_ast -> z3_ast
      = "n_mk_bvneg_no_overflow"

    external n_mk_bvmul_no_overflow : z3_context -> z3_ast -> z3_ast -> bool -> z3_ast
      = "n_mk_bvmul_no_overflow"

    external n_mk_bvmul_no_underflow : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_bvmul_no_underflow"

    external n_mk_select : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_select"

    external n_mk_store : z3_context -> z3_ast -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_store"

    external n_mk_const_array : z3_context -> z3_sort -> z3_ast -> z3_ast
      = "n_mk_const_array"

    external n_mk_map : z3_context -> z3_func_decl -> int -> z3_ast array -> z3_ast
      = "n_mk_map"

    external n_mk_array_default : z3_context -> z3_ast -> z3_ast
      = "n_mk_array_default"

    external n_mk_set_sort : z3_context -> z3_sort -> z3_sort
      = "n_mk_set_sort"

    external n_mk_empty_set : z3_context -> z3_sort -> z3_ast
      = "n_mk_empty_set"

    external n_mk_full_set : z3_context -> z3_sort -> z3_ast
      = "n_mk_full_set"

    external n_mk_set_add : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_set_add"

    external n_mk_set_del : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_set_del"

    external n_mk_set_union : z3_context -> int -> z3_ast array -> z3_ast
      = "n_mk_set_union"

    external n_mk_set_intersect : z3_context -> int -> z3_ast array -> z3_ast
      = "n_mk_set_intersect"

    external n_mk_set_difference : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_set_difference"

    external n_mk_set_complement : z3_context -> z3_ast -> z3_ast
      = "n_mk_set_complement"

    external n_mk_set_member : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_set_member"

    external n_mk_set_subset : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_mk_set_subset"

    external n_mk_numeral : z3_context -> string -> z3_sort -> z3_ast
      = "n_mk_numeral"

    external n_mk_real : z3_context -> int -> int -> z3_ast
      = "n_mk_real"

    external n_mk_int : z3_context -> int -> z3_sort -> z3_ast
      = "n_mk_int"

    external n_mk_unsigned_int : z3_context -> int -> z3_sort -> z3_ast
      = "n_mk_unsigned_int"

    external n_mk_int64 : z3_context -> int -> z3_sort -> z3_ast
      = "n_mk_int64"

    external n_mk_unsigned_int64 : z3_context -> int -> z3_sort -> z3_ast
      = "n_mk_unsigned_int64"

    external n_mk_pattern : z3_context -> int -> z3_ast array -> z3_pattern
      = "n_mk_pattern"

    external n_mk_bound : z3_context -> int -> z3_sort -> z3_ast
      = "n_mk_bound"

    external n_mk_forall : z3_context -> int -> int -> z3_pattern array -> int -> z3_sort array -> z3_symbol array -> z3_ast -> z3_ast
      = "n_mk_forall_bytecode"
        "n_mk_forall"

    external n_mk_exists : z3_context -> int -> int -> z3_pattern array -> int -> z3_sort array -> z3_symbol array -> z3_ast -> z3_ast
      = "n_mk_exists_bytecode"
        "n_mk_exists"

    external n_mk_quantifier : z3_context -> bool -> int -> int -> z3_pattern array -> int -> z3_sort array -> z3_symbol array -> z3_ast -> z3_ast
      = "n_mk_quantifier_bytecode"
        "n_mk_quantifier"

    external n_mk_quantifier_ex : z3_context -> bool -> int -> z3_symbol -> z3_symbol -> int -> z3_pattern array -> int -> z3_ast array -> int -> z3_sort array -> z3_symbol array -> z3_ast -> z3_ast
      = "n_mk_quantifier_ex_bytecode"
        "n_mk_quantifier_ex"

    external n_mk_forall_const : z3_context -> int -> int -> z3_app array -> int -> z3_pattern array -> z3_ast -> z3_ast
      = "n_mk_forall_const_bytecode"
        "n_mk_forall_const"

    external n_mk_exists_const : z3_context -> int -> int -> z3_app array -> int -> z3_pattern array -> z3_ast -> z3_ast
      = "n_mk_exists_const_bytecode"
        "n_mk_exists_const"

    external n_mk_quantifier_const : z3_context -> bool -> int -> int -> z3_app array -> int -> z3_pattern array -> z3_ast -> z3_ast
      = "n_mk_quantifier_const_bytecode"
        "n_mk_quantifier_const"

    external n_mk_quantifier_const_ex : z3_context -> bool -> int -> z3_symbol -> z3_symbol -> int -> z3_app array -> int -> z3_pattern array -> int -> z3_ast array -> z3_ast -> z3_ast
      = "n_mk_quantifier_const_ex_bytecode"
        "n_mk_quantifier_const_ex"

    external n_get_symbol_kind : z3_context -> z3_symbol -> int
      = "n_get_symbol_kind"

    external n_get_symbol_int : z3_context -> z3_symbol -> int
      = "n_get_symbol_int"

    external n_get_symbol_string : z3_context -> z3_symbol -> string
      = "n_get_symbol_string"

    external n_get_sort_name : z3_context -> z3_sort -> z3_symbol
      = "n_get_sort_name"

    external n_get_sort_id : z3_context -> z3_sort -> int
      = "n_get_sort_id"

    external n_sort_to_ast : z3_context -> z3_sort -> z3_ast
      = "n_sort_to_ast"

    external n_is_eq_sort : z3_context -> z3_sort -> z3_sort -> bool
      = "n_is_eq_sort"

    external n_get_sort_kind : z3_context -> z3_sort -> int
      = "n_get_sort_kind"

    external n_get_bv_sort_size : z3_context -> z3_sort -> int
      = "n_get_bv_sort_size"

    external n_get_finite_domain_sort_size : z3_context -> z3_sort -> (bool * int)
      = "n_get_finite_domain_sort_size"

    external n_get_array_sort_domain : z3_context -> z3_sort -> z3_sort
      = "n_get_array_sort_domain"

    external n_get_array_sort_range : z3_context -> z3_sort -> z3_sort
      = "n_get_array_sort_range"

    external n_get_tuple_sort_mk_decl : z3_context -> z3_sort -> z3_func_decl
      = "n_get_tuple_sort_mk_decl"

    external n_get_tuple_sort_num_fields : z3_context -> z3_sort -> int
      = "n_get_tuple_sort_num_fields"

    external n_get_tuple_sort_field_decl : z3_context -> z3_sort -> int -> z3_func_decl
      = "n_get_tuple_sort_field_decl"

    external n_get_datatype_sort_num_constructors : z3_context -> z3_sort -> int
      = "n_get_datatype_sort_num_constructors"

    external n_get_datatype_sort_constructor : z3_context -> z3_sort -> int -> z3_func_decl
      = "n_get_datatype_sort_constructor"

    external n_get_datatype_sort_recognizer : z3_context -> z3_sort -> int -> z3_func_decl
      = "n_get_datatype_sort_recognizer"

    external n_get_datatype_sort_constructor_accessor : z3_context -> z3_sort -> int -> int -> z3_func_decl
      = "n_get_datatype_sort_constructor_accessor"

    external n_get_relation_arity : z3_context -> z3_sort -> int
      = "n_get_relation_arity"

    external n_get_relation_column : z3_context -> z3_sort -> int -> z3_sort
      = "n_get_relation_column"

    external n_func_decl_to_ast : z3_context -> z3_func_decl -> z3_ast
      = "n_func_decl_to_ast"

    external n_is_eq_func_decl : z3_context -> z3_func_decl -> z3_func_decl -> bool
      = "n_is_eq_func_decl"

    external n_get_func_decl_id : z3_context -> z3_func_decl -> int
      = "n_get_func_decl_id"

    external n_get_decl_name : z3_context -> z3_func_decl -> z3_symbol
      = "n_get_decl_name"

    external n_get_decl_kind : z3_context -> z3_func_decl -> int
      = "n_get_decl_kind"

    external n_get_domain_size : z3_context -> z3_func_decl -> int
      = "n_get_domain_size"

    external n_get_arity : z3_context -> z3_func_decl -> int
      = "n_get_arity"

    external n_get_domain : z3_context -> z3_func_decl -> int -> z3_sort
      = "n_get_domain"

    external n_get_range : z3_context -> z3_func_decl -> z3_sort
      = "n_get_range"

    external n_get_decl_num_parameters : z3_context -> z3_func_decl -> int
      = "n_get_decl_num_parameters"

    external n_get_decl_parameter_kind : z3_context -> z3_func_decl -> int -> int
      = "n_get_decl_parameter_kind"

    external n_get_decl_int_parameter : z3_context -> z3_func_decl -> int -> int
      = "n_get_decl_int_parameter"

    external n_get_decl_double_parameter : z3_context -> z3_func_decl -> int -> float
      = "n_get_decl_double_parameter"

    external n_get_decl_symbol_parameter : z3_context -> z3_func_decl -> int -> z3_symbol
      = "n_get_decl_symbol_parameter"

    external n_get_decl_sort_parameter : z3_context -> z3_func_decl -> int -> z3_sort
      = "n_get_decl_sort_parameter"

    external n_get_decl_ast_parameter : z3_context -> z3_func_decl -> int -> z3_ast
      = "n_get_decl_ast_parameter"

    external n_get_decl_func_decl_parameter : z3_context -> z3_func_decl -> int -> z3_func_decl
      = "n_get_decl_func_decl_parameter"

    external n_get_decl_rational_parameter : z3_context -> z3_func_decl -> int -> string
      = "n_get_decl_rational_parameter"

    external n_app_to_ast : z3_context -> z3_app -> z3_ast
      = "n_app_to_ast"

    external n_get_app_decl : z3_context -> z3_app -> z3_func_decl
      = "n_get_app_decl"

    external n_get_app_num_args : z3_context -> z3_app -> int
      = "n_get_app_num_args"

    external n_get_app_arg : z3_context -> z3_app -> int -> z3_ast
      = "n_get_app_arg"

    external n_is_eq_ast : z3_context -> z3_ast -> z3_ast -> bool
      = "n_is_eq_ast"

    external n_get_ast_id : z3_context -> z3_ast -> int
      = "n_get_ast_id"

    external n_get_ast_hash : z3_context -> z3_ast -> int
      = "n_get_ast_hash"

    external n_get_sort : z3_context -> z3_ast -> z3_sort
      = "n_get_sort"

    external n_is_well_sorted : z3_context -> z3_ast -> bool
      = "n_is_well_sorted"

    external n_get_bool_value : z3_context -> z3_ast -> int
      = "n_get_bool_value"

    external n_get_ast_kind : z3_context -> z3_ast -> int
      = "n_get_ast_kind"

    external n_is_app : z3_context -> z3_ast -> bool
      = "n_is_app"

    external n_is_numeral_ast : z3_context -> z3_ast -> bool
      = "n_is_numeral_ast"

    external n_is_algebraic_number : z3_context -> z3_ast -> bool
      = "n_is_algebraic_number"

    external n_to_app : z3_context -> z3_ast -> z3_app
      = "n_to_app"

    external n_to_func_decl : z3_context -> z3_ast -> z3_func_decl
      = "n_to_func_decl"

    external n_get_numeral_string : z3_context -> z3_ast -> string
      = "n_get_numeral_string"

    external n_get_numeral_decimal_string : z3_context -> z3_ast -> int -> string
      = "n_get_numeral_decimal_string"

    external n_get_numerator : z3_context -> z3_ast -> z3_ast
      = "n_get_numerator"

    external n_get_denominator : z3_context -> z3_ast -> z3_ast
      = "n_get_denominator"

    external n_get_numeral_small : z3_context -> z3_ast -> (bool * int * int)
      = "n_get_numeral_small"

    external n_get_numeral_int : z3_context -> z3_ast -> (bool * int)
      = "n_get_numeral_int"

    external n_get_numeral_uint : z3_context -> z3_ast -> (bool * int)
      = "n_get_numeral_uint"

    external n_get_numeral_uint64 : z3_context -> z3_ast -> (bool * int)
      = "n_get_numeral_uint64"

    external n_get_numeral_int64 : z3_context -> z3_ast -> (bool * int)
      = "n_get_numeral_int64"

    external n_get_numeral_rational_int64 : z3_context -> z3_ast -> (bool * int * int)
      = "n_get_numeral_rational_int64"

    external n_get_algebraic_number_lower : z3_context -> z3_ast -> int -> z3_ast
      = "n_get_algebraic_number_lower"

    external n_get_algebraic_number_upper : z3_context -> z3_ast -> int -> z3_ast
      = "n_get_algebraic_number_upper"

    external n_pattern_to_ast : z3_context -> z3_pattern -> z3_ast
      = "n_pattern_to_ast"

    external n_get_pattern_num_terms : z3_context -> z3_pattern -> int
      = "n_get_pattern_num_terms"

    external n_get_pattern : z3_context -> z3_pattern -> int -> z3_ast
      = "n_get_pattern"

    external n_get_index_value : z3_context -> z3_ast -> int
      = "n_get_index_value"

    external n_is_quantifier_forall : z3_context -> z3_ast -> bool
      = "n_is_quantifier_forall"

    external n_get_quantifier_weight : z3_context -> z3_ast -> int
      = "n_get_quantifier_weight"

    external n_get_quantifier_num_patterns : z3_context -> z3_ast -> int
      = "n_get_quantifier_num_patterns"

    external n_get_quantifier_pattern_ast : z3_context -> z3_ast -> int -> z3_pattern
      = "n_get_quantifier_pattern_ast"

    external n_get_quantifier_num_no_patterns : z3_context -> z3_ast -> int
      = "n_get_quantifier_num_no_patterns"

    external n_get_quantifier_no_pattern_ast : z3_context -> z3_ast -> int -> z3_ast
      = "n_get_quantifier_no_pattern_ast"

    external n_get_quantifier_num_bound : z3_context -> z3_ast -> int
      = "n_get_quantifier_num_bound"

    external n_get_quantifier_bound_name : z3_context -> z3_ast -> int -> z3_symbol
      = "n_get_quantifier_bound_name"

    external n_get_quantifier_bound_sort : z3_context -> z3_ast -> int -> z3_sort
      = "n_get_quantifier_bound_sort"

    external n_get_quantifier_body : z3_context -> z3_ast -> z3_ast
      = "n_get_quantifier_body"

    external n_simplify : z3_context -> z3_ast -> z3_ast
      = "n_simplify"

    external n_simplify_ex : z3_context -> z3_ast -> z3_params -> z3_ast
      = "n_simplify_ex"

    external n_simplify_get_help : z3_context -> string
      = "n_simplify_get_help"

    external n_simplify_get_param_descrs : z3_context -> z3_param_descrs
      = "n_simplify_get_param_descrs"

    external n_update_term : z3_context -> z3_ast -> int -> z3_ast array -> z3_ast
      = "n_update_term"

    external n_substitute : z3_context -> z3_ast -> int -> z3_ast array -> z3_ast array -> z3_ast
      = "n_substitute"

    external n_substitute_vars : z3_context -> z3_ast -> int -> z3_ast array -> z3_ast
      = "n_substitute_vars"

    external n_translate : z3_context -> z3_ast -> z3_context -> z3_ast
      = "n_translate"

    external n_model_inc_ref : z3_context -> z3_model -> unit
      = "n_model_inc_ref"

    external n_model_dec_ref : z3_context -> z3_model -> unit
      = "n_model_dec_ref"

    external n_model_eval : z3_context -> z3_model -> z3_ast -> bool -> (bool * ptr)
      = "n_model_eval"

    external n_model_get_const_interp : z3_context -> z3_model -> z3_func_decl -> z3_ast
      = "n_model_get_const_interp"

    external n_model_get_func_interp : z3_context -> z3_model -> z3_func_decl -> z3_func_interp
      = "n_model_get_func_interp"

    external n_model_get_num_consts : z3_context -> z3_model -> int
      = "n_model_get_num_consts"

    external n_model_get_const_decl : z3_context -> z3_model -> int -> z3_func_decl
      = "n_model_get_const_decl"

    external n_model_get_num_funcs : z3_context -> z3_model -> int
      = "n_model_get_num_funcs"

    external n_model_get_func_decl : z3_context -> z3_model -> int -> z3_func_decl
      = "n_model_get_func_decl"

    external n_model_get_num_sorts : z3_context -> z3_model -> int
      = "n_model_get_num_sorts"

    external n_model_get_sort : z3_context -> z3_model -> int -> z3_sort
      = "n_model_get_sort"

    external n_model_get_sort_universe : z3_context -> z3_model -> z3_sort -> z3_ast_vector
      = "n_model_get_sort_universe"

    external n_is_as_array : z3_context -> z3_ast -> bool
      = "n_is_as_array"

    external n_get_as_array_func_decl : z3_context -> z3_ast -> z3_func_decl
      = "n_get_as_array_func_decl"

    external n_func_interp_inc_ref : z3_context -> z3_func_interp -> unit
      = "n_func_interp_inc_ref"

    external n_func_interp_dec_ref : z3_context -> z3_func_interp -> unit
      = "n_func_interp_dec_ref"

    external n_func_interp_get_num_entries : z3_context -> z3_func_interp -> int
      = "n_func_interp_get_num_entries"

    external n_func_interp_get_entry : z3_context -> z3_func_interp -> int -> z3_func_entry
      = "n_func_interp_get_entry"

    external n_func_interp_get_else : z3_context -> z3_func_interp -> z3_ast
      = "n_func_interp_get_else"

    external n_func_interp_get_arity : z3_context -> z3_func_interp -> int
      = "n_func_interp_get_arity"

    external n_func_entry_inc_ref : z3_context -> z3_func_entry -> unit
      = "n_func_entry_inc_ref"

    external n_func_entry_dec_ref : z3_context -> z3_func_entry -> unit
      = "n_func_entry_dec_ref"

    external n_func_entry_get_value : z3_context -> z3_func_entry -> z3_ast
      = "n_func_entry_get_value"

    external n_func_entry_get_num_args : z3_context -> z3_func_entry -> int
      = "n_func_entry_get_num_args"

    external n_func_entry_get_arg : z3_context -> z3_func_entry -> int -> z3_ast
      = "n_func_entry_get_arg"

    external n_open_log : string -> int
      = "n_open_log"

    external n_append_log : string -> unit
      = "n_append_log"

    external n_close_log :  unit -> unit
      = "n_close_log"

    external n_toggle_warning_messages : bool -> unit
      = "n_toggle_warning_messages"

    external n_set_ast_print_mode : z3_context -> int -> unit
      = "n_set_ast_print_mode"

    external n_ast_to_string : z3_context -> z3_ast -> string
      = "n_ast_to_string"

    external n_pattern_to_string : z3_context -> z3_pattern -> string
      = "n_pattern_to_string"

    external n_sort_to_string : z3_context -> z3_sort -> string
      = "n_sort_to_string"

    external n_func_decl_to_string : z3_context -> z3_func_decl -> string
      = "n_func_decl_to_string"

    external n_model_to_string : z3_context -> z3_model -> string
      = "n_model_to_string"

    external n_benchmark_to_smtlib_string : z3_context -> string -> string -> string -> string -> int -> z3_ast array -> z3_ast -> string
      = "n_benchmark_to_smtlib_string_bytecode"
        "n_benchmark_to_smtlib_string"

    external n_parse_smtlib2_string : z3_context -> string -> int -> z3_symbol array -> z3_sort array -> int -> z3_symbol array -> z3_func_decl array -> z3_ast
      = "n_parse_smtlib2_string_bytecode"
        "n_parse_smtlib2_string"

    external n_parse_smtlib2_file : z3_context -> string -> int -> z3_symbol array -> z3_sort array -> int -> z3_symbol array -> z3_func_decl array -> z3_ast
      = "n_parse_smtlib2_file_bytecode"
        "n_parse_smtlib2_file"

    external n_parse_smtlib_string : z3_context -> string -> int -> z3_symbol array -> z3_sort array -> int -> z3_symbol array -> z3_func_decl array -> unit
      = "n_parse_smtlib_string_bytecode"
        "n_parse_smtlib_string"

    external n_parse_smtlib_file : z3_context -> string -> int -> z3_symbol array -> z3_sort array -> int -> z3_symbol array -> z3_func_decl array -> unit
      = "n_parse_smtlib_file_bytecode"
        "n_parse_smtlib_file"

    external n_get_smtlib_num_formulas : z3_context -> int
      = "n_get_smtlib_num_formulas"

    external n_get_smtlib_formula : z3_context -> int -> z3_ast
      = "n_get_smtlib_formula"

    external n_get_smtlib_num_assumptions : z3_context -> int
      = "n_get_smtlib_num_assumptions"

    external n_get_smtlib_assumption : z3_context -> int -> z3_ast
      = "n_get_smtlib_assumption"

    external n_get_smtlib_num_decls : z3_context -> int
      = "n_get_smtlib_num_decls"

    external n_get_smtlib_decl : z3_context -> int -> z3_func_decl
      = "n_get_smtlib_decl"

    external n_get_smtlib_num_sorts : z3_context -> int
      = "n_get_smtlib_num_sorts"

    external n_get_smtlib_sort : z3_context -> int -> z3_sort
      = "n_get_smtlib_sort"

    external n_get_smtlib_error : z3_context -> string
      = "n_get_smtlib_error"

    external n_get_error_code : z3_context -> int
      = "n_get_error_code"

    external n_set_error : z3_context -> int -> unit
      = "n_set_error"

    external n_get_error_msg : int -> string
      = "n_get_error_msg"

    external n_get_error_msg_ex : z3_context -> int -> string
      = "n_get_error_msg_ex"

    external n_get_version :  unit -> (int * int * int * int)
      = "n_get_version"

    external n_enable_trace : string -> unit
      = "n_enable_trace"

    external n_disable_trace : string -> unit
      = "n_disable_trace"

    external n_reset_memory :  unit -> unit
      = "n_reset_memory"

    external n_mk_fixedpoint : z3_context -> z3_fixedpoint
      = "n_mk_fixedpoint"

    external n_fixedpoint_inc_ref : z3_context -> z3_fixedpoint -> unit
      = "n_fixedpoint_inc_ref"

    external n_fixedpoint_dec_ref : z3_context -> z3_fixedpoint -> unit
      = "n_fixedpoint_dec_ref"

    external n_fixedpoint_add_rule : z3_context -> z3_fixedpoint -> z3_ast -> z3_symbol -> unit
      = "n_fixedpoint_add_rule"

    external n_fixedpoint_add_fact : z3_context -> z3_fixedpoint -> z3_func_decl -> int -> int array -> unit
      = "n_fixedpoint_add_fact"

    external n_fixedpoint_assert : z3_context -> z3_fixedpoint -> z3_ast -> unit
      = "n_fixedpoint_assert"

    external n_fixedpoint_query : z3_context -> z3_fixedpoint -> z3_ast -> int
      = "n_fixedpoint_query"

    external n_fixedpoint_query_relations : z3_context -> z3_fixedpoint -> int -> z3_func_decl array -> int
      = "n_fixedpoint_query_relations"

    external n_fixedpoint_get_answer : z3_context -> z3_fixedpoint -> z3_ast
      = "n_fixedpoint_get_answer"

    external n_fixedpoint_get_reason_unknown : z3_context -> z3_fixedpoint -> string
      = "n_fixedpoint_get_reason_unknown"

    external n_fixedpoint_update_rule : z3_context -> z3_fixedpoint -> z3_ast -> z3_symbol -> unit
      = "n_fixedpoint_update_rule"

    external n_fixedpoint_get_num_levels : z3_context -> z3_fixedpoint -> z3_func_decl -> int
      = "n_fixedpoint_get_num_levels"

    external n_fixedpoint_get_cover_delta : z3_context -> z3_fixedpoint -> int -> z3_func_decl -> z3_ast
      = "n_fixedpoint_get_cover_delta"

    external n_fixedpoint_add_cover : z3_context -> z3_fixedpoint -> int -> z3_func_decl -> z3_ast -> unit
      = "n_fixedpoint_add_cover"

    external n_fixedpoint_get_statistics : z3_context -> z3_fixedpoint -> z3_stats
      = "n_fixedpoint_get_statistics"

    external n_fixedpoint_register_relation : z3_context -> z3_fixedpoint -> z3_func_decl -> unit
      = "n_fixedpoint_register_relation"

    external n_fixedpoint_set_predicate_representation : z3_context -> z3_fixedpoint -> z3_func_decl -> int -> z3_symbol array -> unit
      = "n_fixedpoint_set_predicate_representation"

    external n_fixedpoint_get_rules : z3_context -> z3_fixedpoint -> z3_ast_vector
      = "n_fixedpoint_get_rules"

    external n_fixedpoint_get_assertions : z3_context -> z3_fixedpoint -> z3_ast_vector
      = "n_fixedpoint_get_assertions"

    external n_fixedpoint_set_params : z3_context -> z3_fixedpoint -> z3_params -> unit
      = "n_fixedpoint_set_params"

    external n_fixedpoint_get_help : z3_context -> z3_fixedpoint -> string
      = "n_fixedpoint_get_help"

    external n_fixedpoint_get_param_descrs : z3_context -> z3_fixedpoint -> z3_param_descrs
      = "n_fixedpoint_get_param_descrs"

    external n_fixedpoint_to_string : z3_context -> z3_fixedpoint -> int -> z3_ast array -> string
      = "n_fixedpoint_to_string"

    external n_fixedpoint_from_string : z3_context -> z3_fixedpoint -> string -> z3_ast_vector
      = "n_fixedpoint_from_string"

    external n_fixedpoint_from_file : z3_context -> z3_fixedpoint -> string -> z3_ast_vector
      = "n_fixedpoint_from_file"

    external n_fixedpoint_push : z3_context -> z3_fixedpoint -> unit
      = "n_fixedpoint_push"

    external n_fixedpoint_pop : z3_context -> z3_fixedpoint -> unit
      = "n_fixedpoint_pop"

    external n_mk_ast_vector : z3_context -> z3_ast_vector
      = "n_mk_ast_vector"

    external n_ast_vector_inc_ref : z3_context -> z3_ast_vector -> unit
      = "n_ast_vector_inc_ref"

    external n_ast_vector_dec_ref : z3_context -> z3_ast_vector -> unit
      = "n_ast_vector_dec_ref"

    external n_ast_vector_size : z3_context -> z3_ast_vector -> int
      = "n_ast_vector_size"

    external n_ast_vector_get : z3_context -> z3_ast_vector -> int -> z3_ast
      = "n_ast_vector_get"

    external n_ast_vector_set : z3_context -> z3_ast_vector -> int -> z3_ast -> unit
      = "n_ast_vector_set"

    external n_ast_vector_resize : z3_context -> z3_ast_vector -> int -> unit
      = "n_ast_vector_resize"

    external n_ast_vector_push : z3_context -> z3_ast_vector -> z3_ast -> unit
      = "n_ast_vector_push"

    external n_ast_vector_translate : z3_context -> z3_ast_vector -> z3_context -> z3_ast_vector
      = "n_ast_vector_translate"

    external n_ast_vector_to_string : z3_context -> z3_ast_vector -> string
      = "n_ast_vector_to_string"

    external n_mk_ast_map : z3_context -> z3_ast_map
      = "n_mk_ast_map"

    external n_ast_map_inc_ref : z3_context -> z3_ast_map -> unit
      = "n_ast_map_inc_ref"

    external n_ast_map_dec_ref : z3_context -> z3_ast_map -> unit
      = "n_ast_map_dec_ref"

    external n_ast_map_contains : z3_context -> z3_ast_map -> z3_ast -> bool
      = "n_ast_map_contains"

    external n_ast_map_find : z3_context -> z3_ast_map -> z3_ast -> z3_ast
      = "n_ast_map_find"

    external n_ast_map_insert : z3_context -> z3_ast_map -> z3_ast -> z3_ast -> unit
      = "n_ast_map_insert"

    external n_ast_map_erase : z3_context -> z3_ast_map -> z3_ast -> unit
      = "n_ast_map_erase"

    external n_ast_map_reset : z3_context -> z3_ast_map -> unit
      = "n_ast_map_reset"

    external n_ast_map_size : z3_context -> z3_ast_map -> int
      = "n_ast_map_size"

    external n_ast_map_keys : z3_context -> z3_ast_map -> z3_ast_vector
      = "n_ast_map_keys"

    external n_ast_map_to_string : z3_context -> z3_ast_map -> string
      = "n_ast_map_to_string"

    external n_mk_goal : z3_context -> bool -> bool -> bool -> z3_goal
      = "n_mk_goal"

    external n_goal_inc_ref : z3_context -> z3_goal -> unit
      = "n_goal_inc_ref"

    external n_goal_dec_ref : z3_context -> z3_goal -> unit
      = "n_goal_dec_ref"

    external n_goal_precision : z3_context -> z3_goal -> int
      = "n_goal_precision"

    external n_goal_assert : z3_context -> z3_goal -> z3_ast -> unit
      = "n_goal_assert"

    external n_goal_inconsistent : z3_context -> z3_goal -> bool
      = "n_goal_inconsistent"

    external n_goal_depth : z3_context -> z3_goal -> int
      = "n_goal_depth"

    external n_goal_reset : z3_context -> z3_goal -> unit
      = "n_goal_reset"

    external n_goal_size : z3_context -> z3_goal -> int
      = "n_goal_size"

    external n_goal_formula : z3_context -> z3_goal -> int -> z3_ast
      = "n_goal_formula"

    external n_goal_num_exprs : z3_context -> z3_goal -> int
      = "n_goal_num_exprs"

    external n_goal_is_decided_sat : z3_context -> z3_goal -> bool
      = "n_goal_is_decided_sat"

    external n_goal_is_decided_unsat : z3_context -> z3_goal -> bool
      = "n_goal_is_decided_unsat"

    external n_goal_translate : z3_context -> z3_goal -> z3_context -> z3_goal
      = "n_goal_translate"

    external n_goal_to_string : z3_context -> z3_goal -> string
      = "n_goal_to_string"

    external n_mk_tactic : z3_context -> string -> z3_tactic
      = "n_mk_tactic"

    external n_tactic_inc_ref : z3_context -> z3_tactic -> unit
      = "n_tactic_inc_ref"

    external n_tactic_dec_ref : z3_context -> z3_tactic -> unit
      = "n_tactic_dec_ref"

    external n_mk_probe : z3_context -> string -> z3_probe
      = "n_mk_probe"

    external n_probe_inc_ref : z3_context -> z3_probe -> unit
      = "n_probe_inc_ref"

    external n_probe_dec_ref : z3_context -> z3_probe -> unit
      = "n_probe_dec_ref"

    external n_tactic_and_then : z3_context -> z3_tactic -> z3_tactic -> z3_tactic
      = "n_tactic_and_then"

    external n_tactic_or_else : z3_context -> z3_tactic -> z3_tactic -> z3_tactic
      = "n_tactic_or_else"

    external n_tactic_par_or : z3_context -> int -> z3_tactic array -> z3_tactic
      = "n_tactic_par_or"

    external n_tactic_par_and_then : z3_context -> z3_tactic -> z3_tactic -> z3_tactic
      = "n_tactic_par_and_then"

    external n_tactic_try_for : z3_context -> z3_tactic -> int -> z3_tactic
      = "n_tactic_try_for"

    external n_tactic_when : z3_context -> z3_probe -> z3_tactic -> z3_tactic
      = "n_tactic_when"

    external n_tactic_cond : z3_context -> z3_probe -> z3_tactic -> z3_tactic -> z3_tactic
      = "n_tactic_cond"

    external n_tactic_repeat : z3_context -> z3_tactic -> int -> z3_tactic
      = "n_tactic_repeat"

    external n_tactic_skip : z3_context -> z3_tactic
      = "n_tactic_skip"

    external n_tactic_fail : z3_context -> z3_tactic
      = "n_tactic_fail"

    external n_tactic_fail_if : z3_context -> z3_probe -> z3_tactic
      = "n_tactic_fail_if"

    external n_tactic_fail_if_not_decided : z3_context -> z3_tactic
      = "n_tactic_fail_if_not_decided"

    external n_tactic_using_params : z3_context -> z3_tactic -> z3_params -> z3_tactic
      = "n_tactic_using_params"

    external n_probe_const : z3_context -> float -> z3_probe
      = "n_probe_const"

    external n_probe_lt : z3_context -> z3_probe -> z3_probe -> z3_probe
      = "n_probe_lt"

    external n_probe_gt : z3_context -> z3_probe -> z3_probe -> z3_probe
      = "n_probe_gt"

    external n_probe_le : z3_context -> z3_probe -> z3_probe -> z3_probe
      = "n_probe_le"

    external n_probe_ge : z3_context -> z3_probe -> z3_probe -> z3_probe
      = "n_probe_ge"

    external n_probe_eq : z3_context -> z3_probe -> z3_probe -> z3_probe
      = "n_probe_eq"

    external n_probe_and : z3_context -> z3_probe -> z3_probe -> z3_probe
      = "n_probe_and"

    external n_probe_or : z3_context -> z3_probe -> z3_probe -> z3_probe
      = "n_probe_or"

    external n_probe_not : z3_context -> z3_probe -> z3_probe
      = "n_probe_not"

    external n_get_num_tactics : z3_context -> int
      = "n_get_num_tactics"

    external n_get_tactic_name : z3_context -> int -> string
      = "n_get_tactic_name"

    external n_get_num_probes : z3_context -> int
      = "n_get_num_probes"

    external n_get_probe_name : z3_context -> int -> string
      = "n_get_probe_name"

    external n_tactic_get_help : z3_context -> z3_tactic -> string
      = "n_tactic_get_help"

    external n_tactic_get_param_descrs : z3_context -> z3_tactic -> z3_param_descrs
      = "n_tactic_get_param_descrs"

    external n_tactic_get_descr : z3_context -> string -> string
      = "n_tactic_get_descr"

    external n_probe_get_descr : z3_context -> string -> string
      = "n_probe_get_descr"

    external n_probe_apply : z3_context -> z3_probe -> z3_goal -> float
      = "n_probe_apply"

    external n_tactic_apply : z3_context -> z3_tactic -> z3_goal -> z3_apply_result
      = "n_tactic_apply"

    external n_tactic_apply_ex : z3_context -> z3_tactic -> z3_goal -> z3_params -> z3_apply_result
      = "n_tactic_apply_ex"

    external n_apply_result_inc_ref : z3_context -> z3_apply_result -> unit
      = "n_apply_result_inc_ref"

    external n_apply_result_dec_ref : z3_context -> z3_apply_result -> unit
      = "n_apply_result_dec_ref"

    external n_apply_result_to_string : z3_context -> z3_apply_result -> string
      = "n_apply_result_to_string"

    external n_apply_result_get_num_subgoals : z3_context -> z3_apply_result -> int
      = "n_apply_result_get_num_subgoals"

    external n_apply_result_get_subgoal : z3_context -> z3_apply_result -> int -> z3_goal
      = "n_apply_result_get_subgoal"

    external n_apply_result_convert_model : z3_context -> z3_apply_result -> int -> z3_model -> z3_model
      = "n_apply_result_convert_model"

    external n_mk_solver : z3_context -> z3_solver
      = "n_mk_solver"

    external n_mk_simple_solver : z3_context -> z3_solver
      = "n_mk_simple_solver"

    external n_mk_solver_for_logic : z3_context -> z3_symbol -> z3_solver
      = "n_mk_solver_for_logic"

    external n_mk_solver_from_tactic : z3_context -> z3_tactic -> z3_solver
      = "n_mk_solver_from_tactic"

    external n_solver_get_help : z3_context -> z3_solver -> string
      = "n_solver_get_help"

    external n_solver_get_param_descrs : z3_context -> z3_solver -> z3_param_descrs
      = "n_solver_get_param_descrs"

    external n_solver_set_params : z3_context -> z3_solver -> z3_params -> unit
      = "n_solver_set_params"

    external n_solver_inc_ref : z3_context -> z3_solver -> unit
      = "n_solver_inc_ref"

    external n_solver_dec_ref : z3_context -> z3_solver -> unit
      = "n_solver_dec_ref"

    external n_solver_push : z3_context -> z3_solver -> unit
      = "n_solver_push"

    external n_solver_pop : z3_context -> z3_solver -> int -> unit
      = "n_solver_pop"

    external n_solver_reset : z3_context -> z3_solver -> unit
      = "n_solver_reset"

    external n_solver_get_num_scopes : z3_context -> z3_solver -> int
      = "n_solver_get_num_scopes"

    external n_solver_assert : z3_context -> z3_solver -> z3_ast -> unit
      = "n_solver_assert"

    external n_solver_assert_and_track : z3_context -> z3_solver -> z3_ast -> z3_ast -> unit
      = "n_solver_assert_and_track"

    external n_solver_get_assertions : z3_context -> z3_solver -> z3_ast_vector
      = "n_solver_get_assertions"

    external n_solver_check : z3_context -> z3_solver -> int
      = "n_solver_check"

    external n_solver_check_assumptions : z3_context -> z3_solver -> int -> z3_ast array -> int
      = "n_solver_check_assumptions"

    external n_solver_get_model : z3_context -> z3_solver -> z3_model
      = "n_solver_get_model"

    external n_solver_get_proof : z3_context -> z3_solver -> z3_ast
      = "n_solver_get_proof"

    external n_solver_get_unsat_core : z3_context -> z3_solver -> z3_ast_vector
      = "n_solver_get_unsat_core"

    external n_solver_get_reason_unknown : z3_context -> z3_solver -> string
      = "n_solver_get_reason_unknown"

    external n_solver_get_statistics : z3_context -> z3_solver -> z3_stats
      = "n_solver_get_statistics"

    external n_solver_to_string : z3_context -> z3_solver -> string
      = "n_solver_to_string"

    external n_stats_to_string : z3_context -> z3_stats -> string
      = "n_stats_to_string"

    external n_stats_inc_ref : z3_context -> z3_stats -> unit
      = "n_stats_inc_ref"

    external n_stats_dec_ref : z3_context -> z3_stats -> unit
      = "n_stats_dec_ref"

    external n_stats_size : z3_context -> z3_stats -> int
      = "n_stats_size"

    external n_stats_get_key : z3_context -> z3_stats -> int -> string
      = "n_stats_get_key"

    external n_stats_is_uint : z3_context -> z3_stats -> int -> bool
      = "n_stats_is_uint"

    external n_stats_is_double : z3_context -> z3_stats -> int -> bool
      = "n_stats_is_double"

    external n_stats_get_uint_value : z3_context -> z3_stats -> int -> int
      = "n_stats_get_uint_value"

    external n_stats_get_double_value : z3_context -> z3_stats -> int -> float
      = "n_stats_get_double_value"

    external n_mk_injective_function : z3_context -> z3_symbol -> int -> z3_sort array -> z3_sort -> z3_func_decl
      = "n_mk_injective_function"

    external n_set_logic : z3_context -> string -> unit
      = "n_set_logic"

    external n_push : z3_context -> unit
      = "n_push"

    external n_pop : z3_context -> int -> unit
      = "n_pop"

    external n_get_num_scopes : z3_context -> int
      = "n_get_num_scopes"

    external n_persist_ast : z3_context -> z3_ast -> int -> unit
      = "n_persist_ast"

    external n_assert_cnstr : z3_context -> z3_ast -> unit
      = "n_assert_cnstr"

    external n_check_and_get_model : z3_context -> (int * ptr)
      = "n_check_and_get_model"

    external n_check : z3_context -> int
      = "n_check"

    external n_check_assumptions : z3_context -> int -> z3_ast array -> (int * ptr * ptr * int * z3_ast array)
      = "n_check_assumptions"

    external n_get_implied_equalities : z3_context -> z3_solver -> int -> z3_ast array -> (int * int array)
      = "n_get_implied_equalities"

    external n_del_model : z3_context -> z3_model -> unit
      = "n_del_model"

    external n_soft_check_cancel : z3_context -> unit
      = "n_soft_check_cancel"

    external n_get_search_failure : z3_context -> int
      = "n_get_search_failure"

    external n_mk_label : z3_context -> z3_symbol -> bool -> z3_ast -> z3_ast
      = "n_mk_label"

    external n_get_relevant_labels : z3_context -> z3_literals
      = "n_get_relevant_labels"

    external n_get_relevant_literals : z3_context -> z3_literals
      = "n_get_relevant_literals"

    external n_get_guessed_literals : z3_context -> z3_literals
      = "n_get_guessed_literals"

    external n_del_literals : z3_context -> z3_literals -> unit
      = "n_del_literals"

    external n_get_num_literals : z3_context -> z3_literals -> int
      = "n_get_num_literals"

    external n_get_label_symbol : z3_context -> z3_literals -> int -> z3_symbol
      = "n_get_label_symbol"

    external n_get_literal : z3_context -> z3_literals -> int -> z3_ast
      = "n_get_literal"

    external n_disable_literal : z3_context -> z3_literals -> int -> unit
      = "n_disable_literal"

    external n_block_literals : z3_context -> z3_literals -> unit
      = "n_block_literals"

    external n_get_model_num_constants : z3_context -> z3_model -> int
      = "n_get_model_num_constants"

    external n_get_model_constant : z3_context -> z3_model -> int -> z3_func_decl
      = "n_get_model_constant"

    external n_get_model_num_funcs : z3_context -> z3_model -> int
      = "n_get_model_num_funcs"

    external n_get_model_func_decl : z3_context -> z3_model -> int -> z3_func_decl
      = "n_get_model_func_decl"

    external n_eval_func_decl : z3_context -> z3_model -> z3_func_decl -> (bool * ptr)
      = "n_eval_func_decl"

    external n_is_array_value : z3_context -> z3_model -> z3_ast -> (bool * int)
      = "n_is_array_value"

    external n_get_array_value : z3_context -> z3_model -> z3_ast -> int -> (z3_ast array * z3_ast array * ptr)
      = "n_get_array_value"

    external n_get_model_func_else : z3_context -> z3_model -> int -> z3_ast
      = "n_get_model_func_else"

    external n_get_model_func_num_entries : z3_context -> z3_model -> int -> int
      = "n_get_model_func_num_entries"

    external n_get_model_func_entry_num_args : z3_context -> z3_model -> int -> int -> int
      = "n_get_model_func_entry_num_args"

    external n_get_model_func_entry_arg : z3_context -> z3_model -> int -> int -> int -> z3_ast
      = "n_get_model_func_entry_arg"

    external n_get_model_func_entry_value : z3_context -> z3_model -> int -> int -> z3_ast
      = "n_get_model_func_entry_value"

    external n_eval : z3_context -> z3_model -> z3_ast -> (bool * ptr)
      = "n_eval"

    external n_eval_decl : z3_context -> z3_model -> z3_func_decl -> int -> z3_ast array -> (bool * ptr)
      = "n_eval_decl"

    external n_context_to_string : z3_context -> string
      = "n_context_to_string"

    external n_statistics_to_string : z3_context -> string
      = "n_statistics_to_string"

    external n_get_context_assignment : z3_context -> z3_ast
      = "n_get_context_assignment"

    external n_mk_interpolation_context : z3_config -> z3_context
      = "n_mk_interpolation_context"

    external n_interpolation_profile : z3_context -> string
      = "n_interpolation_profile"

    external n_algebraic_is_value : z3_context -> z3_ast -> bool
      = "n_algebraic_is_value"

    external n_algebraic_is_pos : z3_context -> z3_ast -> bool
      = "n_algebraic_is_pos"

    external n_algebraic_is_neg : z3_context -> z3_ast -> bool
      = "n_algebraic_is_neg"

    external n_algebraic_is_zero : z3_context -> z3_ast -> bool
      = "n_algebraic_is_zero"

    external n_algebraic_sign : z3_context -> z3_ast -> int
      = "n_algebraic_sign"

    external n_algebraic_add : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_algebraic_add"

    external n_algebraic_sub : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_algebraic_sub"

    external n_algebraic_mul : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_algebraic_mul"

    external n_algebraic_div : z3_context -> z3_ast -> z3_ast -> z3_ast
      = "n_algebraic_div"

    external n_algebraic_root : z3_context -> z3_ast -> int -> z3_ast
      = "n_algebraic_root"

    external n_algebraic_power : z3_context -> z3_ast -> int -> z3_ast
      = "n_algebraic_power"

    external n_algebraic_lt : z3_context -> z3_ast -> z3_ast -> bool
      = "n_algebraic_lt"

    external n_algebraic_gt : z3_context -> z3_ast -> z3_ast -> bool
      = "n_algebraic_gt"

    external n_algebraic_le : z3_context -> z3_ast -> z3_ast -> bool
      = "n_algebraic_le"

    external n_algebraic_ge : z3_context -> z3_ast -> z3_ast -> bool
      = "n_algebraic_ge"

    external n_algebraic_eq : z3_context -> z3_ast -> z3_ast -> bool
      = "n_algebraic_eq"

    external n_algebraic_neq : z3_context -> z3_ast -> z3_ast -> bool
      = "n_algebraic_neq"

    external n_algebraic_roots : z3_context -> z3_ast -> int -> z3_ast array -> z3_ast_vector
      = "n_algebraic_roots"

    external n_algebraic_eval : z3_context -> z3_ast -> int -> z3_ast array -> int
      = "n_algebraic_eval"

    external n_polynomial_subresultants : z3_context -> z3_ast -> z3_ast -> z3_ast -> z3_ast_vector
      = "n_polynomial_subresultants"

    external n_rcf_del : z3_context -> z3_rcf_num -> unit
      = "n_rcf_del"

    external n_rcf_mk_rational : z3_context -> string -> z3_rcf_num
      = "n_rcf_mk_rational"

    external n_rcf_mk_small_int : z3_context -> int -> z3_rcf_num
      = "n_rcf_mk_small_int"

    external n_rcf_mk_pi : z3_context -> z3_rcf_num
      = "n_rcf_mk_pi"

    external n_rcf_mk_e : z3_context -> z3_rcf_num
      = "n_rcf_mk_e"

    external n_rcf_mk_infinitesimal : z3_context -> z3_rcf_num
      = "n_rcf_mk_infinitesimal"

    external n_rcf_mk_roots : z3_context -> int -> z3_rcf_num array -> (int * z3_rcf_num array)
      = "n_rcf_mk_roots"

    external n_rcf_add : z3_context -> z3_rcf_num -> z3_rcf_num -> z3_rcf_num
      = "n_rcf_add"

    external n_rcf_sub : z3_context -> z3_rcf_num -> z3_rcf_num -> z3_rcf_num
      = "n_rcf_sub"

    external n_rcf_mul : z3_context -> z3_rcf_num -> z3_rcf_num -> z3_rcf_num
      = "n_rcf_mul"

    external n_rcf_div : z3_context -> z3_rcf_num -> z3_rcf_num -> z3_rcf_num
      = "n_rcf_div"

    external n_rcf_neg : z3_context -> z3_rcf_num -> z3_rcf_num
      = "n_rcf_neg"

    external n_rcf_inv : z3_context -> z3_rcf_num -> z3_rcf_num
      = "n_rcf_inv"

    external n_rcf_power : z3_context -> z3_rcf_num -> int -> z3_rcf_num
      = "n_rcf_power"

    external n_rcf_lt : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
      = "n_rcf_lt"

    external n_rcf_gt : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
      = "n_rcf_gt"

    external n_rcf_le : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
      = "n_rcf_le"

    external n_rcf_ge : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
      = "n_rcf_ge"

    external n_rcf_eq : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
      = "n_rcf_eq"

    external n_rcf_neq : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
      = "n_rcf_neq"

    external n_rcf_num_to_string : z3_context -> z3_rcf_num -> bool -> bool -> string
      = "n_rcf_num_to_string"

    external n_rcf_num_to_decimal_string : z3_context -> z3_rcf_num -> int -> string
      = "n_rcf_num_to_decimal_string"

    external n_rcf_get_numerator_denominator : z3_context -> z3_rcf_num -> (ptr * ptr)
      = "n_rcf_get_numerator_denominator"

  end

  let global_param_set a0 a1 = 
    let _ = (ML2C.n_global_param_set a0 a1) in
        ()

  let global_param_reset_all () = 
    let _ = (ML2C.n_global_param_reset_all ()) in
        ()

  let global_param_get a0 = 
    let res = (ML2C.n_global_param_get a0) in
        res

  let mk_config () = 
    let res = (ML2C.n_mk_config ()) in
        res

  let del_config a0 = 
    let _ = (ML2C.n_del_config a0) in
        ()

  let set_param_value a0 a1 a2 = 
    let _ = (ML2C.n_set_param_value a0 a1 a2) in
        ()

  let mk_context a0 = 
    let res = (ML2C.n_mk_context a0) in
        res

  let mk_context_rc a0 = 
    let res = (ML2C.n_mk_context_rc a0) in
        res

  let del_context a0 = 
    let _ = (ML2C.n_del_context a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let inc_ref a0 a1 = 
    let _ = (ML2C.n_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let dec_ref a0 a1 = 
    let _ = (ML2C.n_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let update_param_value a0 a1 a2 = 
    let _ = (ML2C.n_update_param_value a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let get_param_value a0 a1 = 
    let res = (ML2C.n_get_param_value a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let interrupt a0 = 
    let _ = (ML2C.n_interrupt a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let mk_params a0 = 
    let res = (ML2C.n_mk_params a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let params_inc_ref a0 a1 = 
    let _ = (ML2C.n_params_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let params_dec_ref a0 a1 = 
    let _ = (ML2C.n_params_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let params_set_bool a0 a1 a2 a3 = 
    let _ = (ML2C.n_params_set_bool a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let params_set_uint a0 a1 a2 a3 = 
    let _ = (ML2C.n_params_set_uint a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let params_set_double a0 a1 a2 a3 = 
    let _ = (ML2C.n_params_set_double a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let params_set_symbol a0 a1 a2 a3 = 
    let _ = (ML2C.n_params_set_symbol a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let params_to_string a0 a1 = 
    let res = (ML2C.n_params_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let params_validate a0 a1 a2 = 
    let _ = (ML2C.n_params_validate a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let param_descrs_inc_ref a0 a1 = 
    let _ = (ML2C.n_param_descrs_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let param_descrs_dec_ref a0 a1 = 
    let _ = (ML2C.n_param_descrs_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let param_descrs_get_kind a0 a1 a2 = 
    let res = (ML2C.n_param_descrs_get_kind a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let param_descrs_size a0 a1 = 
    let res = (ML2C.n_param_descrs_size a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let param_descrs_get_name a0 a1 a2 = 
    let res = (ML2C.n_param_descrs_get_name a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let param_descrs_to_string a0 a1 = 
    let res = (ML2C.n_param_descrs_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_int_symbol a0 a1 = 
    let res = (ML2C.n_mk_int_symbol a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_string_symbol a0 a1 = 
    let res = (ML2C.n_mk_string_symbol a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_uninterpreted_sort a0 a1 = 
    let res = (ML2C.n_mk_uninterpreted_sort a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bool_sort a0 = 
    let res = (ML2C.n_mk_bool_sort a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_int_sort a0 = 
    let res = (ML2C.n_mk_int_sort a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_real_sort a0 = 
    let res = (ML2C.n_mk_real_sort a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bv_sort a0 a1 = 
    let res = (ML2C.n_mk_bv_sort a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_finite_domain_sort a0 a1 a2 = 
    let res = (ML2C.n_mk_finite_domain_sort a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_array_sort a0 a1 a2 = 
    let res = (ML2C.n_mk_array_sort a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_tuple_sort a0 a1 a2 a3 a4 = 
    let res = (ML2C.n_mk_tuple_sort a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_enumeration_sort a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_enumeration_sort a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_list_sort a0 a1 a2 = 
    let res = (ML2C.n_mk_list_sort a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_constructor a0 a1 a2 a3 a4 a5 a6 = 
    let res = (ML2C.n_mk_constructor a0 a1 a2 a3 a4 a5 a6) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let del_constructor a0 a1 = 
    let _ = (ML2C.n_del_constructor a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let mk_datatype a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_datatype a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_constructor_list a0 a1 a2 = 
    let res = (ML2C.n_mk_constructor_list a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let del_constructor_list a0 a1 = 
    let _ = (ML2C.n_del_constructor_list a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let mk_datatypes a0 a1 a2 a4 = 
    let res = (ML2C.n_mk_datatypes a0 a1 a2 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let query_constructor a0 a1 a2 = 
    let res = (ML2C.n_query_constructor a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_func_decl a0 a1 a2 a3 a4 = 
    let res = (ML2C.n_mk_func_decl a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_app a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_app a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_const a0 a1 a2 = 
    let res = (ML2C.n_mk_const a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_fresh_func_decl a0 a1 a2 a3 a4 = 
    let res = (ML2C.n_mk_fresh_func_decl a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_fresh_const a0 a1 a2 = 
    let res = (ML2C.n_mk_fresh_const a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_true a0 = 
    let res = (ML2C.n_mk_true a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_false a0 = 
    let res = (ML2C.n_mk_false a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_eq a0 a1 a2 = 
    let res = (ML2C.n_mk_eq a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_distinct a0 a1 a2 = 
    let res = (ML2C.n_mk_distinct a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_not a0 a1 = 
    let res = (ML2C.n_mk_not a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_interp a0 a1 = 
    let res = (ML2C.n_mk_interp a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_ite a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_ite a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_iff a0 a1 a2 = 
    let res = (ML2C.n_mk_iff a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_implies a0 a1 a2 = 
    let res = (ML2C.n_mk_implies a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_xor a0 a1 a2 = 
    let res = (ML2C.n_mk_xor a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_and a0 a1 a2 = 
    let res = (ML2C.n_mk_and a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_or a0 a1 a2 = 
    let res = (ML2C.n_mk_or a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_add a0 a1 a2 = 
    let res = (ML2C.n_mk_add a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_mul a0 a1 a2 = 
    let res = (ML2C.n_mk_mul a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_sub a0 a1 a2 = 
    let res = (ML2C.n_mk_sub a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_unary_minus a0 a1 = 
    let res = (ML2C.n_mk_unary_minus a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_div a0 a1 a2 = 
    let res = (ML2C.n_mk_div a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_mod a0 a1 a2 = 
    let res = (ML2C.n_mk_mod a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_rem a0 a1 a2 = 
    let res = (ML2C.n_mk_rem a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_power a0 a1 a2 = 
    let res = (ML2C.n_mk_power a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_lt a0 a1 a2 = 
    let res = (ML2C.n_mk_lt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_le a0 a1 a2 = 
    let res = (ML2C.n_mk_le a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_gt a0 a1 a2 = 
    let res = (ML2C.n_mk_gt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_ge a0 a1 a2 = 
    let res = (ML2C.n_mk_ge a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_int2real a0 a1 = 
    let res = (ML2C.n_mk_int2real a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_real2int a0 a1 = 
    let res = (ML2C.n_mk_real2int a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_is_int a0 a1 = 
    let res = (ML2C.n_mk_is_int a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvnot a0 a1 = 
    let res = (ML2C.n_mk_bvnot a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvredand a0 a1 = 
    let res = (ML2C.n_mk_bvredand a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvredor a0 a1 = 
    let res = (ML2C.n_mk_bvredor a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvand a0 a1 a2 = 
    let res = (ML2C.n_mk_bvand a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvor a0 a1 a2 = 
    let res = (ML2C.n_mk_bvor a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvxor a0 a1 a2 = 
    let res = (ML2C.n_mk_bvxor a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvnand a0 a1 a2 = 
    let res = (ML2C.n_mk_bvnand a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvnor a0 a1 a2 = 
    let res = (ML2C.n_mk_bvnor a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvxnor a0 a1 a2 = 
    let res = (ML2C.n_mk_bvxnor a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvneg a0 a1 = 
    let res = (ML2C.n_mk_bvneg a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvadd a0 a1 a2 = 
    let res = (ML2C.n_mk_bvadd a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsub a0 a1 a2 = 
    let res = (ML2C.n_mk_bvsub a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvmul a0 a1 a2 = 
    let res = (ML2C.n_mk_bvmul a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvudiv a0 a1 a2 = 
    let res = (ML2C.n_mk_bvudiv a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsdiv a0 a1 a2 = 
    let res = (ML2C.n_mk_bvsdiv a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvurem a0 a1 a2 = 
    let res = (ML2C.n_mk_bvurem a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsrem a0 a1 a2 = 
    let res = (ML2C.n_mk_bvsrem a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsmod a0 a1 a2 = 
    let res = (ML2C.n_mk_bvsmod a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvult a0 a1 a2 = 
    let res = (ML2C.n_mk_bvult a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvslt a0 a1 a2 = 
    let res = (ML2C.n_mk_bvslt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvule a0 a1 a2 = 
    let res = (ML2C.n_mk_bvule a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsle a0 a1 a2 = 
    let res = (ML2C.n_mk_bvsle a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvuge a0 a1 a2 = 
    let res = (ML2C.n_mk_bvuge a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsge a0 a1 a2 = 
    let res = (ML2C.n_mk_bvsge a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvugt a0 a1 a2 = 
    let res = (ML2C.n_mk_bvugt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsgt a0 a1 a2 = 
    let res = (ML2C.n_mk_bvsgt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_concat a0 a1 a2 = 
    let res = (ML2C.n_mk_concat a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_extract a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_extract a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_sign_ext a0 a1 a2 = 
    let res = (ML2C.n_mk_sign_ext a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_zero_ext a0 a1 a2 = 
    let res = (ML2C.n_mk_zero_ext a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_repeat a0 a1 a2 = 
    let res = (ML2C.n_mk_repeat a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvshl a0 a1 a2 = 
    let res = (ML2C.n_mk_bvshl a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvlshr a0 a1 a2 = 
    let res = (ML2C.n_mk_bvlshr a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvashr a0 a1 a2 = 
    let res = (ML2C.n_mk_bvashr a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_rotate_left a0 a1 a2 = 
    let res = (ML2C.n_mk_rotate_left a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_rotate_right a0 a1 a2 = 
    let res = (ML2C.n_mk_rotate_right a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_ext_rotate_left a0 a1 a2 = 
    let res = (ML2C.n_mk_ext_rotate_left a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_ext_rotate_right a0 a1 a2 = 
    let res = (ML2C.n_mk_ext_rotate_right a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_int2bv a0 a1 a2 = 
    let res = (ML2C.n_mk_int2bv a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bv2int a0 a1 a2 = 
    let res = (ML2C.n_mk_bv2int a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvadd_no_overflow a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_bvadd_no_overflow a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvadd_no_underflow a0 a1 a2 = 
    let res = (ML2C.n_mk_bvadd_no_underflow a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsub_no_overflow a0 a1 a2 = 
    let res = (ML2C.n_mk_bvsub_no_overflow a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsub_no_underflow a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_bvsub_no_underflow a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvsdiv_no_overflow a0 a1 a2 = 
    let res = (ML2C.n_mk_bvsdiv_no_overflow a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvneg_no_overflow a0 a1 = 
    let res = (ML2C.n_mk_bvneg_no_overflow a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvmul_no_overflow a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_bvmul_no_overflow a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bvmul_no_underflow a0 a1 a2 = 
    let res = (ML2C.n_mk_bvmul_no_underflow a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_select a0 a1 a2 = 
    let res = (ML2C.n_mk_select a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_store a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_store a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_const_array a0 a1 a2 = 
    let res = (ML2C.n_mk_const_array a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_map a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_map a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_array_default a0 a1 = 
    let res = (ML2C.n_mk_array_default a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_set_sort a0 a1 = 
    let res = (ML2C.n_mk_set_sort a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_empty_set a0 a1 = 
    let res = (ML2C.n_mk_empty_set a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_full_set a0 a1 = 
    let res = (ML2C.n_mk_full_set a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_set_add a0 a1 a2 = 
    let res = (ML2C.n_mk_set_add a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_set_del a0 a1 a2 = 
    let res = (ML2C.n_mk_set_del a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_set_union a0 a1 a2 = 
    let res = (ML2C.n_mk_set_union a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_set_intersect a0 a1 a2 = 
    let res = (ML2C.n_mk_set_intersect a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_set_difference a0 a1 a2 = 
    let res = (ML2C.n_mk_set_difference a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_set_complement a0 a1 = 
    let res = (ML2C.n_mk_set_complement a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_set_member a0 a1 a2 = 
    let res = (ML2C.n_mk_set_member a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_set_subset a0 a1 a2 = 
    let res = (ML2C.n_mk_set_subset a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_numeral a0 a1 a2 = 
    let res = (ML2C.n_mk_numeral a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_real a0 a1 a2 = 
    let res = (ML2C.n_mk_real a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_int a0 a1 a2 = 
    let res = (ML2C.n_mk_int a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_unsigned_int a0 a1 a2 = 
    let res = (ML2C.n_mk_unsigned_int a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_int64 a0 a1 a2 = 
    let res = (ML2C.n_mk_int64 a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_unsigned_int64 a0 a1 a2 = 
    let res = (ML2C.n_mk_unsigned_int64 a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_pattern a0 a1 a2 = 
    let res = (ML2C.n_mk_pattern a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_bound a0 a1 a2 = 
    let res = (ML2C.n_mk_bound a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_forall a0 a1 a2 a3 a4 a5 a6 a7 = 
    let res = (ML2C.n_mk_forall a0 a1 a2 a3 a4 a5 a6 a7) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_exists a0 a1 a2 a3 a4 a5 a6 a7 = 
    let res = (ML2C.n_mk_exists a0 a1 a2 a3 a4 a5 a6 a7) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_quantifier a0 a1 a2 a3 a4 a5 a6 a7 a8 = 
    let res = (ML2C.n_mk_quantifier a0 a1 a2 a3 a4 a5 a6 a7 a8) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_quantifier_ex a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 = 
    let res = (ML2C.n_mk_quantifier_ex a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_forall_const a0 a1 a2 a3 a4 a5 a6 = 
    let res = (ML2C.n_mk_forall_const a0 a1 a2 a3 a4 a5 a6) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_exists_const a0 a1 a2 a3 a4 a5 a6 = 
    let res = (ML2C.n_mk_exists_const a0 a1 a2 a3 a4 a5 a6) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_quantifier_const a0 a1 a2 a3 a4 a5 a6 a7 = 
    let res = (ML2C.n_mk_quantifier_const a0 a1 a2 a3 a4 a5 a6 a7) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_quantifier_const_ex a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 = 
    let res = (ML2C.n_mk_quantifier_const_ex a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_symbol_kind a0 a1 = 
    let res = (ML2C.n_get_symbol_kind a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_symbol_int a0 a1 = 
    let res = (ML2C.n_get_symbol_int a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_symbol_string a0 a1 = 
    let res = (ML2C.n_get_symbol_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_sort_name a0 a1 = 
    let res = (ML2C.n_get_sort_name a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_sort_id a0 a1 = 
    let res = (ML2C.n_get_sort_id a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let sort_to_ast a0 a1 = 
    let res = (ML2C.n_sort_to_ast a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_eq_sort a0 a1 a2 = 
    let res = (ML2C.n_is_eq_sort a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_sort_kind a0 a1 = 
    let res = (ML2C.n_get_sort_kind a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_bv_sort_size a0 a1 = 
    let res = (ML2C.n_get_bv_sort_size a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_finite_domain_sort_size a0 a1 = 
    let res = (ML2C.n_get_finite_domain_sort_size a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_array_sort_domain a0 a1 = 
    let res = (ML2C.n_get_array_sort_domain a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_array_sort_range a0 a1 = 
    let res = (ML2C.n_get_array_sort_range a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_tuple_sort_mk_decl a0 a1 = 
    let res = (ML2C.n_get_tuple_sort_mk_decl a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_tuple_sort_num_fields a0 a1 = 
    let res = (ML2C.n_get_tuple_sort_num_fields a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_tuple_sort_field_decl a0 a1 a2 = 
    let res = (ML2C.n_get_tuple_sort_field_decl a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_datatype_sort_num_constructors a0 a1 = 
    let res = (ML2C.n_get_datatype_sort_num_constructors a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_datatype_sort_constructor a0 a1 a2 = 
    let res = (ML2C.n_get_datatype_sort_constructor a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_datatype_sort_recognizer a0 a1 a2 = 
    let res = (ML2C.n_get_datatype_sort_recognizer a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_datatype_sort_constructor_accessor a0 a1 a2 a3 = 
    let res = (ML2C.n_get_datatype_sort_constructor_accessor a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_relation_arity a0 a1 = 
    let res = (ML2C.n_get_relation_arity a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_relation_column a0 a1 a2 = 
    let res = (ML2C.n_get_relation_column a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let func_decl_to_ast a0 a1 = 
    let res = (ML2C.n_func_decl_to_ast a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_eq_func_decl a0 a1 a2 = 
    let res = (ML2C.n_is_eq_func_decl a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_func_decl_id a0 a1 = 
    let res = (ML2C.n_get_func_decl_id a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_name a0 a1 = 
    let res = (ML2C.n_get_decl_name a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_kind a0 a1 = 
    let res = (ML2C.n_get_decl_kind a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_domain_size a0 a1 = 
    let res = (ML2C.n_get_domain_size a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_arity a0 a1 = 
    let res = (ML2C.n_get_arity a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_domain a0 a1 a2 = 
    let res = (ML2C.n_get_domain a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_range a0 a1 = 
    let res = (ML2C.n_get_range a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_num_parameters a0 a1 = 
    let res = (ML2C.n_get_decl_num_parameters a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_parameter_kind a0 a1 a2 = 
    let res = (ML2C.n_get_decl_parameter_kind a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_int_parameter a0 a1 a2 = 
    let res = (ML2C.n_get_decl_int_parameter a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_double_parameter a0 a1 a2 = 
    let res = (ML2C.n_get_decl_double_parameter a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_symbol_parameter a0 a1 a2 = 
    let res = (ML2C.n_get_decl_symbol_parameter a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_sort_parameter a0 a1 a2 = 
    let res = (ML2C.n_get_decl_sort_parameter a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_ast_parameter a0 a1 a2 = 
    let res = (ML2C.n_get_decl_ast_parameter a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_func_decl_parameter a0 a1 a2 = 
    let res = (ML2C.n_get_decl_func_decl_parameter a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_decl_rational_parameter a0 a1 a2 = 
    let res = (ML2C.n_get_decl_rational_parameter a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let app_to_ast a0 a1 = 
    let res = (ML2C.n_app_to_ast a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_app_decl a0 a1 = 
    let res = (ML2C.n_get_app_decl a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_app_num_args a0 a1 = 
    let res = (ML2C.n_get_app_num_args a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_app_arg a0 a1 a2 = 
    let res = (ML2C.n_get_app_arg a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_eq_ast a0 a1 a2 = 
    let res = (ML2C.n_is_eq_ast a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_ast_id a0 a1 = 
    let res = (ML2C.n_get_ast_id a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_ast_hash a0 a1 = 
    let res = (ML2C.n_get_ast_hash a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_sort a0 a1 = 
    let res = (ML2C.n_get_sort a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_well_sorted a0 a1 = 
    let res = (ML2C.n_is_well_sorted a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_bool_value a0 a1 = 
    let res = (ML2C.n_get_bool_value a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_ast_kind a0 a1 = 
    let res = (ML2C.n_get_ast_kind a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_app a0 a1 = 
    let res = (ML2C.n_is_app a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_numeral_ast a0 a1 = 
    let res = (ML2C.n_is_numeral_ast a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_algebraic_number a0 a1 = 
    let res = (ML2C.n_is_algebraic_number a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let to_app a0 a1 = 
    let res = (ML2C.n_to_app a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let to_func_decl a0 a1 = 
    let res = (ML2C.n_to_func_decl a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_numeral_string a0 a1 = 
    let res = (ML2C.n_get_numeral_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_numeral_decimal_string a0 a1 a2 = 
    let res = (ML2C.n_get_numeral_decimal_string a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_numerator a0 a1 = 
    let res = (ML2C.n_get_numerator a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_denominator a0 a1 = 
    let res = (ML2C.n_get_denominator a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_numeral_small a0 a1 = 
    let res = (ML2C.n_get_numeral_small a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_numeral_int a0 a1 = 
    let res = (ML2C.n_get_numeral_int a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_numeral_uint a0 a1 = 
    let res = (ML2C.n_get_numeral_uint a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_numeral_uint64 a0 a1 = 
    let res = (ML2C.n_get_numeral_uint64 a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_numeral_int64 a0 a1 = 
    let res = (ML2C.n_get_numeral_int64 a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_numeral_rational_int64 a0 a1 = 
    let res = (ML2C.n_get_numeral_rational_int64 a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_algebraic_number_lower a0 a1 a2 = 
    let res = (ML2C.n_get_algebraic_number_lower a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_algebraic_number_upper a0 a1 a2 = 
    let res = (ML2C.n_get_algebraic_number_upper a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let pattern_to_ast a0 a1 = 
    let res = (ML2C.n_pattern_to_ast a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_pattern_num_terms a0 a1 = 
    let res = (ML2C.n_get_pattern_num_terms a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_pattern a0 a1 a2 = 
    let res = (ML2C.n_get_pattern a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_index_value a0 a1 = 
    let res = (ML2C.n_get_index_value a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_quantifier_forall a0 a1 = 
    let res = (ML2C.n_is_quantifier_forall a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_quantifier_weight a0 a1 = 
    let res = (ML2C.n_get_quantifier_weight a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_quantifier_num_patterns a0 a1 = 
    let res = (ML2C.n_get_quantifier_num_patterns a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_quantifier_pattern_ast a0 a1 a2 = 
    let res = (ML2C.n_get_quantifier_pattern_ast a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_quantifier_num_no_patterns a0 a1 = 
    let res = (ML2C.n_get_quantifier_num_no_patterns a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_quantifier_no_pattern_ast a0 a1 a2 = 
    let res = (ML2C.n_get_quantifier_no_pattern_ast a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_quantifier_num_bound a0 a1 = 
    let res = (ML2C.n_get_quantifier_num_bound a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_quantifier_bound_name a0 a1 a2 = 
    let res = (ML2C.n_get_quantifier_bound_name a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_quantifier_bound_sort a0 a1 a2 = 
    let res = (ML2C.n_get_quantifier_bound_sort a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_quantifier_body a0 a1 = 
    let res = (ML2C.n_get_quantifier_body a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let simplify a0 a1 = 
    let res = (ML2C.n_simplify a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let simplify_ex a0 a1 a2 = 
    let res = (ML2C.n_simplify_ex a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let simplify_get_help a0 = 
    let res = (ML2C.n_simplify_get_help a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let simplify_get_param_descrs a0 = 
    let res = (ML2C.n_simplify_get_param_descrs a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let update_term a0 a1 a2 a3 = 
    let res = (ML2C.n_update_term a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let substitute a0 a1 a2 a3 a4 = 
    let res = (ML2C.n_substitute a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let substitute_vars a0 a1 a2 a3 = 
    let res = (ML2C.n_substitute_vars a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let translate a0 a1 a2 = 
    let res = (ML2C.n_translate a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_inc_ref a0 a1 = 
    let _ = (ML2C.n_model_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let model_dec_ref a0 a1 = 
    let _ = (ML2C.n_model_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let model_eval a0 a1 a2 a3 = 
    let res = (ML2C.n_model_eval a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_get_const_interp a0 a1 a2 = 
    let res = (ML2C.n_model_get_const_interp a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_get_func_interp a0 a1 a2 = 
    let res = (ML2C.n_model_get_func_interp a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_get_num_consts a0 a1 = 
    let res = (ML2C.n_model_get_num_consts a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_get_const_decl a0 a1 a2 = 
    let res = (ML2C.n_model_get_const_decl a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_get_num_funcs a0 a1 = 
    let res = (ML2C.n_model_get_num_funcs a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_get_func_decl a0 a1 a2 = 
    let res = (ML2C.n_model_get_func_decl a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_get_num_sorts a0 a1 = 
    let res = (ML2C.n_model_get_num_sorts a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_get_sort a0 a1 a2 = 
    let res = (ML2C.n_model_get_sort a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_get_sort_universe a0 a1 a2 = 
    let res = (ML2C.n_model_get_sort_universe a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_as_array a0 a1 = 
    let res = (ML2C.n_is_as_array a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_as_array_func_decl a0 a1 = 
    let res = (ML2C.n_get_as_array_func_decl a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let func_interp_inc_ref a0 a1 = 
    let _ = (ML2C.n_func_interp_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let func_interp_dec_ref a0 a1 = 
    let _ = (ML2C.n_func_interp_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let func_interp_get_num_entries a0 a1 = 
    let res = (ML2C.n_func_interp_get_num_entries a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let func_interp_get_entry a0 a1 a2 = 
    let res = (ML2C.n_func_interp_get_entry a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let func_interp_get_else a0 a1 = 
    let res = (ML2C.n_func_interp_get_else a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let func_interp_get_arity a0 a1 = 
    let res = (ML2C.n_func_interp_get_arity a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let func_entry_inc_ref a0 a1 = 
    let _ = (ML2C.n_func_entry_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let func_entry_dec_ref a0 a1 = 
    let _ = (ML2C.n_func_entry_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let func_entry_get_value a0 a1 = 
    let res = (ML2C.n_func_entry_get_value a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let func_entry_get_num_args a0 a1 = 
    let res = (ML2C.n_func_entry_get_num_args a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let func_entry_get_arg a0 a1 a2 = 
    let res = (ML2C.n_func_entry_get_arg a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let open_log a0 = 
    let res = (ML2C.n_open_log a0) in
        res

  let append_log a0 = 
    let _ = (ML2C.n_append_log a0) in
        ()

  let close_log () = 
    let _ = (ML2C.n_close_log ()) in
        ()

  let toggle_warning_messages a0 = 
    let _ = (ML2C.n_toggle_warning_messages a0) in
        ()

  let set_ast_print_mode a0 a1 = 
    let _ = (ML2C.n_set_ast_print_mode a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_to_string a0 a1 = 
    let res = (ML2C.n_ast_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let pattern_to_string a0 a1 = 
    let res = (ML2C.n_pattern_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let sort_to_string a0 a1 = 
    let res = (ML2C.n_sort_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let func_decl_to_string a0 a1 = 
    let res = (ML2C.n_func_decl_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let model_to_string a0 a1 = 
    let res = (ML2C.n_model_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let benchmark_to_smtlib_string a0 a1 a2 a3 a4 a5 a6 a7 = 
    let res = (ML2C.n_benchmark_to_smtlib_string a0 a1 a2 a3 a4 a5 a6 a7) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let parse_smtlib2_string a0 a1 a2 a3 a4 a5 a6 a7 = 
    let res = (ML2C.n_parse_smtlib2_string a0 a1 a2 a3 a4 a5 a6 a7) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let parse_smtlib2_file a0 a1 a2 a3 a4 a5 a6 a7 = 
    let res = (ML2C.n_parse_smtlib2_file a0 a1 a2 a3 a4 a5 a6 a7) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let parse_smtlib_string a0 a1 a2 a3 a4 a5 a6 a7 = 
    let _ = (ML2C.n_parse_smtlib_string a0 a1 a2 a3 a4 a5 a6 a7) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let parse_smtlib_file a0 a1 a2 a3 a4 a5 a6 a7 = 
    let _ = (ML2C.n_parse_smtlib_file a0 a1 a2 a3 a4 a5 a6 a7) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let get_smtlib_num_formulas a0 = 
    let res = (ML2C.n_get_smtlib_num_formulas a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_smtlib_formula a0 a1 = 
    let res = (ML2C.n_get_smtlib_formula a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_smtlib_num_assumptions a0 = 
    let res = (ML2C.n_get_smtlib_num_assumptions a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_smtlib_assumption a0 a1 = 
    let res = (ML2C.n_get_smtlib_assumption a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_smtlib_num_decls a0 = 
    let res = (ML2C.n_get_smtlib_num_decls a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_smtlib_decl a0 a1 = 
    let res = (ML2C.n_get_smtlib_decl a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_smtlib_num_sorts a0 = 
    let res = (ML2C.n_get_smtlib_num_sorts a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_smtlib_sort a0 a1 = 
    let res = (ML2C.n_get_smtlib_sort a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_smtlib_error a0 = 
    let res = (ML2C.n_get_smtlib_error a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_error_code a0 = 
    let res = (ML2C.n_get_error_code a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let set_error a0 a1 = 
    let _ = (ML2C.n_set_error a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let get_error_msg a0 = 
    let res = (ML2C.n_get_error_msg a0) in
        res

  let get_error_msg_ex a0 a1 = 
    let res = (ML2C.n_get_error_msg_ex a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_version () = 
    let res = (ML2C.n_get_version ()) in
        res

  let enable_trace a0 = 
    let _ = (ML2C.n_enable_trace a0) in
        ()

  let disable_trace a0 = 
    let _ = (ML2C.n_disable_trace a0) in
        ()

  let reset_memory () = 
    let _ = (ML2C.n_reset_memory ()) in
        ()

  let mk_fixedpoint a0 = 
    let res = (ML2C.n_mk_fixedpoint a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_inc_ref a0 a1 = 
    let _ = (ML2C.n_fixedpoint_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_dec_ref a0 a1 = 
    let _ = (ML2C.n_fixedpoint_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_add_rule a0 a1 a2 a3 = 
    let _ = (ML2C.n_fixedpoint_add_rule a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_add_fact a0 a1 a2 a3 a4 = 
    let _ = (ML2C.n_fixedpoint_add_fact a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_assert a0 a1 a2 = 
    let _ = (ML2C.n_fixedpoint_assert a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_query a0 a1 a2 = 
    let res = (ML2C.n_fixedpoint_query a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_query_relations a0 a1 a2 a3 = 
    let res = (ML2C.n_fixedpoint_query_relations a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_get_answer a0 a1 = 
    let res = (ML2C.n_fixedpoint_get_answer a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_get_reason_unknown a0 a1 = 
    let res = (ML2C.n_fixedpoint_get_reason_unknown a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_update_rule a0 a1 a2 a3 = 
    let _ = (ML2C.n_fixedpoint_update_rule a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_get_num_levels a0 a1 a2 = 
    let res = (ML2C.n_fixedpoint_get_num_levels a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_get_cover_delta a0 a1 a2 a3 = 
    let res = (ML2C.n_fixedpoint_get_cover_delta a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_add_cover a0 a1 a2 a3 a4 = 
    let _ = (ML2C.n_fixedpoint_add_cover a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_get_statistics a0 a1 = 
    let res = (ML2C.n_fixedpoint_get_statistics a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_register_relation a0 a1 a2 = 
    let _ = (ML2C.n_fixedpoint_register_relation a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_set_predicate_representation a0 a1 a2 a3 a4 = 
    let _ = (ML2C.n_fixedpoint_set_predicate_representation a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_get_rules a0 a1 = 
    let res = (ML2C.n_fixedpoint_get_rules a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_get_assertions a0 a1 = 
    let res = (ML2C.n_fixedpoint_get_assertions a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_set_params a0 a1 a2 = 
    let _ = (ML2C.n_fixedpoint_set_params a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_get_help a0 a1 = 
    let res = (ML2C.n_fixedpoint_get_help a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_get_param_descrs a0 a1 = 
    let res = (ML2C.n_fixedpoint_get_param_descrs a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_to_string a0 a1 a2 a3 = 
    let res = (ML2C.n_fixedpoint_to_string a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_from_string a0 a1 a2 = 
    let res = (ML2C.n_fixedpoint_from_string a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_from_file a0 a1 a2 = 
    let res = (ML2C.n_fixedpoint_from_file a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let fixedpoint_push a0 a1 = 
    let _ = (ML2C.n_fixedpoint_push a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let fixedpoint_pop a0 a1 = 
    let _ = (ML2C.n_fixedpoint_pop a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let mk_ast_vector a0 = 
    let res = (ML2C.n_mk_ast_vector a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let ast_vector_inc_ref a0 a1 = 
    let _ = (ML2C.n_ast_vector_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_vector_dec_ref a0 a1 = 
    let _ = (ML2C.n_ast_vector_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_vector_size a0 a1 = 
    let res = (ML2C.n_ast_vector_size a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let ast_vector_get a0 a1 a2 = 
    let res = (ML2C.n_ast_vector_get a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let ast_vector_set a0 a1 a2 a3 = 
    let _ = (ML2C.n_ast_vector_set a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_vector_resize a0 a1 a2 = 
    let _ = (ML2C.n_ast_vector_resize a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_vector_push a0 a1 a2 = 
    let _ = (ML2C.n_ast_vector_push a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_vector_translate a0 a1 a2 = 
    let res = (ML2C.n_ast_vector_translate a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let ast_vector_to_string a0 a1 = 
    let res = (ML2C.n_ast_vector_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_ast_map a0 = 
    let res = (ML2C.n_mk_ast_map a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let ast_map_inc_ref a0 a1 = 
    let _ = (ML2C.n_ast_map_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_map_dec_ref a0 a1 = 
    let _ = (ML2C.n_ast_map_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_map_contains a0 a1 a2 = 
    let res = (ML2C.n_ast_map_contains a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let ast_map_find a0 a1 a2 = 
    let res = (ML2C.n_ast_map_find a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let ast_map_insert a0 a1 a2 a3 = 
    let _ = (ML2C.n_ast_map_insert a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_map_erase a0 a1 a2 = 
    let _ = (ML2C.n_ast_map_erase a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_map_reset a0 a1 = 
    let _ = (ML2C.n_ast_map_reset a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let ast_map_size a0 a1 = 
    let res = (ML2C.n_ast_map_size a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let ast_map_keys a0 a1 = 
    let res = (ML2C.n_ast_map_keys a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let ast_map_to_string a0 a1 = 
    let res = (ML2C.n_ast_map_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_goal a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_goal a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_inc_ref a0 a1 = 
    let _ = (ML2C.n_goal_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let goal_dec_ref a0 a1 = 
    let _ = (ML2C.n_goal_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let goal_precision a0 a1 = 
    let res = (ML2C.n_goal_precision a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_assert a0 a1 a2 = 
    let _ = (ML2C.n_goal_assert a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let goal_inconsistent a0 a1 = 
    let res = (ML2C.n_goal_inconsistent a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_depth a0 a1 = 
    let res = (ML2C.n_goal_depth a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_reset a0 a1 = 
    let _ = (ML2C.n_goal_reset a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let goal_size a0 a1 = 
    let res = (ML2C.n_goal_size a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_formula a0 a1 a2 = 
    let res = (ML2C.n_goal_formula a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_num_exprs a0 a1 = 
    let res = (ML2C.n_goal_num_exprs a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_is_decided_sat a0 a1 = 
    let res = (ML2C.n_goal_is_decided_sat a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_is_decided_unsat a0 a1 = 
    let res = (ML2C.n_goal_is_decided_unsat a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_translate a0 a1 a2 = 
    let res = (ML2C.n_goal_translate a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let goal_to_string a0 a1 = 
    let res = (ML2C.n_goal_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_tactic a0 a1 = 
    let res = (ML2C.n_mk_tactic a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_inc_ref a0 a1 = 
    let _ = (ML2C.n_tactic_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let tactic_dec_ref a0 a1 = 
    let _ = (ML2C.n_tactic_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let mk_probe a0 a1 = 
    let res = (ML2C.n_mk_probe a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_inc_ref a0 a1 = 
    let _ = (ML2C.n_probe_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let probe_dec_ref a0 a1 = 
    let _ = (ML2C.n_probe_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let tactic_and_then a0 a1 a2 = 
    let res = (ML2C.n_tactic_and_then a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_or_else a0 a1 a2 = 
    let res = (ML2C.n_tactic_or_else a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_par_or a0 a1 a2 = 
    let res = (ML2C.n_tactic_par_or a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_par_and_then a0 a1 a2 = 
    let res = (ML2C.n_tactic_par_and_then a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_try_for a0 a1 a2 = 
    let res = (ML2C.n_tactic_try_for a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_when a0 a1 a2 = 
    let res = (ML2C.n_tactic_when a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_cond a0 a1 a2 a3 = 
    let res = (ML2C.n_tactic_cond a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_repeat a0 a1 a2 = 
    let res = (ML2C.n_tactic_repeat a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_skip a0 = 
    let res = (ML2C.n_tactic_skip a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_fail a0 = 
    let res = (ML2C.n_tactic_fail a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_fail_if a0 a1 = 
    let res = (ML2C.n_tactic_fail_if a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_fail_if_not_decided a0 = 
    let res = (ML2C.n_tactic_fail_if_not_decided a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_using_params a0 a1 a2 = 
    let res = (ML2C.n_tactic_using_params a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_const a0 a1 = 
    let res = (ML2C.n_probe_const a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_lt a0 a1 a2 = 
    let res = (ML2C.n_probe_lt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_gt a0 a1 a2 = 
    let res = (ML2C.n_probe_gt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_le a0 a1 a2 = 
    let res = (ML2C.n_probe_le a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_ge a0 a1 a2 = 
    let res = (ML2C.n_probe_ge a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_eq a0 a1 a2 = 
    let res = (ML2C.n_probe_eq a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_and a0 a1 a2 = 
    let res = (ML2C.n_probe_and a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_or a0 a1 a2 = 
    let res = (ML2C.n_probe_or a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_not a0 a1 = 
    let res = (ML2C.n_probe_not a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_num_tactics a0 = 
    let res = (ML2C.n_get_num_tactics a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_tactic_name a0 a1 = 
    let res = (ML2C.n_get_tactic_name a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_num_probes a0 = 
    let res = (ML2C.n_get_num_probes a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_probe_name a0 a1 = 
    let res = (ML2C.n_get_probe_name a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_get_help a0 a1 = 
    let res = (ML2C.n_tactic_get_help a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_get_param_descrs a0 a1 = 
    let res = (ML2C.n_tactic_get_param_descrs a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_get_descr a0 a1 = 
    let res = (ML2C.n_tactic_get_descr a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_get_descr a0 a1 = 
    let res = (ML2C.n_probe_get_descr a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let probe_apply a0 a1 a2 = 
    let res = (ML2C.n_probe_apply a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_apply a0 a1 a2 = 
    let res = (ML2C.n_tactic_apply a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let tactic_apply_ex a0 a1 a2 a3 = 
    let res = (ML2C.n_tactic_apply_ex a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let apply_result_inc_ref a0 a1 = 
    let _ = (ML2C.n_apply_result_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let apply_result_dec_ref a0 a1 = 
    let _ = (ML2C.n_apply_result_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let apply_result_to_string a0 a1 = 
    let res = (ML2C.n_apply_result_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let apply_result_get_num_subgoals a0 a1 = 
    let res = (ML2C.n_apply_result_get_num_subgoals a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let apply_result_get_subgoal a0 a1 a2 = 
    let res = (ML2C.n_apply_result_get_subgoal a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let apply_result_convert_model a0 a1 a2 a3 = 
    let res = (ML2C.n_apply_result_convert_model a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_solver a0 = 
    let res = (ML2C.n_mk_solver a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_simple_solver a0 = 
    let res = (ML2C.n_mk_simple_solver a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_solver_for_logic a0 a1 = 
    let res = (ML2C.n_mk_solver_for_logic a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_solver_from_tactic a0 a1 = 
    let res = (ML2C.n_mk_solver_from_tactic a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_get_help a0 a1 = 
    let res = (ML2C.n_solver_get_help a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_get_param_descrs a0 a1 = 
    let res = (ML2C.n_solver_get_param_descrs a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_set_params a0 a1 a2 = 
    let _ = (ML2C.n_solver_set_params a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let solver_inc_ref a0 a1 = 
    let _ = (ML2C.n_solver_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let solver_dec_ref a0 a1 = 
    let _ = (ML2C.n_solver_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let solver_push a0 a1 = 
    let _ = (ML2C.n_solver_push a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let solver_pop a0 a1 a2 = 
    let _ = (ML2C.n_solver_pop a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let solver_reset a0 a1 = 
    let _ = (ML2C.n_solver_reset a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let solver_get_num_scopes a0 a1 = 
    let res = (ML2C.n_solver_get_num_scopes a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_assert a0 a1 a2 = 
    let _ = (ML2C.n_solver_assert a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let solver_assert_and_track a0 a1 a2 a3 = 
    let _ = (ML2C.n_solver_assert_and_track a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let solver_get_assertions a0 a1 = 
    let res = (ML2C.n_solver_get_assertions a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_check a0 a1 = 
    let res = (ML2C.n_solver_check a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_check_assumptions a0 a1 a2 a3 = 
    let res = (ML2C.n_solver_check_assumptions a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_get_model a0 a1 = 
    let res = (ML2C.n_solver_get_model a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_get_proof a0 a1 = 
    let res = (ML2C.n_solver_get_proof a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_get_unsat_core a0 a1 = 
    let res = (ML2C.n_solver_get_unsat_core a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_get_reason_unknown a0 a1 = 
    let res = (ML2C.n_solver_get_reason_unknown a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_get_statistics a0 a1 = 
    let res = (ML2C.n_solver_get_statistics a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let solver_to_string a0 a1 = 
    let res = (ML2C.n_solver_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let stats_to_string a0 a1 = 
    let res = (ML2C.n_stats_to_string a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let stats_inc_ref a0 a1 = 
    let _ = (ML2C.n_stats_inc_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let stats_dec_ref a0 a1 = 
    let _ = (ML2C.n_stats_dec_ref a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let stats_size a0 a1 = 
    let res = (ML2C.n_stats_size a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let stats_get_key a0 a1 a2 = 
    let res = (ML2C.n_stats_get_key a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let stats_is_uint a0 a1 a2 = 
    let res = (ML2C.n_stats_is_uint a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let stats_is_double a0 a1 a2 = 
    let res = (ML2C.n_stats_is_double a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let stats_get_uint_value a0 a1 a2 = 
    let res = (ML2C.n_stats_get_uint_value a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let stats_get_double_value a0 a1 a2 = 
    let res = (ML2C.n_stats_get_double_value a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_injective_function a0 a1 a2 a3 a4 = 
    let res = (ML2C.n_mk_injective_function a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let set_logic a0 a1 = 
    let _ = (ML2C.n_set_logic a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let push a0 = 
    let _ = (ML2C.n_push a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let pop a0 a1 = 
    let _ = (ML2C.n_pop a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let get_num_scopes a0 = 
    let res = (ML2C.n_get_num_scopes a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let persist_ast a0 a1 a2 = 
    let _ = (ML2C.n_persist_ast a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let assert_cnstr a0 a1 = 
    let _ = (ML2C.n_assert_cnstr a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let check_and_get_model a0 = 
    let res = (ML2C.n_check_and_get_model a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let check a0 = 
    let res = (ML2C.n_check a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let check_assumptions a0 a1 a2 = 
    let res = (ML2C.n_check_assumptions a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_implied_equalities a0 a1 a2 a3 = 
    let res = (ML2C.n_get_implied_equalities a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let del_model a0 a1 = 
    let _ = (ML2C.n_del_model a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let soft_check_cancel a0 = 
    let _ = (ML2C.n_soft_check_cancel a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let get_search_failure a0 = 
    let res = (ML2C.n_get_search_failure a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_label a0 a1 a2 a3 = 
    let res = (ML2C.n_mk_label a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_relevant_labels a0 = 
    let res = (ML2C.n_get_relevant_labels a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_relevant_literals a0 = 
    let res = (ML2C.n_get_relevant_literals a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_guessed_literals a0 = 
    let res = (ML2C.n_get_guessed_literals a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let del_literals a0 a1 = 
    let _ = (ML2C.n_del_literals a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let get_num_literals a0 a1 = 
    let res = (ML2C.n_get_num_literals a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_label_symbol a0 a1 a2 = 
    let res = (ML2C.n_get_label_symbol a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_literal a0 a1 a2 = 
    let res = (ML2C.n_get_literal a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let disable_literal a0 a1 a2 = 
    let _ = (ML2C.n_disable_literal a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let block_literals a0 a1 = 
    let _ = (ML2C.n_block_literals a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let get_model_num_constants a0 a1 = 
    let res = (ML2C.n_get_model_num_constants a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_model_constant a0 a1 a2 = 
    let res = (ML2C.n_get_model_constant a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_model_num_funcs a0 a1 = 
    let res = (ML2C.n_get_model_num_funcs a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_model_func_decl a0 a1 a2 = 
    let res = (ML2C.n_get_model_func_decl a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let eval_func_decl a0 a1 a2 = 
    let res = (ML2C.n_eval_func_decl a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let is_array_value a0 a1 a2 = 
    let res = (ML2C.n_is_array_value a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_array_value a0 a1 a2 a3 = 
    let res = (ML2C.n_get_array_value a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_model_func_else a0 a1 a2 = 
    let res = (ML2C.n_get_model_func_else a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_model_func_num_entries a0 a1 a2 = 
    let res = (ML2C.n_get_model_func_num_entries a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_model_func_entry_num_args a0 a1 a2 a3 = 
    let res = (ML2C.n_get_model_func_entry_num_args a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_model_func_entry_arg a0 a1 a2 a3 a4 = 
    let res = (ML2C.n_get_model_func_entry_arg a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_model_func_entry_value a0 a1 a2 a3 = 
    let res = (ML2C.n_get_model_func_entry_value a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let eval a0 a1 a2 = 
    let res = (ML2C.n_eval a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let eval_decl a0 a1 a2 a3 a4 = 
    let res = (ML2C.n_eval_decl a0 a1 a2 a3 a4) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let context_to_string a0 = 
    let res = (ML2C.n_context_to_string a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let statistics_to_string a0 = 
    let res = (ML2C.n_statistics_to_string a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let get_context_assignment a0 = 
    let res = (ML2C.n_get_context_assignment a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let mk_interpolation_context a0 = 
    let res = (ML2C.n_mk_interpolation_context a0) in
        res

  let interpolation_profile a0 = 
    let res = (ML2C.n_interpolation_profile a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_is_value a0 a1 = 
    let res = (ML2C.n_algebraic_is_value a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_is_pos a0 a1 = 
    let res = (ML2C.n_algebraic_is_pos a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_is_neg a0 a1 = 
    let res = (ML2C.n_algebraic_is_neg a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_is_zero a0 a1 = 
    let res = (ML2C.n_algebraic_is_zero a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_sign a0 a1 = 
    let res = (ML2C.n_algebraic_sign a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_add a0 a1 a2 = 
    let res = (ML2C.n_algebraic_add a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_sub a0 a1 a2 = 
    let res = (ML2C.n_algebraic_sub a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_mul a0 a1 a2 = 
    let res = (ML2C.n_algebraic_mul a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_div a0 a1 a2 = 
    let res = (ML2C.n_algebraic_div a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_root a0 a1 a2 = 
    let res = (ML2C.n_algebraic_root a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_power a0 a1 a2 = 
    let res = (ML2C.n_algebraic_power a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_lt a0 a1 a2 = 
    let res = (ML2C.n_algebraic_lt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_gt a0 a1 a2 = 
    let res = (ML2C.n_algebraic_gt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_le a0 a1 a2 = 
    let res = (ML2C.n_algebraic_le a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_ge a0 a1 a2 = 
    let res = (ML2C.n_algebraic_ge a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_eq a0 a1 a2 = 
    let res = (ML2C.n_algebraic_eq a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_neq a0 a1 a2 = 
    let res = (ML2C.n_algebraic_neq a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_roots a0 a1 a2 a3 = 
    let res = (ML2C.n_algebraic_roots a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let algebraic_eval a0 a1 a2 a3 = 
    let res = (ML2C.n_algebraic_eval a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let polynomial_subresultants a0 a1 a2 a3 = 
    let res = (ML2C.n_polynomial_subresultants a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_del a0 a1 = 
    let _ = (ML2C.n_rcf_del a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        ()

  let rcf_mk_rational a0 a1 = 
    let res = (ML2C.n_rcf_mk_rational a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_mk_small_int a0 a1 = 
    let res = (ML2C.n_rcf_mk_small_int a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_mk_pi a0 = 
    let res = (ML2C.n_rcf_mk_pi a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_mk_e a0 = 
    let res = (ML2C.n_rcf_mk_e a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_mk_infinitesimal a0 = 
    let res = (ML2C.n_rcf_mk_infinitesimal a0) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_mk_roots a0 a1 a2 = 
    let res = (ML2C.n_rcf_mk_roots a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_add a0 a1 a2 = 
    let res = (ML2C.n_rcf_add a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_sub a0 a1 a2 = 
    let res = (ML2C.n_rcf_sub a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_mul a0 a1 a2 = 
    let res = (ML2C.n_rcf_mul a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_div a0 a1 a2 = 
    let res = (ML2C.n_rcf_div a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_neg a0 a1 = 
    let res = (ML2C.n_rcf_neg a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_inv a0 a1 = 
    let res = (ML2C.n_rcf_inv a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_power a0 a1 a2 = 
    let res = (ML2C.n_rcf_power a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_lt a0 a1 a2 = 
    let res = (ML2C.n_rcf_lt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_gt a0 a1 a2 = 
    let res = (ML2C.n_rcf_gt a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_le a0 a1 a2 = 
    let res = (ML2C.n_rcf_le a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_ge a0 a1 a2 = 
    let res = (ML2C.n_rcf_ge a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_eq a0 a1 a2 = 
    let res = (ML2C.n_rcf_eq a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_neq a0 a1 a2 = 
    let res = (ML2C.n_rcf_neq a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_num_to_string a0 a1 a2 a3 = 
    let res = (ML2C.n_rcf_num_to_string a0 a1 a2 a3) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_num_to_decimal_string a0 a1 a2 = 
    let res = (ML2C.n_rcf_num_to_decimal_string a0 a1 a2) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

  let rcf_get_numerator_denominator a0 a1 = 
    let res = (ML2C.n_rcf_get_numerator_denominator a0 a1) in
    let err = (error_code_of_int (ML2C.n_get_error_code a0)) in 
      if err <> OK then
        raise (Exception (ML2C.n_get_error_msg_ex a0 (int_of_error_code err)))
      else
        res

(**/**)
