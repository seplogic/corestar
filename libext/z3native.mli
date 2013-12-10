(* Automatically generated file *)

(** The native (raw) interface to the dynamic Z3 library. *)

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

val is_null : ptr -> bool
val mk_null : unit -> ptr
val set_internal_error_handler : ptr -> unit

exception Exception of string

val global_param_set : string -> string -> unit
val global_param_reset_all :  unit -> unit
val global_param_get : string -> (bool * string)
val mk_config :  unit -> z3_config
val del_config : z3_config -> unit
val set_param_value : z3_config -> string -> string -> unit
val mk_context : z3_config -> z3_context
val mk_context_rc : z3_config -> z3_context
val del_context : z3_context -> unit
val inc_ref : z3_context -> z3_ast -> unit
val dec_ref : z3_context -> z3_ast -> unit
val update_param_value : z3_context -> string -> string -> unit
val get_param_value : z3_context -> string -> (bool * string)
val interrupt : z3_context -> unit
val mk_params : z3_context -> z3_params
val params_inc_ref : z3_context -> z3_params -> unit
val params_dec_ref : z3_context -> z3_params -> unit
val params_set_bool : z3_context -> z3_params -> z3_symbol -> bool -> unit
val params_set_uint : z3_context -> z3_params -> z3_symbol -> int -> unit
val params_set_double : z3_context -> z3_params -> z3_symbol -> float -> unit
val params_set_symbol : z3_context -> z3_params -> z3_symbol -> z3_symbol -> unit
val params_to_string : z3_context -> z3_params -> string
val params_validate : z3_context -> z3_params -> z3_param_descrs -> unit
val param_descrs_inc_ref : z3_context -> z3_param_descrs -> unit
val param_descrs_dec_ref : z3_context -> z3_param_descrs -> unit
val param_descrs_get_kind : z3_context -> z3_param_descrs -> z3_symbol -> int
val param_descrs_size : z3_context -> z3_param_descrs -> int
val param_descrs_get_name : z3_context -> z3_param_descrs -> int -> z3_symbol
val param_descrs_to_string : z3_context -> z3_param_descrs -> string
val mk_int_symbol : z3_context -> int -> z3_symbol
val mk_string_symbol : z3_context -> string -> z3_symbol
val mk_uninterpreted_sort : z3_context -> z3_symbol -> z3_sort
val mk_bool_sort : z3_context -> z3_sort
val mk_int_sort : z3_context -> z3_sort
val mk_real_sort : z3_context -> z3_sort
val mk_bv_sort : z3_context -> int -> z3_sort
val mk_finite_domain_sort : z3_context -> z3_symbol -> int -> z3_sort
val mk_array_sort : z3_context -> z3_sort -> z3_sort -> z3_sort
val mk_tuple_sort : z3_context -> z3_symbol -> int -> z3_symbol array -> z3_sort array -> (z3_sort * ptr * z3_func_decl array)
val mk_enumeration_sort : z3_context -> z3_symbol -> int -> z3_symbol array -> (z3_sort * z3_func_decl array * z3_func_decl array)
val mk_list_sort : z3_context -> z3_symbol -> z3_sort -> (z3_sort * ptr * ptr * ptr * ptr * ptr * ptr)
val mk_constructor : z3_context -> z3_symbol -> z3_symbol -> int -> z3_symbol array -> z3_sort array -> int array -> z3_constructor
val del_constructor : z3_context -> z3_constructor -> unit
val mk_datatype : z3_context -> z3_symbol -> int -> z3_constructor array -> (z3_sort * z3_constructor array)
val mk_constructor_list : z3_context -> int -> z3_constructor array -> z3_constructor_list
val del_constructor_list : z3_context -> z3_constructor_list -> unit
val mk_datatypes : z3_context -> int -> z3_symbol array -> z3_constructor_list array -> (z3_sort array * z3_constructor_list array)
val query_constructor : z3_context -> z3_constructor -> int -> (ptr * ptr * z3_func_decl array)
val mk_func_decl : z3_context -> z3_symbol -> int -> z3_sort array -> z3_sort -> z3_func_decl
val mk_app : z3_context -> z3_func_decl -> int -> z3_ast array -> z3_ast
val mk_const : z3_context -> z3_symbol -> z3_sort -> z3_ast
val mk_fresh_func_decl : z3_context -> string -> int -> z3_sort array -> z3_sort -> z3_func_decl
val mk_fresh_const : z3_context -> string -> z3_sort -> z3_ast
val mk_true : z3_context -> z3_ast
val mk_false : z3_context -> z3_ast
val mk_eq : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_distinct : z3_context -> int -> z3_ast array -> z3_ast
val mk_not : z3_context -> z3_ast -> z3_ast
val mk_interp : z3_context -> z3_ast -> z3_ast
val mk_ite : z3_context -> z3_ast -> z3_ast -> z3_ast -> z3_ast
val mk_iff : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_implies : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_xor : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_and : z3_context -> int -> z3_ast array -> z3_ast
val mk_or : z3_context -> int -> z3_ast array -> z3_ast
val mk_add : z3_context -> int -> z3_ast array -> z3_ast
val mk_mul : z3_context -> int -> z3_ast array -> z3_ast
val mk_sub : z3_context -> int -> z3_ast array -> z3_ast
val mk_unary_minus : z3_context -> z3_ast -> z3_ast
val mk_div : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_mod : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_rem : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_power : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_lt : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_le : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_gt : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_ge : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_int2real : z3_context -> z3_ast -> z3_ast
val mk_real2int : z3_context -> z3_ast -> z3_ast
val mk_is_int : z3_context -> z3_ast -> z3_ast
val mk_bvnot : z3_context -> z3_ast -> z3_ast
val mk_bvredand : z3_context -> z3_ast -> z3_ast
val mk_bvredor : z3_context -> z3_ast -> z3_ast
val mk_bvand : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvor : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvxor : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvnand : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvnor : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvxnor : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvneg : z3_context -> z3_ast -> z3_ast
val mk_bvadd : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvsub : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvmul : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvudiv : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvsdiv : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvurem : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvsrem : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvsmod : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvult : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvslt : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvule : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvsle : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvuge : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvsge : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvugt : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvsgt : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_concat : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_extract : z3_context -> int -> int -> z3_ast -> z3_ast
val mk_sign_ext : z3_context -> int -> z3_ast -> z3_ast
val mk_zero_ext : z3_context -> int -> z3_ast -> z3_ast
val mk_repeat : z3_context -> int -> z3_ast -> z3_ast
val mk_bvshl : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvlshr : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvashr : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_rotate_left : z3_context -> int -> z3_ast -> z3_ast
val mk_rotate_right : z3_context -> int -> z3_ast -> z3_ast
val mk_ext_rotate_left : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_ext_rotate_right : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_int2bv : z3_context -> int -> z3_ast -> z3_ast
val mk_bv2int : z3_context -> z3_ast -> bool -> z3_ast
val mk_bvadd_no_overflow : z3_context -> z3_ast -> z3_ast -> bool -> z3_ast
val mk_bvadd_no_underflow : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvsub_no_overflow : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvsub_no_underflow : z3_context -> z3_ast -> z3_ast -> bool -> z3_ast
val mk_bvsdiv_no_overflow : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_bvneg_no_overflow : z3_context -> z3_ast -> z3_ast
val mk_bvmul_no_overflow : z3_context -> z3_ast -> z3_ast -> bool -> z3_ast
val mk_bvmul_no_underflow : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_select : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_store : z3_context -> z3_ast -> z3_ast -> z3_ast -> z3_ast
val mk_const_array : z3_context -> z3_sort -> z3_ast -> z3_ast
val mk_map : z3_context -> z3_func_decl -> int -> z3_ast array -> z3_ast
val mk_array_default : z3_context -> z3_ast -> z3_ast
val mk_set_sort : z3_context -> z3_sort -> z3_sort
val mk_empty_set : z3_context -> z3_sort -> z3_ast
val mk_full_set : z3_context -> z3_sort -> z3_ast
val mk_set_add : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_set_del : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_set_union : z3_context -> int -> z3_ast array -> z3_ast
val mk_set_intersect : z3_context -> int -> z3_ast array -> z3_ast
val mk_set_difference : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_set_complement : z3_context -> z3_ast -> z3_ast
val mk_set_member : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_set_subset : z3_context -> z3_ast -> z3_ast -> z3_ast
val mk_numeral : z3_context -> string -> z3_sort -> z3_ast
val mk_real : z3_context -> int -> int -> z3_ast
val mk_int : z3_context -> int -> z3_sort -> z3_ast
val mk_unsigned_int : z3_context -> int -> z3_sort -> z3_ast
val mk_int64 : z3_context -> int -> z3_sort -> z3_ast
val mk_unsigned_int64 : z3_context -> int -> z3_sort -> z3_ast
val mk_pattern : z3_context -> int -> z3_ast array -> z3_pattern
val mk_bound : z3_context -> int -> z3_sort -> z3_ast
val mk_forall : z3_context -> int -> int -> z3_pattern array -> int -> z3_sort array -> z3_symbol array -> z3_ast -> z3_ast
val mk_exists : z3_context -> int -> int -> z3_pattern array -> int -> z3_sort array -> z3_symbol array -> z3_ast -> z3_ast
val mk_quantifier : z3_context -> bool -> int -> int -> z3_pattern array -> int -> z3_sort array -> z3_symbol array -> z3_ast -> z3_ast
val mk_quantifier_ex : z3_context -> bool -> int -> z3_symbol -> z3_symbol -> int -> z3_pattern array -> int -> z3_ast array -> int -> z3_sort array -> z3_symbol array -> z3_ast -> z3_ast
val mk_forall_const : z3_context -> int -> int -> z3_app array -> int -> z3_pattern array -> z3_ast -> z3_ast
val mk_exists_const : z3_context -> int -> int -> z3_app array -> int -> z3_pattern array -> z3_ast -> z3_ast
val mk_quantifier_const : z3_context -> bool -> int -> int -> z3_app array -> int -> z3_pattern array -> z3_ast -> z3_ast
val mk_quantifier_const_ex : z3_context -> bool -> int -> z3_symbol -> z3_symbol -> int -> z3_app array -> int -> z3_pattern array -> int -> z3_ast array -> z3_ast -> z3_ast
val get_symbol_kind : z3_context -> z3_symbol -> int
val get_symbol_int : z3_context -> z3_symbol -> int
val get_symbol_string : z3_context -> z3_symbol -> string
val get_sort_name : z3_context -> z3_sort -> z3_symbol
val get_sort_id : z3_context -> z3_sort -> int
val sort_to_ast : z3_context -> z3_sort -> z3_ast
val is_eq_sort : z3_context -> z3_sort -> z3_sort -> bool
val get_sort_kind : z3_context -> z3_sort -> int
val get_bv_sort_size : z3_context -> z3_sort -> int
val get_finite_domain_sort_size : z3_context -> z3_sort -> (bool * int)
val get_array_sort_domain : z3_context -> z3_sort -> z3_sort
val get_array_sort_range : z3_context -> z3_sort -> z3_sort
val get_tuple_sort_mk_decl : z3_context -> z3_sort -> z3_func_decl
val get_tuple_sort_num_fields : z3_context -> z3_sort -> int
val get_tuple_sort_field_decl : z3_context -> z3_sort -> int -> z3_func_decl
val get_datatype_sort_num_constructors : z3_context -> z3_sort -> int
val get_datatype_sort_constructor : z3_context -> z3_sort -> int -> z3_func_decl
val get_datatype_sort_recognizer : z3_context -> z3_sort -> int -> z3_func_decl
val get_datatype_sort_constructor_accessor : z3_context -> z3_sort -> int -> int -> z3_func_decl
val get_relation_arity : z3_context -> z3_sort -> int
val get_relation_column : z3_context -> z3_sort -> int -> z3_sort
val func_decl_to_ast : z3_context -> z3_func_decl -> z3_ast
val is_eq_func_decl : z3_context -> z3_func_decl -> z3_func_decl -> bool
val get_func_decl_id : z3_context -> z3_func_decl -> int
val get_decl_name : z3_context -> z3_func_decl -> z3_symbol
val get_decl_kind : z3_context -> z3_func_decl -> int
val get_domain_size : z3_context -> z3_func_decl -> int
val get_arity : z3_context -> z3_func_decl -> int
val get_domain : z3_context -> z3_func_decl -> int -> z3_sort
val get_range : z3_context -> z3_func_decl -> z3_sort
val get_decl_num_parameters : z3_context -> z3_func_decl -> int
val get_decl_parameter_kind : z3_context -> z3_func_decl -> int -> int
val get_decl_int_parameter : z3_context -> z3_func_decl -> int -> int
val get_decl_double_parameter : z3_context -> z3_func_decl -> int -> float
val get_decl_symbol_parameter : z3_context -> z3_func_decl -> int -> z3_symbol
val get_decl_sort_parameter : z3_context -> z3_func_decl -> int -> z3_sort
val get_decl_ast_parameter : z3_context -> z3_func_decl -> int -> z3_ast
val get_decl_func_decl_parameter : z3_context -> z3_func_decl -> int -> z3_func_decl
val get_decl_rational_parameter : z3_context -> z3_func_decl -> int -> string
val app_to_ast : z3_context -> z3_app -> z3_ast
val get_app_decl : z3_context -> z3_app -> z3_func_decl
val get_app_num_args : z3_context -> z3_app -> int
val get_app_arg : z3_context -> z3_app -> int -> z3_ast
val is_eq_ast : z3_context -> z3_ast -> z3_ast -> bool
val get_ast_id : z3_context -> z3_ast -> int
val get_ast_hash : z3_context -> z3_ast -> int
val get_sort : z3_context -> z3_ast -> z3_sort
val is_well_sorted : z3_context -> z3_ast -> bool
val get_bool_value : z3_context -> z3_ast -> int
val get_ast_kind : z3_context -> z3_ast -> int
val is_app : z3_context -> z3_ast -> bool
val is_numeral_ast : z3_context -> z3_ast -> bool
val is_algebraic_number : z3_context -> z3_ast -> bool
val to_app : z3_context -> z3_ast -> z3_app
val to_func_decl : z3_context -> z3_ast -> z3_func_decl
val get_numeral_string : z3_context -> z3_ast -> string
val get_numeral_decimal_string : z3_context -> z3_ast -> int -> string
val get_numerator : z3_context -> z3_ast -> z3_ast
val get_denominator : z3_context -> z3_ast -> z3_ast
val get_numeral_small : z3_context -> z3_ast -> (bool * int * int)
val get_numeral_int : z3_context -> z3_ast -> (bool * int)
val get_numeral_uint : z3_context -> z3_ast -> (bool * int)
val get_numeral_uint64 : z3_context -> z3_ast -> (bool * int)
val get_numeral_int64 : z3_context -> z3_ast -> (bool * int)
val get_numeral_rational_int64 : z3_context -> z3_ast -> (bool * int * int)
val get_algebraic_number_lower : z3_context -> z3_ast -> int -> z3_ast
val get_algebraic_number_upper : z3_context -> z3_ast -> int -> z3_ast
val pattern_to_ast : z3_context -> z3_pattern -> z3_ast
val get_pattern_num_terms : z3_context -> z3_pattern -> int
val get_pattern : z3_context -> z3_pattern -> int -> z3_ast
val get_index_value : z3_context -> z3_ast -> int
val is_quantifier_forall : z3_context -> z3_ast -> bool
val get_quantifier_weight : z3_context -> z3_ast -> int
val get_quantifier_num_patterns : z3_context -> z3_ast -> int
val get_quantifier_pattern_ast : z3_context -> z3_ast -> int -> z3_pattern
val get_quantifier_num_no_patterns : z3_context -> z3_ast -> int
val get_quantifier_no_pattern_ast : z3_context -> z3_ast -> int -> z3_ast
val get_quantifier_num_bound : z3_context -> z3_ast -> int
val get_quantifier_bound_name : z3_context -> z3_ast -> int -> z3_symbol
val get_quantifier_bound_sort : z3_context -> z3_ast -> int -> z3_sort
val get_quantifier_body : z3_context -> z3_ast -> z3_ast
val simplify : z3_context -> z3_ast -> z3_ast
val simplify_ex : z3_context -> z3_ast -> z3_params -> z3_ast
val simplify_get_help : z3_context -> string
val simplify_get_param_descrs : z3_context -> z3_param_descrs
val update_term : z3_context -> z3_ast -> int -> z3_ast array -> z3_ast
val substitute : z3_context -> z3_ast -> int -> z3_ast array -> z3_ast array -> z3_ast
val substitute_vars : z3_context -> z3_ast -> int -> z3_ast array -> z3_ast
val translate : z3_context -> z3_ast -> z3_context -> z3_ast
val model_inc_ref : z3_context -> z3_model -> unit
val model_dec_ref : z3_context -> z3_model -> unit
val model_eval : z3_context -> z3_model -> z3_ast -> bool -> (bool * ptr)
val model_get_const_interp : z3_context -> z3_model -> z3_func_decl -> z3_ast
val model_get_func_interp : z3_context -> z3_model -> z3_func_decl -> z3_func_interp
val model_get_num_consts : z3_context -> z3_model -> int
val model_get_const_decl : z3_context -> z3_model -> int -> z3_func_decl
val model_get_num_funcs : z3_context -> z3_model -> int
val model_get_func_decl : z3_context -> z3_model -> int -> z3_func_decl
val model_get_num_sorts : z3_context -> z3_model -> int
val model_get_sort : z3_context -> z3_model -> int -> z3_sort
val model_get_sort_universe : z3_context -> z3_model -> z3_sort -> z3_ast_vector
val is_as_array : z3_context -> z3_ast -> bool
val get_as_array_func_decl : z3_context -> z3_ast -> z3_func_decl
val func_interp_inc_ref : z3_context -> z3_func_interp -> unit
val func_interp_dec_ref : z3_context -> z3_func_interp -> unit
val func_interp_get_num_entries : z3_context -> z3_func_interp -> int
val func_interp_get_entry : z3_context -> z3_func_interp -> int -> z3_func_entry
val func_interp_get_else : z3_context -> z3_func_interp -> z3_ast
val func_interp_get_arity : z3_context -> z3_func_interp -> int
val func_entry_inc_ref : z3_context -> z3_func_entry -> unit
val func_entry_dec_ref : z3_context -> z3_func_entry -> unit
val func_entry_get_value : z3_context -> z3_func_entry -> z3_ast
val func_entry_get_num_args : z3_context -> z3_func_entry -> int
val func_entry_get_arg : z3_context -> z3_func_entry -> int -> z3_ast
val open_log : string -> int
val append_log : string -> unit
val close_log :  unit -> unit
val toggle_warning_messages : bool -> unit
val set_ast_print_mode : z3_context -> int -> unit
val ast_to_string : z3_context -> z3_ast -> string
val pattern_to_string : z3_context -> z3_pattern -> string
val sort_to_string : z3_context -> z3_sort -> string
val func_decl_to_string : z3_context -> z3_func_decl -> string
val model_to_string : z3_context -> z3_model -> string
val benchmark_to_smtlib_string : z3_context -> string -> string -> string -> string -> int -> z3_ast array -> z3_ast -> string
val parse_smtlib2_string : z3_context -> string -> int -> z3_symbol array -> z3_sort array -> int -> z3_symbol array -> z3_func_decl array -> z3_ast
val parse_smtlib2_file : z3_context -> string -> int -> z3_symbol array -> z3_sort array -> int -> z3_symbol array -> z3_func_decl array -> z3_ast
val parse_smtlib_string : z3_context -> string -> int -> z3_symbol array -> z3_sort array -> int -> z3_symbol array -> z3_func_decl array -> unit
val parse_smtlib_file : z3_context -> string -> int -> z3_symbol array -> z3_sort array -> int -> z3_symbol array -> z3_func_decl array -> unit
val get_smtlib_num_formulas : z3_context -> int
val get_smtlib_formula : z3_context -> int -> z3_ast
val get_smtlib_num_assumptions : z3_context -> int
val get_smtlib_assumption : z3_context -> int -> z3_ast
val get_smtlib_num_decls : z3_context -> int
val get_smtlib_decl : z3_context -> int -> z3_func_decl
val get_smtlib_num_sorts : z3_context -> int
val get_smtlib_sort : z3_context -> int -> z3_sort
val get_smtlib_error : z3_context -> string
val get_error_code : z3_context -> int
val set_error : z3_context -> int -> unit
val get_error_msg : int -> string
val get_error_msg_ex : z3_context -> int -> string
val get_version :  unit -> (int * int * int * int)
val enable_trace : string -> unit
val disable_trace : string -> unit
val reset_memory :  unit -> unit
val mk_fixedpoint : z3_context -> z3_fixedpoint
val fixedpoint_inc_ref : z3_context -> z3_fixedpoint -> unit
val fixedpoint_dec_ref : z3_context -> z3_fixedpoint -> unit
val fixedpoint_add_rule : z3_context -> z3_fixedpoint -> z3_ast -> z3_symbol -> unit
val fixedpoint_add_fact : z3_context -> z3_fixedpoint -> z3_func_decl -> int -> int array -> unit
val fixedpoint_assert : z3_context -> z3_fixedpoint -> z3_ast -> unit
val fixedpoint_query : z3_context -> z3_fixedpoint -> z3_ast -> int
val fixedpoint_query_relations : z3_context -> z3_fixedpoint -> int -> z3_func_decl array -> int
val fixedpoint_get_answer : z3_context -> z3_fixedpoint -> z3_ast
val fixedpoint_get_reason_unknown : z3_context -> z3_fixedpoint -> string
val fixedpoint_update_rule : z3_context -> z3_fixedpoint -> z3_ast -> z3_symbol -> unit
val fixedpoint_get_num_levels : z3_context -> z3_fixedpoint -> z3_func_decl -> int
val fixedpoint_get_cover_delta : z3_context -> z3_fixedpoint -> int -> z3_func_decl -> z3_ast
val fixedpoint_add_cover : z3_context -> z3_fixedpoint -> int -> z3_func_decl -> z3_ast -> unit
val fixedpoint_get_statistics : z3_context -> z3_fixedpoint -> z3_stats
val fixedpoint_register_relation : z3_context -> z3_fixedpoint -> z3_func_decl -> unit
val fixedpoint_set_predicate_representation : z3_context -> z3_fixedpoint -> z3_func_decl -> int -> z3_symbol array -> unit
val fixedpoint_get_rules : z3_context -> z3_fixedpoint -> z3_ast_vector
val fixedpoint_get_assertions : z3_context -> z3_fixedpoint -> z3_ast_vector
val fixedpoint_set_params : z3_context -> z3_fixedpoint -> z3_params -> unit
val fixedpoint_get_help : z3_context -> z3_fixedpoint -> string
val fixedpoint_get_param_descrs : z3_context -> z3_fixedpoint -> z3_param_descrs
val fixedpoint_to_string : z3_context -> z3_fixedpoint -> int -> z3_ast array -> string
val fixedpoint_from_string : z3_context -> z3_fixedpoint -> string -> z3_ast_vector
val fixedpoint_from_file : z3_context -> z3_fixedpoint -> string -> z3_ast_vector
val fixedpoint_push : z3_context -> z3_fixedpoint -> unit
val fixedpoint_pop : z3_context -> z3_fixedpoint -> unit
val mk_ast_vector : z3_context -> z3_ast_vector
val ast_vector_inc_ref : z3_context -> z3_ast_vector -> unit
val ast_vector_dec_ref : z3_context -> z3_ast_vector -> unit
val ast_vector_size : z3_context -> z3_ast_vector -> int
val ast_vector_get : z3_context -> z3_ast_vector -> int -> z3_ast
val ast_vector_set : z3_context -> z3_ast_vector -> int -> z3_ast -> unit
val ast_vector_resize : z3_context -> z3_ast_vector -> int -> unit
val ast_vector_push : z3_context -> z3_ast_vector -> z3_ast -> unit
val ast_vector_translate : z3_context -> z3_ast_vector -> z3_context -> z3_ast_vector
val ast_vector_to_string : z3_context -> z3_ast_vector -> string
val mk_ast_map : z3_context -> z3_ast_map
val ast_map_inc_ref : z3_context -> z3_ast_map -> unit
val ast_map_dec_ref : z3_context -> z3_ast_map -> unit
val ast_map_contains : z3_context -> z3_ast_map -> z3_ast -> bool
val ast_map_find : z3_context -> z3_ast_map -> z3_ast -> z3_ast
val ast_map_insert : z3_context -> z3_ast_map -> z3_ast -> z3_ast -> unit
val ast_map_erase : z3_context -> z3_ast_map -> z3_ast -> unit
val ast_map_reset : z3_context -> z3_ast_map -> unit
val ast_map_size : z3_context -> z3_ast_map -> int
val ast_map_keys : z3_context -> z3_ast_map -> z3_ast_vector
val ast_map_to_string : z3_context -> z3_ast_map -> string
val mk_goal : z3_context -> bool -> bool -> bool -> z3_goal
val goal_inc_ref : z3_context -> z3_goal -> unit
val goal_dec_ref : z3_context -> z3_goal -> unit
val goal_precision : z3_context -> z3_goal -> int
val goal_assert : z3_context -> z3_goal -> z3_ast -> unit
val goal_inconsistent : z3_context -> z3_goal -> bool
val goal_depth : z3_context -> z3_goal -> int
val goal_reset : z3_context -> z3_goal -> unit
val goal_size : z3_context -> z3_goal -> int
val goal_formula : z3_context -> z3_goal -> int -> z3_ast
val goal_num_exprs : z3_context -> z3_goal -> int
val goal_is_decided_sat : z3_context -> z3_goal -> bool
val goal_is_decided_unsat : z3_context -> z3_goal -> bool
val goal_translate : z3_context -> z3_goal -> z3_context -> z3_goal
val goal_to_string : z3_context -> z3_goal -> string
val mk_tactic : z3_context -> string -> z3_tactic
val tactic_inc_ref : z3_context -> z3_tactic -> unit
val tactic_dec_ref : z3_context -> z3_tactic -> unit
val mk_probe : z3_context -> string -> z3_probe
val probe_inc_ref : z3_context -> z3_probe -> unit
val probe_dec_ref : z3_context -> z3_probe -> unit
val tactic_and_then : z3_context -> z3_tactic -> z3_tactic -> z3_tactic
val tactic_or_else : z3_context -> z3_tactic -> z3_tactic -> z3_tactic
val tactic_par_or : z3_context -> int -> z3_tactic array -> z3_tactic
val tactic_par_and_then : z3_context -> z3_tactic -> z3_tactic -> z3_tactic
val tactic_try_for : z3_context -> z3_tactic -> int -> z3_tactic
val tactic_when : z3_context -> z3_probe -> z3_tactic -> z3_tactic
val tactic_cond : z3_context -> z3_probe -> z3_tactic -> z3_tactic -> z3_tactic
val tactic_repeat : z3_context -> z3_tactic -> int -> z3_tactic
val tactic_skip : z3_context -> z3_tactic
val tactic_fail : z3_context -> z3_tactic
val tactic_fail_if : z3_context -> z3_probe -> z3_tactic
val tactic_fail_if_not_decided : z3_context -> z3_tactic
val tactic_using_params : z3_context -> z3_tactic -> z3_params -> z3_tactic
val probe_const : z3_context -> float -> z3_probe
val probe_lt : z3_context -> z3_probe -> z3_probe -> z3_probe
val probe_gt : z3_context -> z3_probe -> z3_probe -> z3_probe
val probe_le : z3_context -> z3_probe -> z3_probe -> z3_probe
val probe_ge : z3_context -> z3_probe -> z3_probe -> z3_probe
val probe_eq : z3_context -> z3_probe -> z3_probe -> z3_probe
val probe_and : z3_context -> z3_probe -> z3_probe -> z3_probe
val probe_or : z3_context -> z3_probe -> z3_probe -> z3_probe
val probe_not : z3_context -> z3_probe -> z3_probe
val get_num_tactics : z3_context -> int
val get_tactic_name : z3_context -> int -> string
val get_num_probes : z3_context -> int
val get_probe_name : z3_context -> int -> string
val tactic_get_help : z3_context -> z3_tactic -> string
val tactic_get_param_descrs : z3_context -> z3_tactic -> z3_param_descrs
val tactic_get_descr : z3_context -> string -> string
val probe_get_descr : z3_context -> string -> string
val probe_apply : z3_context -> z3_probe -> z3_goal -> float
val tactic_apply : z3_context -> z3_tactic -> z3_goal -> z3_apply_result
val tactic_apply_ex : z3_context -> z3_tactic -> z3_goal -> z3_params -> z3_apply_result
val apply_result_inc_ref : z3_context -> z3_apply_result -> unit
val apply_result_dec_ref : z3_context -> z3_apply_result -> unit
val apply_result_to_string : z3_context -> z3_apply_result -> string
val apply_result_get_num_subgoals : z3_context -> z3_apply_result -> int
val apply_result_get_subgoal : z3_context -> z3_apply_result -> int -> z3_goal
val apply_result_convert_model : z3_context -> z3_apply_result -> int -> z3_model -> z3_model
val mk_solver : z3_context -> z3_solver
val mk_simple_solver : z3_context -> z3_solver
val mk_solver_for_logic : z3_context -> z3_symbol -> z3_solver
val mk_solver_from_tactic : z3_context -> z3_tactic -> z3_solver
val solver_get_help : z3_context -> z3_solver -> string
val solver_get_param_descrs : z3_context -> z3_solver -> z3_param_descrs
val solver_set_params : z3_context -> z3_solver -> z3_params -> unit
val solver_inc_ref : z3_context -> z3_solver -> unit
val solver_dec_ref : z3_context -> z3_solver -> unit
val solver_push : z3_context -> z3_solver -> unit
val solver_pop : z3_context -> z3_solver -> int -> unit
val solver_reset : z3_context -> z3_solver -> unit
val solver_get_num_scopes : z3_context -> z3_solver -> int
val solver_assert : z3_context -> z3_solver -> z3_ast -> unit
val solver_assert_and_track : z3_context -> z3_solver -> z3_ast -> z3_ast -> unit
val solver_get_assertions : z3_context -> z3_solver -> z3_ast_vector
val solver_check : z3_context -> z3_solver -> int
val solver_check_assumptions : z3_context -> z3_solver -> int -> z3_ast array -> int
val solver_get_model : z3_context -> z3_solver -> z3_model
val solver_get_proof : z3_context -> z3_solver -> z3_ast
val solver_get_unsat_core : z3_context -> z3_solver -> z3_ast_vector
val solver_get_reason_unknown : z3_context -> z3_solver -> string
val solver_get_statistics : z3_context -> z3_solver -> z3_stats
val solver_to_string : z3_context -> z3_solver -> string
val stats_to_string : z3_context -> z3_stats -> string
val stats_inc_ref : z3_context -> z3_stats -> unit
val stats_dec_ref : z3_context -> z3_stats -> unit
val stats_size : z3_context -> z3_stats -> int
val stats_get_key : z3_context -> z3_stats -> int -> string
val stats_is_uint : z3_context -> z3_stats -> int -> bool
val stats_is_double : z3_context -> z3_stats -> int -> bool
val stats_get_uint_value : z3_context -> z3_stats -> int -> int
val stats_get_double_value : z3_context -> z3_stats -> int -> float
val mk_injective_function : z3_context -> z3_symbol -> int -> z3_sort array -> z3_sort -> z3_func_decl
val set_logic : z3_context -> string -> unit
val push : z3_context -> unit
val pop : z3_context -> int -> unit
val get_num_scopes : z3_context -> int
val persist_ast : z3_context -> z3_ast -> int -> unit
val assert_cnstr : z3_context -> z3_ast -> unit
val check_and_get_model : z3_context -> (int * ptr)
val check : z3_context -> int
val check_assumptions : z3_context -> int -> z3_ast array -> (int * ptr * ptr * int * z3_ast array)
val get_implied_equalities : z3_context -> z3_solver -> int -> z3_ast array -> (int * int array)
val del_model : z3_context -> z3_model -> unit
val soft_check_cancel : z3_context -> unit
val get_search_failure : z3_context -> int
val mk_label : z3_context -> z3_symbol -> bool -> z3_ast -> z3_ast
val get_relevant_labels : z3_context -> z3_literals
val get_relevant_literals : z3_context -> z3_literals
val get_guessed_literals : z3_context -> z3_literals
val del_literals : z3_context -> z3_literals -> unit
val get_num_literals : z3_context -> z3_literals -> int
val get_label_symbol : z3_context -> z3_literals -> int -> z3_symbol
val get_literal : z3_context -> z3_literals -> int -> z3_ast
val disable_literal : z3_context -> z3_literals -> int -> unit
val block_literals : z3_context -> z3_literals -> unit
val get_model_num_constants : z3_context -> z3_model -> int
val get_model_constant : z3_context -> z3_model -> int -> z3_func_decl
val get_model_num_funcs : z3_context -> z3_model -> int
val get_model_func_decl : z3_context -> z3_model -> int -> z3_func_decl
val eval_func_decl : z3_context -> z3_model -> z3_func_decl -> (bool * ptr)
val is_array_value : z3_context -> z3_model -> z3_ast -> (bool * int)
val get_array_value : z3_context -> z3_model -> z3_ast -> int -> (z3_ast array * z3_ast array * ptr)
val get_model_func_else : z3_context -> z3_model -> int -> z3_ast
val get_model_func_num_entries : z3_context -> z3_model -> int -> int
val get_model_func_entry_num_args : z3_context -> z3_model -> int -> int -> int
val get_model_func_entry_arg : z3_context -> z3_model -> int -> int -> int -> z3_ast
val get_model_func_entry_value : z3_context -> z3_model -> int -> int -> z3_ast
val eval : z3_context -> z3_model -> z3_ast -> (bool * ptr)
val eval_decl : z3_context -> z3_model -> z3_func_decl -> int -> z3_ast array -> (bool * ptr)
val context_to_string : z3_context -> string
val statistics_to_string : z3_context -> string
val get_context_assignment : z3_context -> z3_ast
val mk_interpolation_context : z3_config -> z3_context
val interpolation_profile : z3_context -> string
val algebraic_is_value : z3_context -> z3_ast -> bool
val algebraic_is_pos : z3_context -> z3_ast -> bool
val algebraic_is_neg : z3_context -> z3_ast -> bool
val algebraic_is_zero : z3_context -> z3_ast -> bool
val algebraic_sign : z3_context -> z3_ast -> int
val algebraic_add : z3_context -> z3_ast -> z3_ast -> z3_ast
val algebraic_sub : z3_context -> z3_ast -> z3_ast -> z3_ast
val algebraic_mul : z3_context -> z3_ast -> z3_ast -> z3_ast
val algebraic_div : z3_context -> z3_ast -> z3_ast -> z3_ast
val algebraic_root : z3_context -> z3_ast -> int -> z3_ast
val algebraic_power : z3_context -> z3_ast -> int -> z3_ast
val algebraic_lt : z3_context -> z3_ast -> z3_ast -> bool
val algebraic_gt : z3_context -> z3_ast -> z3_ast -> bool
val algebraic_le : z3_context -> z3_ast -> z3_ast -> bool
val algebraic_ge : z3_context -> z3_ast -> z3_ast -> bool
val algebraic_eq : z3_context -> z3_ast -> z3_ast -> bool
val algebraic_neq : z3_context -> z3_ast -> z3_ast -> bool
val algebraic_roots : z3_context -> z3_ast -> int -> z3_ast array -> z3_ast_vector
val algebraic_eval : z3_context -> z3_ast -> int -> z3_ast array -> int
val polynomial_subresultants : z3_context -> z3_ast -> z3_ast -> z3_ast -> z3_ast_vector
val rcf_del : z3_context -> z3_rcf_num -> unit
val rcf_mk_rational : z3_context -> string -> z3_rcf_num
val rcf_mk_small_int : z3_context -> int -> z3_rcf_num
val rcf_mk_pi : z3_context -> z3_rcf_num
val rcf_mk_e : z3_context -> z3_rcf_num
val rcf_mk_infinitesimal : z3_context -> z3_rcf_num
val rcf_mk_roots : z3_context -> int -> z3_rcf_num array -> (int * z3_rcf_num array)
val rcf_add : z3_context -> z3_rcf_num -> z3_rcf_num -> z3_rcf_num
val rcf_sub : z3_context -> z3_rcf_num -> z3_rcf_num -> z3_rcf_num
val rcf_mul : z3_context -> z3_rcf_num -> z3_rcf_num -> z3_rcf_num
val rcf_div : z3_context -> z3_rcf_num -> z3_rcf_num -> z3_rcf_num
val rcf_neg : z3_context -> z3_rcf_num -> z3_rcf_num
val rcf_inv : z3_context -> z3_rcf_num -> z3_rcf_num
val rcf_power : z3_context -> z3_rcf_num -> int -> z3_rcf_num
val rcf_lt : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
val rcf_gt : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
val rcf_le : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
val rcf_ge : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
val rcf_eq : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
val rcf_neq : z3_context -> z3_rcf_num -> z3_rcf_num -> bool
val rcf_num_to_string : z3_context -> z3_rcf_num -> bool -> bool -> string
val rcf_num_to_decimal_string : z3_context -> z3_rcf_num -> int -> string
val rcf_get_numerator_denominator : z3_context -> z3_rcf_num -> (ptr * ptr)

(**/**)
