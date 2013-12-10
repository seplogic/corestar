// Automatically generated file

#include <stddef.h>
#include <string.h>

#ifdef __cplusplus
extern "C" {
#endif
#include <caml/mlvalues.h>
#include <caml/memory.h>
#include <caml/alloc.h>
#include <caml/fail.h>
#include <caml/callback.h>
#ifdef Custom_tag
#include <caml/custom.h>
#include <caml/bigarray.h>
#endif
#ifdef __cplusplus
}
#endif

#include <z3.h>

#define CAMLlocal6(X1,X2,X3,X4,X5,X6)                               \
  CAMLlocal5(X1,X2,X3,X4,X5);                                       \
  CAMLlocal1(X6)                                                      
#define CAMLlocal7(X1,X2,X3,X4,X5,X6,X7)                            \
  CAMLlocal5(X1,X2,X3,X4,X5);                                       \
  CAMLlocal2(X6,X7)                                                   
#define CAMLlocal8(X1,X2,X3,X4,X5,X6,X7,X8)                         \
  CAMLlocal5(X1,X2,X3,X4,X5);                                       \
  CAMLlocal3(X6,X7,X8)                                                

#define CAMLparam7(X1,X2,X3,X4,X5,X6,X7)                            \
  CAMLparam5(X1,X2,X3,X4,X5);                                       \
  CAMLxparam2(X6,X7)                                                  
#define CAMLparam8(X1,X2,X3,X4,X5,X6,X7,X8)                         \
  CAMLparam5(X1,X2,X3,X4,X5);                                       \
  CAMLxparam3(X6,X7,X8)                                               
#define CAMLparam9(X1,X2,X3,X4,X5,X6,X7,X8,X9)                      \
  CAMLparam5(X1,X2,X3,X4,X5);                                       \
  CAMLxparam4(X6,X7,X8,X9)                                            
#define CAMLparam12(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12)         \
  CAMLparam5(X1,X2,X3,X4,X5);                                       \
  CAMLxparam5(X6,X7,X8,X9,X10);                                     \
  CAMLxparam2(X11,X12)                                                
#define CAMLparam13(X1,X2,X3,X4,X5,X6,X7,X8,X9,X10,X11,X12,X13)     \
  CAMLparam5(X1,X2,X3,X4,X5);                                       \
  CAMLxparam5(X6,X7,X8,X9,X10);                                     \
  CAMLxparam3(X11,X12,X13)                                            


static struct custom_operations default_custom_ops = {
  (char*) "default handling",
  custom_finalize_default,
  custom_compare_default,
  custom_hash_default,
  custom_serialize_default,
  custom_deserialize_default
};

#ifdef __cplusplus
extern "C" {
#endif

CAMLprim value n_is_null(value p) {
  void * t = * (void**) Data_custom_val(p);
  return Val_bool(t == 0);
}

CAMLprim value n_mk_null( void ) {
  CAMLparam0();
  CAMLlocal1(result);
  void * z3_result = 0;
  result = caml_alloc_custom(&default_custom_ops, sizeof(void*), 0, 1);
  memcpy( Data_custom_val(result), &z3_result, sizeof(void*));
  CAMLreturn (result);
}

void MLErrorHandler(Z3_context c, Z3_error_code e)
{
  // Internal do-nothing error handler. This is required to avoid that Z3 calls exit()
  // upon errors, but the actual error handling is done by throwing exceptions in the
  // wrappers below.
}

void n_set_internal_error_handler(value a0)
{
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_set_error_handler(_a0, MLErrorHandler);
}

CAMLprim value n_global_param_set(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_string _a0 = (Z3_string) String_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_global_param_set(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_global_param_reset_all() {
  CAMLparam0();
  CAMLlocal1(result);
  Z3_global_param_reset_all();
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_global_param_get(value a0) {
  CAMLparam1(a0);
  CAMLlocal3(result, res_val, _a1_val);
  Z3_string _a0 = (Z3_string) String_val(a0);
  Z3_string _a1;
  Z3_bool z3_result;
  z3_result = Z3_global_param_get(_a0, &_a1);
  res_val = Val_bool(z3_result);
  _a1_val = caml_copy_string((const char*) _a1);
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a1_val);
  CAMLreturn(result);
}

CAMLprim value n_mk_config() {
  CAMLparam0();
  CAMLlocal1(result);
  Z3_config z3_result;
  z3_result = Z3_mk_config();
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_config), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_config));
  CAMLreturn(result);
}

CAMLprim value n_del_config(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_config _a0 = * (Z3_config*) Data_custom_val(a0);
  Z3_del_config(_a0);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_set_param_value(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_config _a0 = * (Z3_config*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_string _a2 = (Z3_string) String_val(a2);
  Z3_set_param_value(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_mk_context(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_config _a0 = * (Z3_config*) Data_custom_val(a0);
  Z3_context z3_result;
  z3_result = Z3_mk_context(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_context), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_context));
  CAMLreturn(result);
}

CAMLprim value n_mk_context_rc(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_config _a0 = * (Z3_config*) Data_custom_val(a0);
  Z3_context z3_result;
  z3_result = Z3_mk_context_rc(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_context), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_context));
  CAMLreturn(result);
}

CAMLprim value n_del_context(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_del_context(_a0);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_update_param_value(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_string _a2 = (Z3_string) String_val(a2);
  Z3_update_param_value(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_get_param_value(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal3(result, res_val, _a2_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_string _a2;
  Z3_bool z3_result;
  z3_result = Z3_get_param_value(_a0, _a1, &_a2);
  res_val = Val_bool(z3_result);
  _a2_val = caml_copy_string((const char*) _a2);
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a2_val);
  CAMLreturn(result);
}

CAMLprim value n_interrupt(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_interrupt(_a0);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_mk_params(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_params z3_result;
  z3_result = Z3_mk_params(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_params), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_params));
  CAMLreturn(result);
}

CAMLprim value n_params_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_params _a1 = * (Z3_params*) Data_custom_val(a1);
  Z3_params_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_params_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_params _a1 = * (Z3_params*) Data_custom_val(a1);
  Z3_params_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_params_set_bool(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_params _a1 = * (Z3_params*) Data_custom_val(a1);
  Z3_symbol _a2 = * (Z3_symbol*) Data_custom_val(a2);
  Z3_bool _a3 = (Z3_bool) Bool_val(a3);
  Z3_params_set_bool(_a0, _a1, _a2, _a3);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_params_set_uint(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_params _a1 = * (Z3_params*) Data_custom_val(a1);
  Z3_symbol _a2 = * (Z3_symbol*) Data_custom_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  Z3_params_set_uint(_a0, _a1, _a2, _a3);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_params_set_double(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_params _a1 = * (Z3_params*) Data_custom_val(a1);
  Z3_symbol _a2 = * (Z3_symbol*) Data_custom_val(a2);
  double _a3 = (double) Double_val(a3);
  Z3_params_set_double(_a0, _a1, _a2, _a3);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_params_set_symbol(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_params _a1 = * (Z3_params*) Data_custom_val(a1);
  Z3_symbol _a2 = * (Z3_symbol*) Data_custom_val(a2);
  Z3_symbol _a3 = * (Z3_symbol*) Data_custom_val(a3);
  Z3_params_set_symbol(_a0, _a1, _a2, _a3);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_params_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_params _a1 = * (Z3_params*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_params_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_params_validate(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_params _a1 = * (Z3_params*) Data_custom_val(a1);
  Z3_param_descrs _a2 = * (Z3_param_descrs*) Data_custom_val(a2);
  Z3_params_validate(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_param_descrs_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_param_descrs _a1 = * (Z3_param_descrs*) Data_custom_val(a1);
  Z3_param_descrs_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_param_descrs_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_param_descrs _a1 = * (Z3_param_descrs*) Data_custom_val(a1);
  Z3_param_descrs_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_param_descrs_get_kind(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_param_descrs _a1 = * (Z3_param_descrs*) Data_custom_val(a1);
  Z3_symbol _a2 = * (Z3_symbol*) Data_custom_val(a2);
  unsigned z3_result;
  z3_result = Z3_param_descrs_get_kind(_a0, _a1, _a2);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_param_descrs_size(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_param_descrs _a1 = * (Z3_param_descrs*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_param_descrs_size(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_param_descrs_get_name(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_param_descrs _a1 = * (Z3_param_descrs*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol z3_result;
  z3_result = Z3_param_descrs_get_name(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_symbol), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_symbol));
  CAMLreturn(result);
}

CAMLprim value n_param_descrs_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_param_descrs _a1 = * (Z3_param_descrs*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_param_descrs_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_mk_int_symbol(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  int _a1 = (int) Int_val(a1);
  Z3_symbol z3_result;
  z3_result = Z3_mk_int_symbol(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_symbol), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_symbol));
  CAMLreturn(result);
}

CAMLprim value n_mk_string_symbol(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_symbol z3_result;
  z3_result = Z3_mk_string_symbol(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_symbol), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_symbol));
  CAMLreturn(result);
}

CAMLprim value n_mk_uninterpreted_sort(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  Z3_sort z3_result;
  z3_result = Z3_mk_uninterpreted_sort(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_mk_bool_sort(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort z3_result;
  z3_result = Z3_mk_bool_sort(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_mk_int_sort(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort z3_result;
  z3_result = Z3_mk_int_sort(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_mk_real_sort(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort z3_result;
  z3_result = Z3_mk_real_sort(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_mk_bv_sort(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_sort z3_result;
  z3_result = Z3_mk_bv_sort(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_mk_finite_domain_sort(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  __uint64 _a2 = (__uint64) Unsigned_long_val(a2);
  Z3_sort z3_result;
  z3_result = Z3_mk_finite_domain_sort(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_mk_array_sort(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_sort z3_result;
  z3_result = Z3_mk_array_sort(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_mk_tuple_sort(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal6(result, res_val, _a3_val, _a4_val, _a5_val, _a6_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol * _a3 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a2);
  Z3_sort * _a4 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a2);
  Z3_func_decl _a5;
  Z3_func_decl * _a6 = (Z3_func_decl*) malloc(sizeof(Z3_func_decl) * (_a2));
  Z3_sort z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_symbol*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a2; _i++) { _a4[_i] = * (Z3_sort*) Data_custom_val(Field(a4, _i)); }
  z3_result = Z3_mk_tuple_sort(_a0, _a1, _a2, _a3, _a4, &_a5, _a6);
  res_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(res_val), &z3_result, sizeof(Z3_sort));
  _a5_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(_a5_val), &_a5, sizeof(Z3_func_decl));
  _a6_val = caml_alloc(_a2, 0);
  for (_i = 0; _i < _a2; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(t), &_a6[_i], sizeof(Z3_func_decl)); Store_field(_a6, _i, t); }
  result = caml_alloc(3, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a5_val);
  Store_field(result, 2, _a6_val);
  free(_a3);
  free(_a4);
  free(_a6);
  CAMLreturn(result);
}

CAMLprim value n_mk_enumeration_sort(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal5(result, res_val, _a3_val, _a4_val, _a5_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol * _a3 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a2);
  Z3_func_decl * _a4 = (Z3_func_decl*) malloc(sizeof(Z3_func_decl) * (_a2));
  Z3_func_decl * _a5 = (Z3_func_decl*) malloc(sizeof(Z3_func_decl) * (_a2));
  Z3_sort z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_symbol*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_mk_enumeration_sort(_a0, _a1, _a2, _a3, _a4, _a5);
  res_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(res_val), &z3_result, sizeof(Z3_sort));
  _a4_val = caml_alloc(_a2, 0);
  for (_i = 0; _i < _a2; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(t), &_a4[_i], sizeof(Z3_func_decl)); Store_field(_a4, _i, t); }
  _a5_val = caml_alloc(_a2, 0);
  for (_i = 0; _i < _a2; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(t), &_a5[_i], sizeof(Z3_func_decl)); Store_field(_a5, _i, t); }
  result = caml_alloc(3, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a4_val);
  Store_field(result, 2, _a5_val);
  free(_a3);
  free(_a4);
  free(_a5);
  CAMLreturn(result);
}

CAMLprim value n_mk_list_sort(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal8(result, res_val, _a3_val, _a4_val, _a5_val, _a6_val, _a7_val, _a8_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_func_decl _a3;
  Z3_func_decl _a4;
  Z3_func_decl _a5;
  Z3_func_decl _a6;
  Z3_func_decl _a7;
  Z3_func_decl _a8;
  Z3_sort z3_result;
  z3_result = Z3_mk_list_sort(_a0, _a1, _a2, &_a3, &_a4, &_a5, &_a6, &_a7, &_a8);
  res_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(res_val), &z3_result, sizeof(Z3_sort));
  _a3_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(_a3_val), &_a3, sizeof(Z3_func_decl));
  _a4_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(_a4_val), &_a4, sizeof(Z3_func_decl));
  _a5_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(_a5_val), &_a5, sizeof(Z3_func_decl));
  _a6_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(_a6_val), &_a6, sizeof(Z3_func_decl));
  _a7_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(_a7_val), &_a7, sizeof(Z3_func_decl));
  _a8_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(_a8_val), &_a8, sizeof(Z3_func_decl));
  result = caml_alloc(7, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a3_val);
  Store_field(result, 2, _a4_val);
  Store_field(result, 3, _a5_val);
  Store_field(result, 4, _a6_val);
  Store_field(result, 5, _a7_val);
  Store_field(result, 6, _a8_val);
  CAMLreturn(result);
}

CAMLprim value n_mk_constructor(value a0, value a1, value a2, value a3, value a4, value a5, value a6) {
  CAMLparam7(a0, a1, a2, a3, a4, a5, a6);
  CAMLlocal5(result, res_val, _a4_val, _a5_val, _a6_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  Z3_symbol _a2 = * (Z3_symbol*) Data_custom_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  Z3_symbol * _a4 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a3);
  Z3_sort * _a5 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a3);
  unsigned * _a6 = (unsigned*) malloc(sizeof(unsigned) * _a3);
  Z3_constructor z3_result;
  for (_i = 0; _i < _a3; _i++) { _a4[_i] = * (Z3_symbol*) Data_custom_val(Field(a4, _i)); }
  for (_i = 0; _i < _a3; _i++) { _a5[_i] = * (Z3_sort*) Data_custom_val(Field(a5, _i)); }
  for (_i = 0; _i < _a3; _i++) { _a6[_i] = (unsigned) Unsigned_int_val(Field(a6, _i)); }
  z3_result = Z3_mk_constructor(_a0, _a1, _a2, _a3, _a4, _a5, _a6);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_constructor), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_constructor));
  free(_a4);
  free(_a5);
  free(_a6);
  CAMLreturn(result);
}

CAMLprim value n_mk_constructor_bytecode(value * argv, int argn) {
  return n_mk_constructor(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6]);
}


CAMLprim value n_del_constructor(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_constructor _a1 = * (Z3_constructor*) Data_custom_val(a1);
  Z3_del_constructor(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_mk_datatype(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_constructor * _a3 = (Z3_constructor*) malloc(sizeof(Z3_constructor) * _a2);
  Z3_sort z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_constructor*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_mk_datatype(_a0, _a1, _a2, _a3);
  res_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(res_val), &z3_result, sizeof(Z3_sort));
  _a3_val = caml_alloc(_a2, 0);
  for (_i = 0; _i < _a2; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_constructor), 0, 1); memcpy( Data_custom_val(t), &_a3[_i], sizeof(Z3_constructor)); Store_field(_a3, _i, t); }
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a3_val);
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_mk_constructor_list(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_constructor * _a2 = (Z3_constructor*) malloc(sizeof(Z3_constructor) * _a1);
  Z3_constructor_list z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_constructor*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_constructor_list(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_constructor_list), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_constructor_list));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_del_constructor_list(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_constructor_list _a1 = * (Z3_constructor_list*) Data_custom_val(a1);
  Z3_del_constructor_list(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_mk_datatypes(value a0, value a1, value a2, value a4) {
  CAMLparam4(a0, a1, a2, a4);
  CAMLlocal5(result, res_val, _a2_val, _a3_val, _a4_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_symbol * _a2 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a1);
  Z3_sort * _a3 = (Z3_sort*) malloc(sizeof(Z3_sort) * (_a1));
  Z3_constructor_list * _a4 = (Z3_constructor_list*) malloc(sizeof(Z3_constructor_list) * _a1);
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_symbol*) Data_custom_val(Field(a2, _i)); }
  for (_i = 0; _i < _a1; _i++) { _a4[_i] = * (Z3_constructor_list*) Data_custom_val(Field(a4, _i)); }
  Z3_mk_datatypes(_a0, _a1, _a2, _a3, _a4);
  _a3_val = caml_alloc(_a1, 0);
  for (_i = 0; _i < _a1; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(t), &_a3[_i], sizeof(Z3_sort)); Store_field(_a3, _i, t); }
  _a4_val = caml_alloc(_a1, 0);
  for (_i = 0; _i < _a1; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_constructor_list), 0, 1); memcpy( Data_custom_val(t), &_a4[_i], sizeof(Z3_constructor_list)); Store_field(_a4, _i, t); }
  result = caml_alloc(2, 0);
  Store_field(result, 0, _a3_val);
  Store_field(result, 1, _a4_val);
  free(_a2);
  free(_a3);
  free(_a4);
  CAMLreturn(result);
}

CAMLprim value n_query_constructor(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal5(result, res_val, _a3_val, _a4_val, _a5_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_constructor _a1 = * (Z3_constructor*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl _a3;
  Z3_func_decl _a4;
  Z3_func_decl * _a5 = (Z3_func_decl*) malloc(sizeof(Z3_func_decl) * (_a2));
  Z3_query_constructor(_a0, _a1, _a2, &_a3, &_a4, _a5);
  _a3_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(_a3_val), &_a3, sizeof(Z3_func_decl));
  _a4_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(_a4_val), &_a4, sizeof(Z3_func_decl));
  _a5_val = caml_alloc(_a2, 0);
  for (_i = 0; _i < _a2; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(t), &_a5[_i], sizeof(Z3_func_decl)); Store_field(_a5, _i, t); }
  result = caml_alloc(3, 0);
  Store_field(result, 0, _a3_val);
  Store_field(result, 1, _a4_val);
  Store_field(result, 2, _a5_val);
  free(_a5);
  CAMLreturn(result);
}

CAMLprim value n_mk_func_decl(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_sort * _a3 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a2);
  Z3_sort _a4 = * (Z3_sort*) Data_custom_val(a4);
  Z3_func_decl z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_sort*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_mk_func_decl(_a0, _a1, _a2, _a3, _a4);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_mk_app(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_mk_app(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_mk_const(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_const(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_fresh_func_decl(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_sort * _a3 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a2);
  Z3_sort _a4 = * (Z3_sort*) Data_custom_val(a4);
  Z3_func_decl z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_sort*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_mk_fresh_func_decl(_a0, _a1, _a2, _a3, _a4);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_mk_fresh_const(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_fresh_const(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_true(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast z3_result;
  z3_result = Z3_mk_true(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_false(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast z3_result;
  z3_result = Z3_mk_false(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_eq(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_eq(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_distinct(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_ast z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_distinct(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_mk_not(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_not(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_interp(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_interp(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_ite(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast _a3 = * (Z3_ast*) Data_custom_val(a3);
  Z3_ast z3_result;
  z3_result = Z3_mk_ite(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_iff(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_iff(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_implies(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_implies(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_xor(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_xor(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_and(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_ast z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_and(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_mk_or(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_ast z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_or(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_mk_add(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_ast z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_add(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_mk_mul(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_ast z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_mul(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_mk_sub(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_ast z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_sub(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_mk_unary_minus(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_unary_minus(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_div(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_div(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_mod(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_mod(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_rem(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_rem(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_power(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_power(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_lt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_lt(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_le(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_le(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_gt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_gt(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_ge(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_ge(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_int2real(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_int2real(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_real2int(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_real2int(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_is_int(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_is_int(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvnot(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvnot(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvredand(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvredand(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvredor(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvredor(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvand(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvand(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvor(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvor(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvxor(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvxor(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvnand(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvnand(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvnor(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvnor(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvxnor(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvxnor(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvneg(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvneg(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvadd(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvadd(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsub(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsub(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvmul(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvmul(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvudiv(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvudiv(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsdiv(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsdiv(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvurem(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvurem(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsrem(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsrem(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsmod(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsmod(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvult(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvult(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvslt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvslt(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvule(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvule(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsle(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsle(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvuge(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvuge(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsge(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsge(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvugt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvugt(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsgt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsgt(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_concat(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_concat(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_extract(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast _a3 = * (Z3_ast*) Data_custom_val(a3);
  Z3_ast z3_result;
  z3_result = Z3_mk_extract(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_sign_ext(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_sign_ext(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_zero_ext(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_zero_ext(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_repeat(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_repeat(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvshl(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvshl(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvlshr(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvlshr(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvashr(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvashr(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_rotate_left(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_rotate_left(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_rotate_right(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_rotate_right(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_ext_rotate_left(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_ext_rotate_left(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_ext_rotate_right(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_ext_rotate_right(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_int2bv(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_int2bv(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bv2int(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool _a2 = (Z3_bool) Bool_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bv2int(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvadd_no_overflow(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool _a3 = (Z3_bool) Bool_val(a3);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvadd_no_overflow(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvadd_no_underflow(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvadd_no_underflow(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsub_no_overflow(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsub_no_overflow(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsub_no_underflow(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool _a3 = (Z3_bool) Bool_val(a3);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsub_no_underflow(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvsdiv_no_overflow(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvsdiv_no_overflow(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvneg_no_overflow(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvneg_no_overflow(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvmul_no_overflow(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool _a3 = (Z3_bool) Bool_val(a3);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvmul_no_overflow(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_bvmul_no_underflow(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bvmul_no_underflow(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_select(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_select(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_store(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast _a3 = * (Z3_ast*) Data_custom_val(a3);
  Z3_ast z3_result;
  z3_result = Z3_mk_store(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_const_array(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_const_array(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_map(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_mk_map(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_mk_array_default(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_array_default(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_set_sort(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_sort z3_result;
  z3_result = Z3_mk_set_sort(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_mk_empty_set(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_empty_set(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_full_set(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_full_set(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_set_add(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_set_add(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_set_del(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_set_del(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_set_union(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_ast z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_set_union(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_mk_set_intersect(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_ast z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_set_intersect(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_mk_set_difference(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_set_difference(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_set_complement(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_mk_set_complement(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_set_member(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_set_member(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_set_subset(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_set_subset(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_numeral(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_numeral(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_real(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  int _a1 = (int) Int_val(a1);
  int _a2 = (int) Int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_real(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_int(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  int _a1 = (int) Int_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_int(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_unsigned_int(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_unsigned_int(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_int64(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  __int64 _a1 = (__int64) Long_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_int64(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_unsigned_int64(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  __uint64 _a1 = (__uint64) Unsigned_long_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_unsigned_int64(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_pattern(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_pattern z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_mk_pattern(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_pattern), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_pattern));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_mk_bound(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_mk_bound(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_forall(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7) {
  CAMLparam8(a0, a1, a2, a3, a4, a5, a6, a7);
  CAMLlocal5(result, res_val, _a3_val, _a5_val, _a6_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_pattern * _a3 = (Z3_pattern*) malloc(sizeof(Z3_pattern) * _a2);
  unsigned _a4 = (unsigned) Unsigned_int_val(a4);
  Z3_sort * _a5 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a4);
  Z3_symbol * _a6 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a4);
  Z3_ast _a7 = * (Z3_ast*) Data_custom_val(a7);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_pattern*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a4; _i++) { _a5[_i] = * (Z3_sort*) Data_custom_val(Field(a5, _i)); }
  for (_i = 0; _i < _a4; _i++) { _a6[_i] = * (Z3_symbol*) Data_custom_val(Field(a6, _i)); }
  z3_result = Z3_mk_forall(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  free(_a5);
  free(_a6);
  CAMLreturn(result);
}

CAMLprim value n_mk_forall_bytecode(value * argv, int argn) {
  return n_mk_forall(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7]);
}


CAMLprim value n_mk_exists(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7) {
  CAMLparam8(a0, a1, a2, a3, a4, a5, a6, a7);
  CAMLlocal5(result, res_val, _a3_val, _a5_val, _a6_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_pattern * _a3 = (Z3_pattern*) malloc(sizeof(Z3_pattern) * _a2);
  unsigned _a4 = (unsigned) Unsigned_int_val(a4);
  Z3_sort * _a5 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a4);
  Z3_symbol * _a6 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a4);
  Z3_ast _a7 = * (Z3_ast*) Data_custom_val(a7);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_pattern*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a4; _i++) { _a5[_i] = * (Z3_sort*) Data_custom_val(Field(a5, _i)); }
  for (_i = 0; _i < _a4; _i++) { _a6[_i] = * (Z3_symbol*) Data_custom_val(Field(a6, _i)); }
  z3_result = Z3_mk_exists(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  free(_a5);
  free(_a6);
  CAMLreturn(result);
}

CAMLprim value n_mk_exists_bytecode(value * argv, int argn) {
  return n_mk_exists(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7]);
}


CAMLprim value n_mk_quantifier(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7, value a8) {
  CAMLparam9(a0, a1, a2, a3, a4, a5, a6, a7, a8);
  CAMLlocal5(result, res_val, _a4_val, _a6_val, _a7_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_bool _a1 = (Z3_bool) Bool_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  Z3_pattern * _a4 = (Z3_pattern*) malloc(sizeof(Z3_pattern) * _a3);
  unsigned _a5 = (unsigned) Unsigned_int_val(a5);
  Z3_sort * _a6 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a5);
  Z3_symbol * _a7 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a5);
  Z3_ast _a8 = * (Z3_ast*) Data_custom_val(a8);
  Z3_ast z3_result;
  for (_i = 0; _i < _a3; _i++) { _a4[_i] = * (Z3_pattern*) Data_custom_val(Field(a4, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a6[_i] = * (Z3_sort*) Data_custom_val(Field(a6, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a7[_i] = * (Z3_symbol*) Data_custom_val(Field(a7, _i)); }
  z3_result = Z3_mk_quantifier(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7, _a8);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a4);
  free(_a6);
  free(_a7);
  CAMLreturn(result);
}

CAMLprim value n_mk_quantifier_bytecode(value * argv, int argn) {
  return n_mk_quantifier(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8]);
}


CAMLprim value n_mk_quantifier_ex(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7, value a8, value a9, value a10, value a11, value a12) {
  CAMLparam13(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12);
  CAMLlocal6(result, res_val, _a6_val, _a8_val, _a10_val, _a11_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_bool _a1 = (Z3_bool) Bool_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol _a3 = * (Z3_symbol*) Data_custom_val(a3);
  Z3_symbol _a4 = * (Z3_symbol*) Data_custom_val(a4);
  unsigned _a5 = (unsigned) Unsigned_int_val(a5);
  Z3_pattern * _a6 = (Z3_pattern*) malloc(sizeof(Z3_pattern) * _a5);
  unsigned _a7 = (unsigned) Unsigned_int_val(a7);
  Z3_ast * _a8 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a7);
  unsigned _a9 = (unsigned) Unsigned_int_val(a9);
  Z3_sort * _a10 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a9);
  Z3_symbol * _a11 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a9);
  Z3_ast _a12 = * (Z3_ast*) Data_custom_val(a12);
  Z3_ast z3_result;
  for (_i = 0; _i < _a5; _i++) { _a6[_i] = * (Z3_pattern*) Data_custom_val(Field(a6, _i)); }
  for (_i = 0; _i < _a7; _i++) { _a8[_i] = * (Z3_ast*) Data_custom_val(Field(a8, _i)); }
  for (_i = 0; _i < _a9; _i++) { _a10[_i] = * (Z3_sort*) Data_custom_val(Field(a10, _i)); }
  for (_i = 0; _i < _a9; _i++) { _a11[_i] = * (Z3_symbol*) Data_custom_val(Field(a11, _i)); }
  z3_result = Z3_mk_quantifier_ex(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7, _a8, _a9, _a10, _a11, _a12);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a6);
  free(_a8);
  free(_a10);
  free(_a11);
  CAMLreturn(result);
}

CAMLprim value n_mk_quantifier_ex_bytecode(value * argv, int argn) {
  return n_mk_quantifier_ex(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8], argv[9], argv[10], argv[11], argv[12]);
}


CAMLprim value n_mk_forall_const(value a0, value a1, value a2, value a3, value a4, value a5, value a6) {
  CAMLparam7(a0, a1, a2, a3, a4, a5, a6);
  CAMLlocal4(result, res_val, _a3_val, _a5_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_app * _a3 = (Z3_app*) malloc(sizeof(Z3_app) * _a2);
  unsigned _a4 = (unsigned) Unsigned_int_val(a4);
  Z3_pattern * _a5 = (Z3_pattern*) malloc(sizeof(Z3_pattern) * _a4);
  Z3_ast _a6 = * (Z3_ast*) Data_custom_val(a6);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_app*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a4; _i++) { _a5[_i] = * (Z3_pattern*) Data_custom_val(Field(a5, _i)); }
  z3_result = Z3_mk_forall_const(_a0, _a1, _a2, _a3, _a4, _a5, _a6);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  free(_a5);
  CAMLreturn(result);
}

CAMLprim value n_mk_forall_const_bytecode(value * argv, int argn) {
  return n_mk_forall_const(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6]);
}


CAMLprim value n_mk_exists_const(value a0, value a1, value a2, value a3, value a4, value a5, value a6) {
  CAMLparam7(a0, a1, a2, a3, a4, a5, a6);
  CAMLlocal4(result, res_val, _a3_val, _a5_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_app * _a3 = (Z3_app*) malloc(sizeof(Z3_app) * _a2);
  unsigned _a4 = (unsigned) Unsigned_int_val(a4);
  Z3_pattern * _a5 = (Z3_pattern*) malloc(sizeof(Z3_pattern) * _a4);
  Z3_ast _a6 = * (Z3_ast*) Data_custom_val(a6);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_app*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a4; _i++) { _a5[_i] = * (Z3_pattern*) Data_custom_val(Field(a5, _i)); }
  z3_result = Z3_mk_exists_const(_a0, _a1, _a2, _a3, _a4, _a5, _a6);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  free(_a5);
  CAMLreturn(result);
}

CAMLprim value n_mk_exists_const_bytecode(value * argv, int argn) {
  return n_mk_exists_const(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6]);
}


CAMLprim value n_mk_quantifier_const(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7) {
  CAMLparam8(a0, a1, a2, a3, a4, a5, a6, a7);
  CAMLlocal4(result, res_val, _a4_val, _a6_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_bool _a1 = (Z3_bool) Bool_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  Z3_app * _a4 = (Z3_app*) malloc(sizeof(Z3_app) * _a3);
  unsigned _a5 = (unsigned) Unsigned_int_val(a5);
  Z3_pattern * _a6 = (Z3_pattern*) malloc(sizeof(Z3_pattern) * _a5);
  Z3_ast _a7 = * (Z3_ast*) Data_custom_val(a7);
  Z3_ast z3_result;
  for (_i = 0; _i < _a3; _i++) { _a4[_i] = * (Z3_app*) Data_custom_val(Field(a4, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a6[_i] = * (Z3_pattern*) Data_custom_val(Field(a6, _i)); }
  z3_result = Z3_mk_quantifier_const(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a4);
  free(_a6);
  CAMLreturn(result);
}

CAMLprim value n_mk_quantifier_const_bytecode(value * argv, int argn) {
  return n_mk_quantifier_const(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7]);
}


CAMLprim value n_mk_quantifier_const_ex(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7, value a8, value a9, value a10, value a11) {
  CAMLparam12(a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11);
  CAMLlocal5(result, res_val, _a6_val, _a8_val, _a10_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_bool _a1 = (Z3_bool) Bool_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol _a3 = * (Z3_symbol*) Data_custom_val(a3);
  Z3_symbol _a4 = * (Z3_symbol*) Data_custom_val(a4);
  unsigned _a5 = (unsigned) Unsigned_int_val(a5);
  Z3_app * _a6 = (Z3_app*) malloc(sizeof(Z3_app) * _a5);
  unsigned _a7 = (unsigned) Unsigned_int_val(a7);
  Z3_pattern * _a8 = (Z3_pattern*) malloc(sizeof(Z3_pattern) * _a7);
  unsigned _a9 = (unsigned) Unsigned_int_val(a9);
  Z3_ast * _a10 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a9);
  Z3_ast _a11 = * (Z3_ast*) Data_custom_val(a11);
  Z3_ast z3_result;
  for (_i = 0; _i < _a5; _i++) { _a6[_i] = * (Z3_app*) Data_custom_val(Field(a6, _i)); }
  for (_i = 0; _i < _a7; _i++) { _a8[_i] = * (Z3_pattern*) Data_custom_val(Field(a8, _i)); }
  for (_i = 0; _i < _a9; _i++) { _a10[_i] = * (Z3_ast*) Data_custom_val(Field(a10, _i)); }
  z3_result = Z3_mk_quantifier_const_ex(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7, _a8, _a9, _a10, _a11);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a6);
  free(_a8);
  free(_a10);
  CAMLreturn(result);
}

CAMLprim value n_mk_quantifier_const_ex_bytecode(value * argv, int argn) {
  return n_mk_quantifier_const_ex(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7], argv[8], argv[9], argv[10], argv[11]);
}


CAMLprim value n_get_symbol_kind(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_symbol_kind(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_symbol_int(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  int z3_result;
  z3_result = Z3_get_symbol_int(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_symbol_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_get_symbol_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_sort_name(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_symbol z3_result;
  z3_result = Z3_get_sort_name(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_symbol), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_symbol));
  CAMLreturn(result);
}

CAMLprim value n_get_sort_id(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_sort_id(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_sort_to_ast(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_sort_to_ast(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_is_eq_sort(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_is_eq_sort(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_sort_kind(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_sort_kind(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_bv_sort_size(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_bv_sort_size(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_finite_domain_sort_size(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal3(result, res_val, _a2_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  __uint64 _a2;
  Z3_bool z3_result;
  z3_result = Z3_get_finite_domain_sort_size(_a0, _a1, &_a2);
  res_val = Val_bool(z3_result);
  _a2_val = Val_long(_a2);
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a2_val);
  CAMLreturn(result);
}

CAMLprim value n_get_array_sort_domain(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_sort z3_result;
  z3_result = Z3_get_array_sort_domain(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_get_array_sort_range(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_sort z3_result;
  z3_result = Z3_get_array_sort_range(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_get_tuple_sort_mk_decl(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_func_decl z3_result;
  z3_result = Z3_get_tuple_sort_mk_decl(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_tuple_sort_num_fields(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_tuple_sort_num_fields(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_tuple_sort_field_decl(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl z3_result;
  z3_result = Z3_get_tuple_sort_field_decl(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_datatype_sort_num_constructors(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_datatype_sort_num_constructors(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_datatype_sort_constructor(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl z3_result;
  z3_result = Z3_get_datatype_sort_constructor(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_datatype_sort_recognizer(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl z3_result;
  z3_result = Z3_get_datatype_sort_recognizer(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_datatype_sort_constructor_accessor(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  Z3_func_decl z3_result;
  z3_result = Z3_get_datatype_sort_constructor_accessor(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_relation_arity(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_relation_arity(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_relation_column(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_sort z3_result;
  z3_result = Z3_get_relation_column(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_func_decl_to_ast(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_func_decl_to_ast(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_is_eq_func_decl(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  Z3_func_decl _a2 = * (Z3_func_decl*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_is_eq_func_decl(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_func_decl_id(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_func_decl_id(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_decl_name(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  Z3_symbol z3_result;
  z3_result = Z3_get_decl_name(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_symbol), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_symbol));
  CAMLreturn(result);
}

CAMLprim value n_get_decl_kind(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_decl_kind(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_domain_size(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_domain_size(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_arity(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_arity(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_domain(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_sort z3_result;
  z3_result = Z3_get_domain(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_get_range(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  Z3_sort z3_result;
  z3_result = Z3_get_range(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_get_decl_num_parameters(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_decl_num_parameters(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_decl_parameter_kind(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  unsigned z3_result;
  z3_result = Z3_get_decl_parameter_kind(_a0, _a1, _a2);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_decl_int_parameter(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  int z3_result;
  z3_result = Z3_get_decl_int_parameter(_a0, _a1, _a2);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_decl_double_parameter(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  double z3_result;
  z3_result = Z3_get_decl_double_parameter(_a0, _a1, _a2);
  Store_double_val(result, z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_decl_symbol_parameter(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol z3_result;
  z3_result = Z3_get_decl_symbol_parameter(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_symbol), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_symbol));
  CAMLreturn(result);
}

CAMLprim value n_get_decl_sort_parameter(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_sort z3_result;
  z3_result = Z3_get_decl_sort_parameter(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_get_decl_ast_parameter(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_get_decl_ast_parameter(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_decl_func_decl_parameter(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl z3_result;
  z3_result = Z3_get_decl_func_decl_parameter(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_decl_rational_parameter(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_string z3_result;
  z3_result = Z3_get_decl_rational_parameter(_a0, _a1, _a2);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_app_to_ast(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_app _a1 = * (Z3_app*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_app_to_ast(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_app_decl(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_app _a1 = * (Z3_app*) Data_custom_val(a1);
  Z3_func_decl z3_result;
  z3_result = Z3_get_app_decl(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_app_num_args(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_app _a1 = * (Z3_app*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_app_num_args(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_app_arg(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_app _a1 = * (Z3_app*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_get_app_arg(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_is_eq_ast(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_is_eq_ast(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_ast_id(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_ast_id(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_ast_hash(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_ast_hash(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_sort(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_sort z3_result;
  z3_result = Z3_get_sort(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_is_well_sorted(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_is_well_sorted(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_bool_value(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_bool_value(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_ast_kind(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_ast_kind(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_is_app(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_is_app(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_is_numeral_ast(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_is_numeral_ast(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_is_algebraic_number(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_is_algebraic_number(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_to_app(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_app z3_result;
  z3_result = Z3_to_app(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_app), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_app));
  CAMLreturn(result);
}

CAMLprim value n_to_func_decl(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_func_decl z3_result;
  z3_result = Z3_to_func_decl(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_numeral_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_get_numeral_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_numeral_decimal_string(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_string z3_result;
  z3_result = Z3_get_numeral_decimal_string(_a0, _a1, _a2);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_numerator(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_get_numerator(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_denominator(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_get_denominator(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_numeral_small(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal4(result, res_val, _a2_val, _a3_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  __int64 _a2;
  __int64 _a3;
  Z3_bool z3_result;
  z3_result = Z3_get_numeral_small(_a0, _a1, &_a2, &_a3);
  res_val = Val_bool(z3_result);
  _a2_val = Val_long(_a2);
  _a3_val = Val_long(_a3);
  result = caml_alloc(3, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a2_val);
  Store_field(result, 2, _a3_val);
  CAMLreturn(result);
}

CAMLprim value n_get_numeral_int(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal3(result, res_val, _a2_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  int _a2;
  Z3_bool z3_result;
  z3_result = Z3_get_numeral_int(_a0, _a1, &_a2);
  res_val = Val_bool(z3_result);
  _a2_val = Val_int(_a2);
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a2_val);
  CAMLreturn(result);
}

CAMLprim value n_get_numeral_uint(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal3(result, res_val, _a2_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2;
  Z3_bool z3_result;
  z3_result = Z3_get_numeral_uint(_a0, _a1, &_a2);
  res_val = Val_bool(z3_result);
  _a2_val = Val_int(_a2);
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a2_val);
  CAMLreturn(result);
}

CAMLprim value n_get_numeral_uint64(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal3(result, res_val, _a2_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  __uint64 _a2;
  Z3_bool z3_result;
  z3_result = Z3_get_numeral_uint64(_a0, _a1, &_a2);
  res_val = Val_bool(z3_result);
  _a2_val = Val_long(_a2);
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a2_val);
  CAMLreturn(result);
}

CAMLprim value n_get_numeral_int64(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal3(result, res_val, _a2_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  __int64 _a2;
  Z3_bool z3_result;
  z3_result = Z3_get_numeral_int64(_a0, _a1, &_a2);
  res_val = Val_bool(z3_result);
  _a2_val = Val_long(_a2);
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a2_val);
  CAMLreturn(result);
}

CAMLprim value n_get_numeral_rational_int64(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal4(result, res_val, _a2_val, _a3_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  __int64 _a2;
  __int64 _a3;
  Z3_bool z3_result;
  z3_result = Z3_get_numeral_rational_int64(_a0, _a1, &_a2, &_a3);
  res_val = Val_bool(z3_result);
  _a2_val = Val_long(_a2);
  _a3_val = Val_long(_a3);
  result = caml_alloc(3, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a2_val);
  Store_field(result, 2, _a3_val);
  CAMLreturn(result);
}

CAMLprim value n_get_algebraic_number_lower(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_get_algebraic_number_lower(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_algebraic_number_upper(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_get_algebraic_number_upper(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_pattern_to_ast(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_pattern _a1 = * (Z3_pattern*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_pattern_to_ast(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_pattern_num_terms(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_pattern _a1 = * (Z3_pattern*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_pattern_num_terms(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_pattern(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_pattern _a1 = * (Z3_pattern*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_get_pattern(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_index_value(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_index_value(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_is_quantifier_forall(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_is_quantifier_forall(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_quantifier_weight(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_quantifier_weight(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_quantifier_num_patterns(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_quantifier_num_patterns(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_quantifier_pattern_ast(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_pattern z3_result;
  z3_result = Z3_get_quantifier_pattern_ast(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_pattern), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_pattern));
  CAMLreturn(result);
}

CAMLprim value n_get_quantifier_num_no_patterns(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_quantifier_num_no_patterns(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_quantifier_no_pattern_ast(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_get_quantifier_no_pattern_ast(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_quantifier_num_bound(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_quantifier_num_bound(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_quantifier_bound_name(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol z3_result;
  z3_result = Z3_get_quantifier_bound_name(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_symbol), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_symbol));
  CAMLreturn(result);
}

CAMLprim value n_get_quantifier_bound_sort(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_sort z3_result;
  z3_result = Z3_get_quantifier_bound_sort(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_get_quantifier_body(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_get_quantifier_body(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_simplify(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_simplify(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_simplify_ex(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_params _a2 = * (Z3_params*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_simplify_ex(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_simplify_get_help(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string z3_result;
  z3_result = Z3_simplify_get_help(_a0);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_simplify_get_param_descrs(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_param_descrs z3_result;
  z3_result = Z3_simplify_get_param_descrs(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_param_descrs), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_param_descrs));
  CAMLreturn(result);
}

CAMLprim value n_update_term(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_update_term(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_substitute(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal4(result, res_val, _a3_val, _a4_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  Z3_ast * _a4 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a2; _i++) { _a4[_i] = * (Z3_ast*) Data_custom_val(Field(a4, _i)); }
  z3_result = Z3_substitute(_a0, _a1, _a2, _a3, _a4);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  free(_a4);
  CAMLreturn(result);
}

CAMLprim value n_substitute_vars(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_substitute_vars(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_translate(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_context _a2 = * (Z3_context*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_translate(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_model_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_model_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_model_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_model_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_model_eval(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a4_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool _a3 = (Z3_bool) Bool_val(a3);
  Z3_ast _a4;
  Z3_bool z3_result;
  z3_result = Z3_model_eval(_a0, _a1, _a2, _a3, &_a4);
  res_val = Val_bool(z3_result);
  _a4_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(_a4_val), &_a4, sizeof(Z3_ast));
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a4_val);
  CAMLreturn(result);
}

CAMLprim value n_model_get_const_interp(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_func_decl _a2 = * (Z3_func_decl*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_model_get_const_interp(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_model_get_func_interp(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_func_decl _a2 = * (Z3_func_decl*) Data_custom_val(a2);
  Z3_func_interp z3_result;
  z3_result = Z3_model_get_func_interp(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_interp), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_interp));
  CAMLreturn(result);
}

CAMLprim value n_model_get_num_consts(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_model_get_num_consts(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_model_get_const_decl(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl z3_result;
  z3_result = Z3_model_get_const_decl(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_model_get_num_funcs(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_model_get_num_funcs(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_model_get_func_decl(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl z3_result;
  z3_result = Z3_model_get_func_decl(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_model_get_num_sorts(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_model_get_num_sorts(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_model_get_sort(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_sort z3_result;
  z3_result = Z3_model_get_sort(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_model_get_sort_universe(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_sort _a2 = * (Z3_sort*) Data_custom_val(a2);
  Z3_ast_vector z3_result;
  z3_result = Z3_model_get_sort_universe(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_is_as_array(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_is_as_array(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_as_array_func_decl(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_func_decl z3_result;
  z3_result = Z3_get_as_array_func_decl(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_func_interp_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_interp _a1 = * (Z3_func_interp*) Data_custom_val(a1);
  Z3_func_interp_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_func_interp_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_interp _a1 = * (Z3_func_interp*) Data_custom_val(a1);
  Z3_func_interp_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_func_interp_get_num_entries(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_interp _a1 = * (Z3_func_interp*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_func_interp_get_num_entries(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_func_interp_get_entry(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_interp _a1 = * (Z3_func_interp*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_entry z3_result;
  z3_result = Z3_func_interp_get_entry(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_entry), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_entry));
  CAMLreturn(result);
}

CAMLprim value n_func_interp_get_else(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_interp _a1 = * (Z3_func_interp*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_func_interp_get_else(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_func_interp_get_arity(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_interp _a1 = * (Z3_func_interp*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_func_interp_get_arity(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_func_entry_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_entry _a1 = * (Z3_func_entry*) Data_custom_val(a1);
  Z3_func_entry_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_func_entry_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_entry _a1 = * (Z3_func_entry*) Data_custom_val(a1);
  Z3_func_entry_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_func_entry_get_value(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_entry _a1 = * (Z3_func_entry*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_func_entry_get_value(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_func_entry_get_num_args(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_entry _a1 = * (Z3_func_entry*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_func_entry_get_num_args(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_func_entry_get_arg(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_entry _a1 = * (Z3_func_entry*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_func_entry_get_arg(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_open_log(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_string _a0 = (Z3_string) String_val(a0);
  int z3_result;
  z3_result = Z3_open_log(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_append_log(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_string _a0 = (Z3_string) String_val(a0);
  Z3_append_log(_a0);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_close_log() {
  CAMLparam0();
  CAMLlocal1(result);
  Z3_close_log();
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_toggle_warning_messages(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_bool _a0 = (Z3_bool) Bool_val(a0);
  Z3_toggle_warning_messages(_a0);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_set_ast_print_mode(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_print_mode _a1 = (Z3_ast_print_mode) Int_val(a1);
  Z3_set_ast_print_mode(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_ast_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_pattern_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_pattern _a1 = * (Z3_pattern*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_pattern_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_sort_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_sort _a1 = * (Z3_sort*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_sort_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_func_decl_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_func_decl _a1 = * (Z3_func_decl*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_func_decl_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_model_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_model_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_benchmark_to_smtlib_string(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7) {
  CAMLparam8(a0, a1, a2, a3, a4, a5, a6, a7);
  CAMLlocal3(result, res_val, _a6_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_string _a2 = (Z3_string) String_val(a2);
  Z3_string _a3 = (Z3_string) String_val(a3);
  Z3_string _a4 = (Z3_string) String_val(a4);
  unsigned _a5 = (unsigned) Unsigned_int_val(a5);
  Z3_ast * _a6 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a5);
  Z3_ast _a7 = * (Z3_ast*) Data_custom_val(a7);
  Z3_string z3_result;
  for (_i = 0; _i < _a5; _i++) { _a6[_i] = * (Z3_ast*) Data_custom_val(Field(a6, _i)); }
  z3_result = Z3_benchmark_to_smtlib_string(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7);
  result = caml_copy_string((const char*) z3_result);
  free(_a6);
  CAMLreturn(result);
}

CAMLprim value n_benchmark_to_smtlib_string_bytecode(value * argv, int argn) {
  return n_benchmark_to_smtlib_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7]);
}


CAMLprim value n_parse_smtlib2_string(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7) {
  CAMLparam8(a0, a1, a2, a3, a4, a5, a6, a7);
  CAMLlocal6(result, res_val, _a3_val, _a4_val, _a6_val, _a7_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol * _a3 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a2);
  Z3_sort * _a4 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a2);
  unsigned _a5 = (unsigned) Unsigned_int_val(a5);
  Z3_symbol * _a6 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a5);
  Z3_func_decl * _a7 = (Z3_func_decl*) malloc(sizeof(Z3_func_decl) * _a5);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_symbol*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a2; _i++) { _a4[_i] = * (Z3_sort*) Data_custom_val(Field(a4, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a6[_i] = * (Z3_symbol*) Data_custom_val(Field(a6, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a7[_i] = * (Z3_func_decl*) Data_custom_val(Field(a7, _i)); }
  z3_result = Z3_parse_smtlib2_string(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  free(_a4);
  free(_a6);
  free(_a7);
  CAMLreturn(result);
}

CAMLprim value n_parse_smtlib2_string_bytecode(value * argv, int argn) {
  return n_parse_smtlib2_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7]);
}


CAMLprim value n_parse_smtlib2_file(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7) {
  CAMLparam8(a0, a1, a2, a3, a4, a5, a6, a7);
  CAMLlocal6(result, res_val, _a3_val, _a4_val, _a6_val, _a7_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol * _a3 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a2);
  Z3_sort * _a4 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a2);
  unsigned _a5 = (unsigned) Unsigned_int_val(a5);
  Z3_symbol * _a6 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a5);
  Z3_func_decl * _a7 = (Z3_func_decl*) malloc(sizeof(Z3_func_decl) * _a5);
  Z3_ast z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_symbol*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a2; _i++) { _a4[_i] = * (Z3_sort*) Data_custom_val(Field(a4, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a6[_i] = * (Z3_symbol*) Data_custom_val(Field(a6, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a7[_i] = * (Z3_func_decl*) Data_custom_val(Field(a7, _i)); }
  z3_result = Z3_parse_smtlib2_file(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  free(_a3);
  free(_a4);
  free(_a6);
  free(_a7);
  CAMLreturn(result);
}

CAMLprim value n_parse_smtlib2_file_bytecode(value * argv, int argn) {
  return n_parse_smtlib2_file(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7]);
}


CAMLprim value n_parse_smtlib_string(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7) {
  CAMLparam8(a0, a1, a2, a3, a4, a5, a6, a7);
  CAMLlocal6(result, res_val, _a3_val, _a4_val, _a6_val, _a7_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol * _a3 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a2);
  Z3_sort * _a4 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a2);
  unsigned _a5 = (unsigned) Unsigned_int_val(a5);
  Z3_symbol * _a6 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a5);
  Z3_func_decl * _a7 = (Z3_func_decl*) malloc(sizeof(Z3_func_decl) * _a5);
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_symbol*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a2; _i++) { _a4[_i] = * (Z3_sort*) Data_custom_val(Field(a4, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a6[_i] = * (Z3_symbol*) Data_custom_val(Field(a6, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a7[_i] = * (Z3_func_decl*) Data_custom_val(Field(a7, _i)); }
  Z3_parse_smtlib_string(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7);
  result = Val_unit;
  free(_a3);
  free(_a4);
  free(_a6);
  free(_a7);
  CAMLreturn(result);
}

CAMLprim value n_parse_smtlib_string_bytecode(value * argv, int argn) {
  return n_parse_smtlib_string(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7]);
}


CAMLprim value n_parse_smtlib_file(value a0, value a1, value a2, value a3, value a4, value a5, value a6, value a7) {
  CAMLparam8(a0, a1, a2, a3, a4, a5, a6, a7);
  CAMLlocal6(result, res_val, _a3_val, _a4_val, _a6_val, _a7_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol * _a3 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a2);
  Z3_sort * _a4 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a2);
  unsigned _a5 = (unsigned) Unsigned_int_val(a5);
  Z3_symbol * _a6 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a5);
  Z3_func_decl * _a7 = (Z3_func_decl*) malloc(sizeof(Z3_func_decl) * _a5);
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_symbol*) Data_custom_val(Field(a3, _i)); }
  for (_i = 0; _i < _a2; _i++) { _a4[_i] = * (Z3_sort*) Data_custom_val(Field(a4, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a6[_i] = * (Z3_symbol*) Data_custom_val(Field(a6, _i)); }
  for (_i = 0; _i < _a5; _i++) { _a7[_i] = * (Z3_func_decl*) Data_custom_val(Field(a7, _i)); }
  Z3_parse_smtlib_file(_a0, _a1, _a2, _a3, _a4, _a5, _a6, _a7);
  result = Val_unit;
  free(_a3);
  free(_a4);
  free(_a6);
  free(_a7);
  CAMLreturn(result);
}

CAMLprim value n_parse_smtlib_file_bytecode(value * argv, int argn) {
  return n_parse_smtlib_file(argv[0], argv[1], argv[2], argv[3], argv[4], argv[5], argv[6], argv[7]);
}


CAMLprim value n_get_smtlib_num_formulas(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned z3_result;
  z3_result = Z3_get_smtlib_num_formulas(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_smtlib_formula(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_get_smtlib_formula(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_smtlib_num_assumptions(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned z3_result;
  z3_result = Z3_get_smtlib_num_assumptions(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_smtlib_assumption(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_get_smtlib_assumption(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_smtlib_num_decls(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned z3_result;
  z3_result = Z3_get_smtlib_num_decls(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_smtlib_decl(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_func_decl z3_result;
  z3_result = Z3_get_smtlib_decl(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_smtlib_num_sorts(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned z3_result;
  z3_result = Z3_get_smtlib_num_sorts(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_smtlib_sort(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_sort z3_result;
  z3_result = Z3_get_smtlib_sort(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_sort), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_sort));
  CAMLreturn(result);
}

CAMLprim value n_get_smtlib_error(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string z3_result;
  z3_result = Z3_get_smtlib_error(_a0);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_error_code(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned z3_result;
  z3_result = Z3_get_error_code(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_set_error(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_error_code _a1 = (Z3_error_code) Int_val(a1);
  Z3_set_error(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_get_error_msg(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_error_code _a0 = (Z3_error_code) Int_val(a0);
  Z3_string z3_result;
  z3_result = Z3_get_error_msg(_a0);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_error_msg_ex(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_error_code _a1 = (Z3_error_code) Int_val(a1);
  Z3_string z3_result;
  z3_result = Z3_get_error_msg_ex(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_version() {
  CAMLparam0();
  CAMLlocal6(result, res_val, _a0_val, _a1_val, _a2_val, _a3_val);
  unsigned _a0;
  unsigned _a1;
  unsigned _a2;
  unsigned _a3;
  Z3_get_version(&_a0, &_a1, &_a2, &_a3);
  _a0_val = Val_int(_a0);
  _a1_val = Val_int(_a1);
  _a2_val = Val_int(_a2);
  _a3_val = Val_int(_a3);
  result = caml_alloc(4, 0);
  Store_field(result, 0, _a0_val);
  Store_field(result, 1, _a1_val);
  Store_field(result, 2, _a2_val);
  Store_field(result, 3, _a3_val);
  CAMLreturn(result);
}

CAMLprim value n_enable_trace(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_string _a0 = (Z3_string) String_val(a0);
  Z3_enable_trace(_a0);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_disable_trace(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_string _a0 = (Z3_string) String_val(a0);
  Z3_disable_trace(_a0);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_reset_memory() {
  CAMLparam0();
  CAMLlocal1(result);
  Z3_reset_memory();
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_mk_fixedpoint(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint z3_result;
  z3_result = Z3_mk_fixedpoint(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_fixedpoint), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_fixedpoint));
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_fixedpoint_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_fixedpoint_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_add_rule(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_symbol _a3 = * (Z3_symbol*) Data_custom_val(a3);
  Z3_fixedpoint_add_rule(_a0, _a1, _a2, _a3);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_add_fact(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal3(result, res_val, _a4_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_func_decl _a2 = * (Z3_func_decl*) Data_custom_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  unsigned * _a4 = (unsigned*) malloc(sizeof(unsigned) * _a3);
  for (_i = 0; _i < _a3; _i++) { _a4[_i] = (unsigned) Unsigned_int_val(Field(a4, _i)); }
  Z3_fixedpoint_add_fact(_a0, _a1, _a2, _a3, _a4);
  result = Val_unit;
  free(_a4);
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_assert(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_fixedpoint_assert(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_query(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  int z3_result;
  z3_result = Z3_fixedpoint_query(_a0, _a1, _a2);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_query_relations(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl * _a3 = (Z3_func_decl*) malloc(sizeof(Z3_func_decl) * _a2);
  int z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_func_decl*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_fixedpoint_query_relations(_a0, _a1, _a2, _a3);
  result = Val_int(z3_result);
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_get_answer(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_fixedpoint_get_answer(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_get_reason_unknown(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_fixedpoint_get_reason_unknown(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_update_rule(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_symbol _a3 = * (Z3_symbol*) Data_custom_val(a3);
  Z3_fixedpoint_update_rule(_a0, _a1, _a2, _a3);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_get_num_levels(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_func_decl _a2 = * (Z3_func_decl*) Data_custom_val(a2);
  unsigned z3_result;
  z3_result = Z3_fixedpoint_get_num_levels(_a0, _a1, _a2);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_get_cover_delta(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  int _a2 = (int) Int_val(a2);
  Z3_func_decl _a3 = * (Z3_func_decl*) Data_custom_val(a3);
  Z3_ast z3_result;
  z3_result = Z3_fixedpoint_get_cover_delta(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_add_cover(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  int _a2 = (int) Int_val(a2);
  Z3_func_decl _a3 = * (Z3_func_decl*) Data_custom_val(a3);
  Z3_ast _a4 = * (Z3_ast*) Data_custom_val(a4);
  Z3_fixedpoint_add_cover(_a0, _a1, _a2, _a3, _a4);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_get_statistics(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_stats z3_result;
  z3_result = Z3_fixedpoint_get_statistics(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_stats), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_stats));
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_register_relation(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_func_decl _a2 = * (Z3_func_decl*) Data_custom_val(a2);
  Z3_fixedpoint_register_relation(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_set_predicate_representation(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal3(result, res_val, _a4_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_func_decl _a2 = * (Z3_func_decl*) Data_custom_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  Z3_symbol * _a4 = (Z3_symbol*) malloc(sizeof(Z3_symbol) * _a3);
  for (_i = 0; _i < _a3; _i++) { _a4[_i] = * (Z3_symbol*) Data_custom_val(Field(a4, _i)); }
  Z3_fixedpoint_set_predicate_representation(_a0, _a1, _a2, _a3, _a4);
  result = Val_unit;
  free(_a4);
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_get_rules(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_ast_vector z3_result;
  z3_result = Z3_fixedpoint_get_rules(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_get_assertions(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_ast_vector z3_result;
  z3_result = Z3_fixedpoint_get_assertions(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_set_params(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_params _a2 = * (Z3_params*) Data_custom_val(a2);
  Z3_fixedpoint_set_params(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_get_help(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_fixedpoint_get_help(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_get_param_descrs(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_param_descrs z3_result;
  z3_result = Z3_fixedpoint_get_param_descrs(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_param_descrs), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_param_descrs));
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_to_string(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  Z3_string z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_fixedpoint_to_string(_a0, _a1, _a2, _a3);
  result = caml_copy_string((const char*) z3_result);
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_from_string(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_string _a2 = (Z3_string) String_val(a2);
  Z3_ast_vector z3_result;
  z3_result = Z3_fixedpoint_from_string(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_from_file(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_string _a2 = (Z3_string) String_val(a2);
  Z3_ast_vector z3_result;
  z3_result = Z3_fixedpoint_from_file(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_push(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_fixedpoint_push(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_fixedpoint_pop(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_fixedpoint _a1 = * (Z3_fixedpoint*) Data_custom_val(a1);
  Z3_fixedpoint_pop(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_mk_ast_vector(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector z3_result;
  z3_result = Z3_mk_ast_vector(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_ast_vector_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector _a1 = * (Z3_ast_vector*) Data_custom_val(a1);
  Z3_ast_vector_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_vector_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector _a1 = * (Z3_ast_vector*) Data_custom_val(a1);
  Z3_ast_vector_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_vector_size(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector _a1 = * (Z3_ast_vector*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_ast_vector_size(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_ast_vector_get(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector _a1 = * (Z3_ast_vector*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_ast_vector_get(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_ast_vector_set(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector _a1 = * (Z3_ast_vector*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast _a3 = * (Z3_ast*) Data_custom_val(a3);
  Z3_ast_vector_set(_a0, _a1, _a2, _a3);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_vector_resize(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector _a1 = * (Z3_ast_vector*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast_vector_resize(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_vector_push(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector _a1 = * (Z3_ast_vector*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast_vector_push(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_vector_translate(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector _a1 = * (Z3_ast_vector*) Data_custom_val(a1);
  Z3_context _a2 = * (Z3_context*) Data_custom_val(a2);
  Z3_ast_vector z3_result;
  z3_result = Z3_ast_vector_translate(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_ast_vector_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_vector _a1 = * (Z3_ast_vector*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_ast_vector_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_mk_ast_map(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map z3_result;
  z3_result = Z3_mk_ast_map(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_map), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_map));
  CAMLreturn(result);
}

CAMLprim value n_ast_map_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  Z3_ast_map_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_map_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  Z3_ast_map_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_map_contains(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_ast_map_contains(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_ast_map_find(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_ast_map_find(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_ast_map_insert(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast _a3 = * (Z3_ast*) Data_custom_val(a3);
  Z3_ast_map_insert(_a0, _a1, _a2, _a3);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_map_erase(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast_map_erase(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_map_reset(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  Z3_ast_map_reset(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_ast_map_size(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_ast_map_size(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_ast_map_keys(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  Z3_ast_vector z3_result;
  z3_result = Z3_ast_map_keys(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_ast_map_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast_map _a1 = * (Z3_ast_map*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_ast_map_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_mk_goal(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_bool _a1 = (Z3_bool) Bool_val(a1);
  Z3_bool _a2 = (Z3_bool) Bool_val(a2);
  Z3_bool _a3 = (Z3_bool) Bool_val(a3);
  Z3_goal z3_result;
  z3_result = Z3_mk_goal(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_goal), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_goal));
  CAMLreturn(result);
}

CAMLprim value n_goal_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  Z3_goal_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_goal_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  Z3_goal_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_goal_precision(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_goal_precision(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_goal_assert(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_goal_assert(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_goal_inconsistent(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_goal_inconsistent(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_goal_depth(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_goal_depth(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_goal_reset(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  Z3_goal_reset(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_goal_size(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_goal_size(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_goal_formula(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_goal_formula(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_goal_num_exprs(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_goal_num_exprs(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_goal_is_decided_sat(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_goal_is_decided_sat(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_goal_is_decided_unsat(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_goal_is_decided_unsat(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_goal_translate(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  Z3_context _a2 = * (Z3_context*) Data_custom_val(a2);
  Z3_goal z3_result;
  z3_result = Z3_goal_translate(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_goal), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_goal));
  CAMLreturn(result);
}

CAMLprim value n_goal_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_goal _a1 = * (Z3_goal*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_goal_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_mk_tactic(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_tactic z3_result;
  z3_result = Z3_mk_tactic(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_tactic_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_tactic_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_tactic_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_mk_probe(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_probe z3_result;
  z3_result = Z3_mk_probe(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_probe_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_probe_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_tactic_and_then(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_tactic _a2 = * (Z3_tactic*) Data_custom_val(a2);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_and_then(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_or_else(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_tactic _a2 = * (Z3_tactic*) Data_custom_val(a2);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_or_else(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_par_or(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a2_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_tactic * _a2 = (Z3_tactic*) malloc(sizeof(Z3_tactic) * _a1);
  Z3_tactic z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_tactic*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_tactic_par_or(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  free(_a2);
  CAMLreturn(result);
}

CAMLprim value n_tactic_par_and_then(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_tactic _a2 = * (Z3_tactic*) Data_custom_val(a2);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_par_and_then(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_try_for(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_try_for(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_when(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_tactic _a2 = * (Z3_tactic*) Data_custom_val(a2);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_when(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_cond(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_tactic _a2 = * (Z3_tactic*) Data_custom_val(a2);
  Z3_tactic _a3 = * (Z3_tactic*) Data_custom_val(a3);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_cond(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_repeat(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_repeat(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_skip(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_skip(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_fail(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_fail(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_fail_if(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_fail_if(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_fail_if_not_decided(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_fail_if_not_decided(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_tactic_using_params(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_params _a2 = * (Z3_params*) Data_custom_val(a2);
  Z3_tactic z3_result;
  z3_result = Z3_tactic_using_params(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_tactic), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_tactic));
  CAMLreturn(result);
}

CAMLprim value n_probe_const(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  double _a1 = (double) Double_val(a1);
  Z3_probe z3_result;
  z3_result = Z3_probe_const(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_probe_lt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe _a2 = * (Z3_probe*) Data_custom_val(a2);
  Z3_probe z3_result;
  z3_result = Z3_probe_lt(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_probe_gt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe _a2 = * (Z3_probe*) Data_custom_val(a2);
  Z3_probe z3_result;
  z3_result = Z3_probe_gt(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_probe_le(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe _a2 = * (Z3_probe*) Data_custom_val(a2);
  Z3_probe z3_result;
  z3_result = Z3_probe_le(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_probe_ge(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe _a2 = * (Z3_probe*) Data_custom_val(a2);
  Z3_probe z3_result;
  z3_result = Z3_probe_ge(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_probe_eq(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe _a2 = * (Z3_probe*) Data_custom_val(a2);
  Z3_probe z3_result;
  z3_result = Z3_probe_eq(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_probe_and(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe _a2 = * (Z3_probe*) Data_custom_val(a2);
  Z3_probe z3_result;
  z3_result = Z3_probe_and(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_probe_or(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe _a2 = * (Z3_probe*) Data_custom_val(a2);
  Z3_probe z3_result;
  z3_result = Z3_probe_or(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_probe_not(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_probe z3_result;
  z3_result = Z3_probe_not(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_probe), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_probe));
  CAMLreturn(result);
}

CAMLprim value n_get_num_tactics(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned z3_result;
  z3_result = Z3_get_num_tactics(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_tactic_name(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_string z3_result;
  z3_result = Z3_get_tactic_name(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_num_probes(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned z3_result;
  z3_result = Z3_get_num_probes(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_probe_name(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_string z3_result;
  z3_result = Z3_get_probe_name(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_tactic_get_help(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_tactic_get_help(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_tactic_get_param_descrs(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_param_descrs z3_result;
  z3_result = Z3_tactic_get_param_descrs(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_param_descrs), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_param_descrs));
  CAMLreturn(result);
}

CAMLprim value n_tactic_get_descr(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_string z3_result;
  z3_result = Z3_tactic_get_descr(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_probe_get_descr(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_string z3_result;
  z3_result = Z3_probe_get_descr(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_probe_apply(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_probe _a1 = * (Z3_probe*) Data_custom_val(a1);
  Z3_goal _a2 = * (Z3_goal*) Data_custom_val(a2);
  double z3_result;
  z3_result = Z3_probe_apply(_a0, _a1, _a2);
  Store_double_val(result, z3_result);
  CAMLreturn(result);
}

CAMLprim value n_tactic_apply(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_goal _a2 = * (Z3_goal*) Data_custom_val(a2);
  Z3_apply_result z3_result;
  z3_result = Z3_tactic_apply(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_apply_result), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_apply_result));
  CAMLreturn(result);
}

CAMLprim value n_tactic_apply_ex(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_goal _a2 = * (Z3_goal*) Data_custom_val(a2);
  Z3_params _a3 = * (Z3_params*) Data_custom_val(a3);
  Z3_apply_result z3_result;
  z3_result = Z3_tactic_apply_ex(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_apply_result), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_apply_result));
  CAMLreturn(result);
}

CAMLprim value n_apply_result_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_apply_result _a1 = * (Z3_apply_result*) Data_custom_val(a1);
  Z3_apply_result_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_apply_result_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_apply_result _a1 = * (Z3_apply_result*) Data_custom_val(a1);
  Z3_apply_result_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_apply_result_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_apply_result _a1 = * (Z3_apply_result*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_apply_result_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_apply_result_get_num_subgoals(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_apply_result _a1 = * (Z3_apply_result*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_apply_result_get_num_subgoals(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_apply_result_get_subgoal(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_apply_result _a1 = * (Z3_apply_result*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_goal z3_result;
  z3_result = Z3_apply_result_get_subgoal(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_goal), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_goal));
  CAMLreturn(result);
}

CAMLprim value n_apply_result_convert_model(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_apply_result _a1 = * (Z3_apply_result*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_model _a3 = * (Z3_model*) Data_custom_val(a3);
  Z3_model z3_result;
  z3_result = Z3_apply_result_convert_model(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_model), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_model));
  CAMLreturn(result);
}

CAMLprim value n_mk_solver(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver z3_result;
  z3_result = Z3_mk_solver(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_solver), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_solver));
  CAMLreturn(result);
}

CAMLprim value n_mk_simple_solver(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver z3_result;
  z3_result = Z3_mk_simple_solver(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_solver), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_solver));
  CAMLreturn(result);
}

CAMLprim value n_mk_solver_for_logic(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  Z3_solver z3_result;
  z3_result = Z3_mk_solver_for_logic(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_solver), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_solver));
  CAMLreturn(result);
}

CAMLprim value n_mk_solver_from_tactic(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_tactic _a1 = * (Z3_tactic*) Data_custom_val(a1);
  Z3_solver z3_result;
  z3_result = Z3_mk_solver_from_tactic(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_solver), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_solver));
  CAMLreturn(result);
}

CAMLprim value n_solver_get_help(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_solver_get_help(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_solver_get_param_descrs(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_param_descrs z3_result;
  z3_result = Z3_solver_get_param_descrs(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_param_descrs), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_param_descrs));
  CAMLreturn(result);
}

CAMLprim value n_solver_set_params(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_params _a2 = * (Z3_params*) Data_custom_val(a2);
  Z3_solver_set_params(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_solver_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_solver_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_solver_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_solver_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_solver_push(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_solver_push(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_solver_pop(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_solver_pop(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_solver_reset(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_solver_reset(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_solver_get_num_scopes(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_solver_get_num_scopes(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_solver_assert(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_solver_assert(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_solver_assert_and_track(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast _a3 = * (Z3_ast*) Data_custom_val(a3);
  Z3_solver_assert_and_track(_a0, _a1, _a2, _a3);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_solver_get_assertions(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_ast_vector z3_result;
  z3_result = Z3_solver_get_assertions(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_solver_check(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  int z3_result;
  z3_result = Z3_solver_check(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_solver_check_assumptions(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  int z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_solver_check_assumptions(_a0, _a1, _a2, _a3);
  result = Val_int(z3_result);
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_solver_get_model(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_model z3_result;
  z3_result = Z3_solver_get_model(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_model), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_model));
  CAMLreturn(result);
}

CAMLprim value n_solver_get_proof(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_ast z3_result;
  z3_result = Z3_solver_get_proof(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_solver_get_unsat_core(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_ast_vector z3_result;
  z3_result = Z3_solver_get_unsat_core(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_solver_get_reason_unknown(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_solver_get_reason_unknown(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_solver_get_statistics(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_stats z3_result;
  z3_result = Z3_solver_get_statistics(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_stats), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_stats));
  CAMLreturn(result);
}

CAMLprim value n_solver_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_solver_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_stats_to_string(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_stats _a1 = * (Z3_stats*) Data_custom_val(a1);
  Z3_string z3_result;
  z3_result = Z3_stats_to_string(_a0, _a1);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_stats_inc_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_stats _a1 = * (Z3_stats*) Data_custom_val(a1);
  Z3_stats_inc_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_stats_dec_ref(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_stats _a1 = * (Z3_stats*) Data_custom_val(a1);
  Z3_stats_dec_ref(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_stats_size(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_stats _a1 = * (Z3_stats*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_stats_size(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_stats_get_key(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_stats _a1 = * (Z3_stats*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_string z3_result;
  z3_result = Z3_stats_get_key(_a0, _a1, _a2);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_stats_is_uint(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_stats _a1 = * (Z3_stats*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_stats_is_uint(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_stats_is_double(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_stats _a1 = * (Z3_stats*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_stats_is_double(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_stats_get_uint_value(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_stats _a1 = * (Z3_stats*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  unsigned z3_result;
  z3_result = Z3_stats_get_uint_value(_a0, _a1, _a2);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_stats_get_double_value(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_stats _a1 = * (Z3_stats*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  double z3_result;
  z3_result = Z3_stats_get_double_value(_a0, _a1, _a2);
  Store_double_val(result, z3_result);
  CAMLreturn(result);
}

CAMLprim value n_mk_injective_function(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_sort * _a3 = (Z3_sort*) malloc(sizeof(Z3_sort) * _a2);
  Z3_sort _a4 = * (Z3_sort*) Data_custom_val(a4);
  Z3_func_decl z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_sort*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_mk_injective_function(_a0, _a1, _a2, _a3, _a4);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_set_logic(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_set_logic(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_push(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_push(_a0);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_pop(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_pop(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_get_num_scopes(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned z3_result;
  z3_result = Z3_get_num_scopes(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_persist_ast(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_persist_ast(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_assert_cnstr(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_assert_cnstr(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_check_and_get_model(value a0) {
  CAMLparam1(a0);
  CAMLlocal3(result, res_val, _a1_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1;
  int z3_result;
  z3_result = Z3_check_and_get_model(_a0, &_a1);
  res_val = Val_int(z3_result);
  _a1_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_model), 0, 1); memcpy( Data_custom_val(_a1_val), &_a1, sizeof(Z3_model));
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a1_val);
  CAMLreturn(result);
}

CAMLprim value n_check(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  int z3_result;
  z3_result = Z3_check(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_check_assumptions(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal7(result, res_val, _a2_val, _a3_val, _a4_val, _a5_val, _a6_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_ast * _a2 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a1);
  Z3_model _a3;
  Z3_ast _a4;
  unsigned _a5;
  Z3_ast * _a6 = (Z3_ast*) malloc(sizeof(Z3_ast) * (_a1));
  int z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_ast*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_check_assumptions(_a0, _a1, _a2, &_a3, &_a4, &_a5, _a6);
  res_val = Val_int(z3_result);
  _a3_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_model), 0, 1); memcpy( Data_custom_val(_a3_val), &_a3, sizeof(Z3_model));
  _a4_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(_a4_val), &_a4, sizeof(Z3_ast));
  _a5_val = Val_int(_a5);
  _a6_val = caml_alloc(_a1, 0);
  for (_i = 0; _i < _a1; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(t), &_a6[_i], sizeof(Z3_ast)); Store_field(_a6, _i, t); }
  result = caml_alloc(5, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a3_val);
  Store_field(result, 2, _a4_val);
  Store_field(result, 3, _a5_val);
  Store_field(result, 4, _a6_val);
  free(_a2);
  free(_a6);
  CAMLreturn(result);
}

CAMLprim value n_get_implied_equalities(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal4(result, res_val, _a3_val, _a4_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_solver _a1 = * (Z3_solver*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  unsigned * _a4 = (unsigned*) malloc(sizeof(unsigned) * (_a2));
  unsigned z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_get_implied_equalities(_a0, _a1, _a2, _a3, _a4);
  res_val = Val_int(z3_result);
  _a4_val = caml_alloc(_a2, 0);
  for (_i = 0; _i < _a2; _i++) { value t; t = Val_int(_a4[_i]); Store_field(_a4, _i, t); }
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a4_val);
  free(_a3);
  free(_a4);
  CAMLreturn(result);
}

CAMLprim value n_del_model(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_del_model(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_soft_check_cancel(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_soft_check_cancel(_a0);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_get_search_failure(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned z3_result;
  z3_result = Z3_get_search_failure(_a0);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_mk_label(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_symbol _a1 = * (Z3_symbol*) Data_custom_val(a1);
  Z3_bool _a2 = (Z3_bool) Bool_val(a2);
  Z3_ast _a3 = * (Z3_ast*) Data_custom_val(a3);
  Z3_ast z3_result;
  z3_result = Z3_mk_label(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_relevant_labels(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_literals z3_result;
  z3_result = Z3_get_relevant_labels(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_literals), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_literals));
  CAMLreturn(result);
}

CAMLprim value n_get_relevant_literals(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_literals z3_result;
  z3_result = Z3_get_relevant_literals(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_literals), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_literals));
  CAMLreturn(result);
}

CAMLprim value n_get_guessed_literals(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_literals z3_result;
  z3_result = Z3_get_guessed_literals(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_literals), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_literals));
  CAMLreturn(result);
}

CAMLprim value n_del_literals(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_literals _a1 = * (Z3_literals*) Data_custom_val(a1);
  Z3_del_literals(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_get_num_literals(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_literals _a1 = * (Z3_literals*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_num_literals(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_label_symbol(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_literals _a1 = * (Z3_literals*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_symbol z3_result;
  z3_result = Z3_get_label_symbol(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_symbol), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_symbol));
  CAMLreturn(result);
}

CAMLprim value n_get_literal(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_literals _a1 = * (Z3_literals*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_get_literal(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_disable_literal(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_literals _a1 = * (Z3_literals*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_disable_literal(_a0, _a1, _a2);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_block_literals(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_literals _a1 = * (Z3_literals*) Data_custom_val(a1);
  Z3_block_literals(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_get_model_num_constants(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_model_num_constants(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_model_constant(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl z3_result;
  z3_result = Z3_get_model_constant(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_get_model_num_funcs(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned z3_result;
  z3_result = Z3_get_model_num_funcs(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_model_func_decl(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_func_decl z3_result;
  z3_result = Z3_get_model_func_decl(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_func_decl), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_func_decl));
  CAMLreturn(result);
}

CAMLprim value n_eval_func_decl(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a3_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_func_decl _a2 = * (Z3_func_decl*) Data_custom_val(a2);
  Z3_ast _a3;
  Z3_bool z3_result;
  z3_result = Z3_eval_func_decl(_a0, _a1, _a2, &_a3);
  res_val = Val_bool(z3_result);
  _a3_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(_a3_val), &_a3, sizeof(Z3_ast));
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a3_val);
  CAMLreturn(result);
}

CAMLprim value n_is_array_value(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a3_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  unsigned _a3;
  Z3_bool z3_result;
  z3_result = Z3_is_array_value(_a0, _a1, _a2, &_a3);
  res_val = Val_bool(z3_result);
  _a3_val = Val_int(_a3);
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a3_val);
  CAMLreturn(result);
}

CAMLprim value n_get_array_value(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal5(result, res_val, _a4_val, _a5_val, _a6_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  Z3_ast * _a4 = (Z3_ast*) malloc(sizeof(Z3_ast) * (_a3));
  Z3_ast * _a5 = (Z3_ast*) malloc(sizeof(Z3_ast) * (_a3));
  Z3_ast _a6;
  Z3_get_array_value(_a0, _a1, _a2, _a3, _a4, _a5, &_a6);
  _a4_val = caml_alloc(_a3, 0);
  for (_i = 0; _i < _a3; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(t), &_a4[_i], sizeof(Z3_ast)); Store_field(_a4, _i, t); }
  _a5_val = caml_alloc(_a3, 0);
  for (_i = 0; _i < _a3; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(t), &_a5[_i], sizeof(Z3_ast)); Store_field(_a5, _i, t); }
  _a6_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(_a6_val), &_a6, sizeof(Z3_ast));
  result = caml_alloc(3, 0);
  Store_field(result, 0, _a4_val);
  Store_field(result, 1, _a5_val);
  Store_field(result, 2, _a6_val);
  free(_a4);
  free(_a5);
  CAMLreturn(result);
}

CAMLprim value n_get_model_func_else(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_get_model_func_else(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_model_func_num_entries(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  unsigned z3_result;
  z3_result = Z3_get_model_func_num_entries(_a0, _a1, _a2);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_model_func_entry_num_args(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  unsigned z3_result;
  z3_result = Z3_get_model_func_entry_num_args(_a0, _a1, _a2, _a3);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_model_func_entry_arg(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  unsigned _a4 = (unsigned) Unsigned_int_val(a4);
  Z3_ast z3_result;
  z3_result = Z3_get_model_func_entry_arg(_a0, _a1, _a2, _a3, _a4);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_get_model_func_entry_value(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  Z3_ast z3_result;
  z3_result = Z3_get_model_func_entry_value(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_eval(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal3(result, res_val, _a3_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast _a3;
  Z3_bool z3_result;
  z3_result = Z3_eval(_a0, _a1, _a2, &_a3);
  res_val = Val_bool(z3_result);
  _a3_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(_a3_val), &_a3, sizeof(Z3_ast));
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a3_val);
  CAMLreturn(result);
}

CAMLprim value n_eval_decl(value a0, value a1, value a2, value a3, value a4) {
  CAMLparam5(a0, a1, a2, a3, a4);
  CAMLlocal4(result, res_val, _a4_val, _a5_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_model _a1 = * (Z3_model*) Data_custom_val(a1);
  Z3_func_decl _a2 = * (Z3_func_decl*) Data_custom_val(a2);
  unsigned _a3 = (unsigned) Unsigned_int_val(a3);
  Z3_ast * _a4 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a3);
  Z3_ast _a5;
  Z3_bool z3_result;
  for (_i = 0; _i < _a3; _i++) { _a4[_i] = * (Z3_ast*) Data_custom_val(Field(a4, _i)); }
  z3_result = Z3_eval_decl(_a0, _a1, _a2, _a3, _a4, &_a5);
  res_val = Val_bool(z3_result);
  _a5_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(_a5_val), &_a5, sizeof(Z3_ast));
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a5_val);
  free(_a4);
  CAMLreturn(result);
}

CAMLprim value n_context_to_string(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string z3_result;
  z3_result = Z3_context_to_string(_a0);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_statistics_to_string(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string z3_result;
  z3_result = Z3_statistics_to_string(_a0);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_get_context_assignment(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast z3_result;
  z3_result = Z3_get_context_assignment(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_mk_interpolation_context(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_config _a0 = * (Z3_config*) Data_custom_val(a0);
  Z3_context z3_result;
  z3_result = Z3_mk_interpolation_context(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_context), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_context));
  CAMLreturn(result);
}

CAMLprim value n_interpolation_profile(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string z3_result;
  z3_result = Z3_interpolation_profile(_a0);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_is_value(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_is_value(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_is_pos(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_is_pos(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_is_neg(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_is_neg(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_is_zero(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_is_zero(_a0, _a1);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_sign(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  int z3_result;
  z3_result = Z3_algebraic_sign(_a0, _a1);
  result = Val_int(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_add(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_algebraic_add(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_algebraic_sub(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_algebraic_sub(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_algebraic_mul(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_algebraic_mul(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_algebraic_div(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_algebraic_div(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_algebraic_root(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_algebraic_root(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_algebraic_power(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast z3_result;
  z3_result = Z3_algebraic_power(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast));
  CAMLreturn(result);
}

CAMLprim value n_algebraic_lt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_lt(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_gt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_gt(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_le(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_le(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_ge(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_ge(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_eq(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_eq(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_neq(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_algebraic_neq(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_roots(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  Z3_ast_vector z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_algebraic_roots(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_algebraic_eval(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal3(result, res_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_ast * _a3 = (Z3_ast*) malloc(sizeof(Z3_ast) * _a2);
  int z3_result;
  for (_i = 0; _i < _a2; _i++) { _a3[_i] = * (Z3_ast*) Data_custom_val(Field(a3, _i)); }
  z3_result = Z3_algebraic_eval(_a0, _a1, _a2, _a3);
  result = Val_int(z3_result);
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_polynomial_subresultants(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_ast _a1 = * (Z3_ast*) Data_custom_val(a1);
  Z3_ast _a2 = * (Z3_ast*) Data_custom_val(a2);
  Z3_ast _a3 = * (Z3_ast*) Data_custom_val(a3);
  Z3_ast_vector z3_result;
  z3_result = Z3_polynomial_subresultants(_a0, _a1, _a2, _a3);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_ast_vector), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_ast_vector));
  CAMLreturn(result);
}

CAMLprim value n_rcf_del(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_del(_a0, _a1);
  result = Val_unit;
  CAMLreturn(result);
}

CAMLprim value n_rcf_mk_rational(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_string _a1 = (Z3_string) String_val(a1);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_mk_rational(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_mk_small_int(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  int _a1 = (int) Int_val(a1);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_mk_small_int(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_mk_pi(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_mk_pi(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_mk_e(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_mk_e(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_mk_infinitesimal(value a0) {
  CAMLparam1(a0);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_mk_infinitesimal(_a0);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_mk_roots(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal4(result, res_val, _a2_val, _a3_val);
  unsigned _i;
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  unsigned _a1 = (unsigned) Unsigned_int_val(a1);
  Z3_rcf_num * _a2 = (Z3_rcf_num*) malloc(sizeof(Z3_rcf_num) * _a1);
  Z3_rcf_num * _a3 = (Z3_rcf_num*) malloc(sizeof(Z3_rcf_num) * (_a1));
  unsigned z3_result;
  for (_i = 0; _i < _a1; _i++) { _a2[_i] = * (Z3_rcf_num*) Data_custom_val(Field(a2, _i)); }
  z3_result = Z3_rcf_mk_roots(_a0, _a1, _a2, _a3);
  res_val = Val_int(z3_result);
  _a3_val = caml_alloc(_a1, 0);
  for (_i = 0; _i < _a1; _i++) { value t; t = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(t), &_a3[_i], sizeof(Z3_rcf_num)); Store_field(_a3, _i, t); }
  result = caml_alloc(2, 0);
  Store_field(result, 0, res_val);
  Store_field(result, 1, _a3_val);
  free(_a2);
  free(_a3);
  CAMLreturn(result);
}

CAMLprim value n_rcf_add(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_add(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_sub(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_sub(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_mul(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_mul(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_div(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_div(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_neg(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_neg(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_inv(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_inv(_a0, _a1);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_power(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_rcf_num z3_result;
  z3_result = Z3_rcf_power(_a0, _a1, _a2);
  result = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(result), &z3_result, sizeof(Z3_rcf_num));
  CAMLreturn(result);
}

CAMLprim value n_rcf_lt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_rcf_lt(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_rcf_gt(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_rcf_gt(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_rcf_le(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_rcf_le(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_rcf_ge(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_rcf_ge(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_rcf_eq(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_rcf_eq(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_rcf_neq(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2 = * (Z3_rcf_num*) Data_custom_val(a2);
  Z3_bool z3_result;
  z3_result = Z3_rcf_neq(_a0, _a1, _a2);
  result = Val_bool(z3_result);
  CAMLreturn(result);
}

CAMLprim value n_rcf_num_to_string(value a0, value a1, value a2, value a3) {
  CAMLparam4(a0, a1, a2, a3);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_bool _a2 = (Z3_bool) Bool_val(a2);
  Z3_bool _a3 = (Z3_bool) Bool_val(a3);
  Z3_string z3_result;
  z3_result = Z3_rcf_num_to_string(_a0, _a1, _a2, _a3);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_rcf_num_to_decimal_string(value a0, value a1, value a2) {
  CAMLparam3(a0, a1, a2);
  CAMLlocal1(result);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  unsigned _a2 = (unsigned) Unsigned_int_val(a2);
  Z3_string z3_result;
  z3_result = Z3_rcf_num_to_decimal_string(_a0, _a1, _a2);
  result = caml_copy_string((const char*) z3_result);
  CAMLreturn(result);
}

CAMLprim value n_rcf_get_numerator_denominator(value a0, value a1) {
  CAMLparam2(a0, a1);
  CAMLlocal4(result, res_val, _a2_val, _a3_val);
  Z3_context _a0 = * (Z3_context*) Data_custom_val(a0);
  Z3_rcf_num _a1 = * (Z3_rcf_num*) Data_custom_val(a1);
  Z3_rcf_num _a2;
  Z3_rcf_num _a3;
  Z3_rcf_get_numerator_denominator(_a0, _a1, &_a2, &_a3);
  _a2_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(_a2_val), &_a2, sizeof(Z3_rcf_num));
  _a3_val = caml_alloc_custom(&default_custom_ops, sizeof(Z3_rcf_num), 0, 1); memcpy( Data_custom_val(_a3_val), &_a3, sizeof(Z3_rcf_num));
  result = caml_alloc(2, 0);
  Store_field(result, 0, _a2_val);
  Store_field(result, 1, _a3_val);
  CAMLreturn(result);
}

#ifdef __cplusplus
}
#endif
