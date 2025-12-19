// Lean compiler output
// Module: TwinPrimeConjecture
// Imports: Init Mathlib
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
LEAN_EXPORT lean_object* l_Hamiltonian(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_NormedAddCommGroup_toENormedAddCommMonoid___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ToeplitzCoeffs_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Hamiltonian___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hamiltonian___redArg(lean_object*);
LEAN_EXPORT lean_object* l_t__min(lean_object*);
lean_object* l_AddMonoid_toAddZeroClass___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Hamiltonian___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_c__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_t__min___boxed(lean_object*);
LEAN_EXPORT lean_object* l_norm__t(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_norm__t___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Hamiltonian___redArg___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* l_Real_definition____x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_ToeplitzCoeffs_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_c__0(lean_object*);
LEAN_EXPORT lean_object* l_ToeplitzCoeffs_ctorIdx(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
}
LEAN_EXPORT lean_object* l_ToeplitzCoeffs_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_ToeplitzCoeffs_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_t__min(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Real_definition____x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
return x_2;
}
}
LEAN_EXPORT lean_object* l_t__min___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_t__min(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Hamiltonian___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Hamiltonian___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_NormedAddCommGroup_toENormedAddCommMonoid___redArg(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc_ref(x_3);
lean_dec_ref(x_2);
x_4 = l_AddMonoid_toAddZeroClass___redArg(x_3);
lean_dec_ref(x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec_ref(x_4);
x_6 = lean_alloc_closure((void*)(l_Hamiltonian___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Hamiltonian(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Hamiltonian___redArg(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Hamiltonian___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Hamiltonian___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Hamiltonian___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Hamiltonian(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_c__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Real_definition____x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
return x_2;
}
}
LEAN_EXPORT lean_object* l_c__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_c__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_norm__t(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Real_definition____x40_Mathlib_Data_Real_Basic_3335671075____hygCtx___hyg_2_;
return x_3;
}
}
LEAN_EXPORT lean_object* l_norm__t___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_norm__t(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Mathlib(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_TwinPrimeConjecture(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mathlib(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
