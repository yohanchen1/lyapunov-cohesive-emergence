// Lean compiler output
// Module: DGNG
// Imports: public import Init public import DGNG.Theorem1 public import DGNG.Theorem2 public import DGNG.Theorem3 public import DGNG.Theorem3_n public import DGNG.Theorem1_n public import DGNG.Theorem1_K3 public import DGNG.LaSalle public import DGNG.LaSalle_n public import DGNG.EnergyBound_n
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_Theorem1(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_Theorem2(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_Theorem3(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_Theorem3__n(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_Theorem1__n(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_Theorem1__K3(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_LaSalle(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_LaSalle__n(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_EnergyBound__n(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DGNG_DGNG(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_Theorem1(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_Theorem2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_Theorem3(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_Theorem3__n(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_Theorem1__n(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_Theorem1__K3(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_LaSalle(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_LaSalle__n(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_EnergyBound__n(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
