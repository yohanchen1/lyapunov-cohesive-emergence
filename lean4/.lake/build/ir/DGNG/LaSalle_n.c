// Lean compiler output
// Module: DGNG.LaSalle_n
// Imports: public import Init public import Mathlib.Tactic public import Mathlib.Analysis.Calculus.Deriv.Basic public import Mathlib.Analysis.Calculus.Deriv.MeanValue public import Mathlib.Analysis.Calculus.Deriv.Pi public import Mathlib.Analysis.Calculus.Deriv.Prod public import Mathlib.Analysis.Convex.Basic public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp public import DGNG.GraphTheory public import DGNG.Theorem2 public import DGNG.EnergyBound_n public import DGNG.Theorem1_n
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
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupState___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupState___lam__0___boxed(lean_object*, lean_object*);
extern lean_object* lp_mathlib_Real_instAddCommGroup;
static lean_once_cell_t lp_DGNG_instAddCommGroupState___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_DGNG_instAddCommGroupState___closed__0;
lean_object* lp_mathlib_Pi_addCommGroup___redArg(lean_object*);
static lean_once_cell_t lp_DGNG_instAddCommGroupState___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_DGNG_instAddCommGroupState___closed__1;
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupState(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupState___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupWeight___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupWeight___lam__1___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_DGNG_instAddCommGroupWeight___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_DGNG_instAddCommGroupWeight___closed__0;
static lean_once_cell_t lp_DGNG_instAddCommGroupWeight___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_DGNG_instAddCommGroupWeight___closed__1;
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupWeight(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupWeight___boxed(lean_object*);
extern lean_object* lp_mathlib_Real_instDistribLattice;
extern lean_object* lp_mathlib_Real_instAddGroup;
lean_object* lp_mathlib_abs___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__1___lam__0(lean_object*, lean_object*);
extern lean_object* lp_mathlib_NNReal_instSemilatticeSup;
extern lean_object* lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
lean_object* l_List_finRange(lean_object*);
lean_object* lp_mathlib_Finset_sup___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__1(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_(lean_object*, lean_object*);
lean_object* lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__3___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__8___lam__0(lean_object*, lean_object*, lean_object*);
extern lean_object* lp_mathlib_instSemilatticeSupENNReal;
extern lean_object* lp_mathlib_ENNReal_instOrderBot;
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__8(lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_instInfSetUniformSpace___lam__0(lean_object*);
static lean_once_cell_t lp_DGNG_instNormedAddCommGroupState___aux__11___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_DGNG_instNormedAddCommGroupState___aux__11___closed__0;
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__11(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__11___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__17(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__17___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__1___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__3___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__8___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__8___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__8(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__11(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__11___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__17(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__17___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupState___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc_ref(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupState___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_DGNG_instAddCommGroupState___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_lp_DGNG_instAddCommGroupState___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lp_mathlib_Real_instAddCommGroup;
x_2 = lean_alloc_closure((void*)(lp_DGNG_instAddCommGroupState___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_DGNG_instAddCommGroupState___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&lp_DGNG_instAddCommGroupState___closed__0, &lp_DGNG_instAddCommGroupState___closed__0_once, _init_lp_DGNG_instAddCommGroupState___closed__0);
x_2 = lp_mathlib_Pi_addCommGroup___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupState(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&lp_DGNG_instAddCommGroupState___closed__1, &lp_DGNG_instAddCommGroupState___closed__1_once, _init_lp_DGNG_instAddCommGroupState___closed__1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupState___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_DGNG_instAddCommGroupState(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupWeight___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_mathlib_Pi_addCommGroup___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupWeight___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lp_DGNG_instAddCommGroupWeight___lam__1(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_lp_DGNG_instAddCommGroupWeight___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&lp_DGNG_instAddCommGroupState___closed__0, &lp_DGNG_instAddCommGroupState___closed__0_once, _init_lp_DGNG_instAddCommGroupState___closed__0);
x_2 = lean_alloc_closure((void*)(lp_DGNG_instAddCommGroupWeight___lam__1___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_lp_DGNG_instAddCommGroupWeight___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&lp_DGNG_instAddCommGroupWeight___closed__0, &lp_DGNG_instAddCommGroupWeight___closed__0_once, _init_lp_DGNG_instAddCommGroupWeight___closed__0);
x_2 = lp_mathlib_Pi_addCommGroup___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupWeight(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_obj_once(&lp_DGNG_instAddCommGroupWeight___closed__1, &lp_DGNG_instAddCommGroupWeight___closed__1_once, _init_lp_DGNG_instAddCommGroupWeight___closed__1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instAddCommGroupWeight___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_DGNG_instAddCommGroupWeight(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lp_mathlib_Real_instDistribLattice;
x_5 = lp_mathlib_Real_instAddGroup;
x_6 = lp_mathlib_abs___redArg(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_alloc_closure((void*)(lp_DGNG_instNormedAddCommGroupState___aux__1___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lp_mathlib_NNReal_instSemilatticeSup;
x_5 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_6 = l_List_finRange(x_1);
x_7 = lp_mathlib_Finset_sup___redArg(x_4, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_1(x_2, x_3);
x_6 = lp_mathlib_Real_instDistribLattice;
x_7 = lp_mathlib_Real_instAddGroup;
x_8 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(x_8, 0, x_5);
x_9 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_8);
x_10 = lp_mathlib_abs___redArg(x_6, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(lp_DGNG_instNormedAddCommGroupState___aux__3___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_mathlib_NNReal_instSemilatticeSup;
x_6 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_7 = l_List_finRange(x_1);
x_8 = lp_mathlib_Finset_sup___redArg(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__8___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lp_mathlib_Real_instDistribLattice;
x_5 = lp_mathlib_Real_instAddGroup;
lean_inc(x_3);
x_6 = lean_apply_1(x_1, x_3);
x_7 = lean_apply_1(x_2, x_3);
x_8 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_9, 0, x_6);
lean_closure_set(x_9, 1, x_8);
x_10 = lp_mathlib_abs___redArg(x_4, x_5, x_9);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(lp_DGNG_instNormedAddCommGroupState___aux__8___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_mathlib_instSemilatticeSupENNReal;
x_6 = lp_mathlib_ENNReal_instOrderBot;
x_7 = l_List_finRange(x_1);
x_8 = lp_mathlib_Finset_sup___redArg(x_5, x_6, x_7, x_4);
return x_8;
}
}
static lean_object* _init_lp_DGNG_instNormedAddCommGroupState___aux__11___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = lp_mathlib_instInfSetUniformSpace___lam__0(lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__11(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&lp_DGNG_instNormedAddCommGroupState___aux__11___closed__0, &lp_DGNG_instNormedAddCommGroupState___aux__11___closed__0_once, _init_lp_DGNG_instNormedAddCommGroupState___aux__11___closed__0);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__11___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_DGNG_instNormedAddCommGroupState___aux__11(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupState___aux__17___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_DGNG_instNormedAddCommGroupState___aux__17(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_apply_2(x_1, x_2, x_3);
x_5 = lp_mathlib_Real_instDistribLattice;
x_6 = lp_mathlib_Real_instAddGroup;
x_7 = lp_mathlib_abs___redArg(x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_alloc_closure((void*)(lp_DGNG_instNormedAddCommGroupWeight___aux__1___lam__0), 3, 2);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
x_5 = lp_mathlib_NNReal_instSemilatticeSup;
x_6 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_7 = l_List_finRange(x_2);
x_8 = lp_mathlib_Finset_sup___redArg(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_inc(x_1);
x_3 = lean_alloc_closure((void*)(lp_DGNG_instNormedAddCommGroupWeight___aux__1___lam__1), 3, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
x_4 = lp_mathlib_NNReal_instSemilatticeSup;
x_5 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_6 = l_List_finRange(x_1);
x_7 = lp_mathlib_Finset_sup___redArg(x_4, x_5, x_6, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_apply_2(x_1, x_2, x_4);
x_6 = lean_apply_2(x_3, x_2, x_4);
x_7 = lp_mathlib_Real_instDistribLattice;
x_8 = lp_mathlib_Real_instAddGroup;
x_9 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(x_9, 0, x_6);
x_10 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_10, 0, x_5);
lean_closure_set(x_10, 1, x_9);
x_11 = lp_mathlib_abs___redArg(x_7, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__3___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_alloc_closure((void*)(lp_DGNG_instNormedAddCommGroupWeight___aux__3___lam__0), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = lp_mathlib_NNReal_instSemilatticeSup;
x_7 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_8 = l_List_finRange(x_3);
x_9 = lp_mathlib_Finset_sup___redArg(x_6, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(lp_DGNG_instNormedAddCommGroupWeight___aux__3___lam__1), 4, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_1);
x_5 = lp_mathlib_NNReal_instSemilatticeSup;
x_6 = lp_mathlib_Real_definition_00___x40_Mathlib_Data_Real_Basic_1850581184____hygCtx___hyg_8_;
x_7 = l_List_finRange(x_1);
x_8 = lp_mathlib_Finset_sup___redArg(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__8___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lp_mathlib_Real_instDistribLattice;
x_6 = lp_mathlib_Real_instAddGroup;
lean_inc(x_4);
lean_inc(x_2);
x_7 = lean_apply_2(x_1, x_2, x_4);
x_8 = lean_apply_2(x_3, x_2, x_4);
x_9 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_2451848184____hygCtx___hyg_8_), 2, 1);
lean_closure_set(x_9, 0, x_8);
x_10 = lean_alloc_closure((void*)(lp_mathlib_Real_definition___lam__0_00___x40_Mathlib_Data_Real_Basic_1138242547____hygCtx___hyg_8_), 3, 2);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_9);
x_11 = lp_mathlib_abs___redArg(x_5, x_6, x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__8___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_alloc_closure((void*)(lp_DGNG_instNormedAddCommGroupWeight___aux__8___lam__0), 4, 3);
lean_closure_set(x_5, 0, x_1);
lean_closure_set(x_5, 1, x_4);
lean_closure_set(x_5, 2, x_2);
x_6 = lp_mathlib_instSemilatticeSupENNReal;
x_7 = lp_mathlib_ENNReal_instOrderBot;
x_8 = l_List_finRange(x_3);
x_9 = lp_mathlib_Finset_sup___redArg(x_6, x_7, x_8, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(lp_DGNG_instNormedAddCommGroupWeight___aux__8___lam__1), 4, 3);
lean_closure_set(x_4, 0, x_2);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_1);
x_5 = lp_mathlib_instSemilatticeSupENNReal;
x_6 = lp_mathlib_ENNReal_instOrderBot;
x_7 = l_List_finRange(x_1);
x_8 = lp_mathlib_Finset_sup___redArg(x_5, x_6, x_7, x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__11(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&lp_DGNG_instNormedAddCommGroupState___aux__11___closed__0, &lp_DGNG_instNormedAddCommGroupState___aux__11___closed__0_once, _init_lp_DGNG_instNormedAddCommGroupState___aux__11___closed__0);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__11___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_DGNG_instNormedAddCommGroupWeight___aux__11(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__17(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_DGNG_instNormedAddCommGroupWeight___aux__17___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_DGNG_instNormedAddCommGroupWeight___aux__17(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_MeanValue(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Pi(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Prod(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_Convex_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Trigonometric_DerivHyp(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_GraphTheory(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_Theorem2(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_EnergyBound__n(uint8_t builtin);
lean_object* initialize_DGNG_DGNG_Theorem1__n(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_DGNG_DGNG_LaSalle__n(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_MeanValue(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Pi(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Calculus_Deriv_Prod(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_Convex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Analysis_SpecialFunctions_Trigonometric_DerivHyp(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_GraphTheory(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_Theorem2(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_EnergyBound__n(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_DGNG_DGNG_Theorem1__n(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
