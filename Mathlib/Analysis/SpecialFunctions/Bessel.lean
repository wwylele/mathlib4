/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

module

public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric

import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# Bessel function

We introduce Bessel functions in this file. Bessel functions commonly take two complex parameters
`a` and `x`. They are analytic for `x ∈ Complex.slitPlane`. We also provide scoped notation in
the namespace `Complex` for these functions.

## `Complex.besselJ a x`: Bessel function of the first kind $J_a(x)$

The Bessel function $J_a(x)$ has the representation
$$
J_a(x) = (x / 2)^a \frac{₀F₁(-; a + 1; -(x/2)^2)} {Γ(a + 1)}
$$
where $₀F₁$ is the hypergeometric function.
Based on this, we define `Complex.besselJ a x` using `Complex.regularizedHGFun` for the fraction
part which removes the singularity for negative integer $a$.

This function is analytic for all `x` when `a` is an integer. (see `Complex.analyticAt_besselJ_int`)

$J_a(0) = 0$ for all complex $a \ne 0$. For $a = 0$, we have $J_0(0) = 1$.
(See `Complex.besselJ_zero`)

## TODO

* Bessel function of the second kind
* Differential equations
* Generating functions
* Bessel's integrals
-/

@[expose] public noncomputable section

open Nat FormalMultilinearSeries
open scoped Real

namespace Complex

local notation "F₀₁(" a ")" => regularizedHGFun 0 {(a : ℂ)}

/-- Bessel function of the first kind $J_a(x)$. -/
@[pp_nodot, dlmf 10.2.E2]
noncomputable def besselJ (a x : ℂ) := (x / 2) ^ a * F₀₁(a + 1) (- (x / 2) ^ 2)

/-- Modified Bessel function of the first kind $I_a(x)$. -/
@[pp_nodot, dlmf 10.25.E2]
noncomputable def besselI (a x : ℂ) := (x / 2) ^ a * F₀₁(a + 1) ((x / 2) ^ 2)

local notation "J" => besselJ
local notation "I'" => besselI

theorem besselJ_def : J = fun a x ↦ (x / 2) ^ a * F₀₁(a + 1) (- (x / 2) ^ 2) := rfl

theorem besselI_def : I' = fun a x ↦ (x / 2) ^ a * F₀₁(a + 1) ((x / 2) ^ 2) := rfl

theorem besselI_eq_mul_besselJ (a x : ℂ) :
    I' a x = (if x.arg ≤ π / 2 then 1 else exp (a * (2 * π * I))) * (-I) ^ a * J a (x * I) := by
  have : (x / 2).arg = x.arg := by
    by_cases hx : x = 0
    · simp [hx]
    trans (x / 2 * 2).arg
    · rw [arg_mul (by simp [hx]) (by simp) (by simp [arg_le_pi, neg_pi_lt_arg])]
      simp
    · simp
  rw [← this, besselJ, besselI, mul_div_right_comm, mul_pow, I_sq, mul_neg, neg_neg, mul_one]
  by_cases h : (x / 2).arg ≤ π / 2
  · calc
    _ = (-I) ^ a * (I ^ a) * (x / 2) ^ a * F₀₁(a + 1) ((x / 2) ^ 2) := by
      rw [← mul_cpow (by simp [Real.pi_pos, Real.pi_nonneg])]
      simp
    _ = _ := by
      rw [mul_cpow (by grind [arg_I, arg_le_pi, neg_pi_lt_arg]), ite_eq_left h]
      ring
  · calc
    _ = exp (a * (2 * π * I)) * exp (-2 * π * I * a) * ((-I) ^ a * (I ^ a)) *
        (x / 2) ^ a * F₀₁(a + 1) ((x / 2) ^ 2) := by
      rw [← exp_add, ← mul_cpow (by simp [Real.pi_pos, Real.pi_nonneg]), mul_comm a]
      simp
    _ = _ := by
      rw [mul_cpow_of_pi_lt (by grind [arg_I]), ite_eq_right h]
      ring

theorem besselI_int_eq_mul_besselJ (a : ℤ) (x : ℂ) :
    I' a x = (-I) ^ a * J a (x * I) := by
  simp [besselI_eq_mul_besselJ]

/-- `J a` is even or odd when $a$ is even or odd, respectively. -/
theorem besselJ_int_neg (a : ℤ) (x : ℂ) : J a (-x) = (-1) ^ a * J a x := by
  simp [besselJ_def, ← mul_assoc, neg_div, ← mul_zpow]

/-- `I a` is even or odd when $a$ is even or odd, respectively. -/
theorem besselI_int_neg (a : ℤ) (x : ℂ) : I' a (-x) = (-1) ^ a * I' a x := by
  rw [besselI_int_eq_mul_besselJ, besselI_int_eq_mul_besselJ, neg_mul, besselJ_int_neg,
    mul_left_comm]

theorem odd_besselJ {a : ℤ} (ha : Odd a) : Function.Odd (J a) := by
  intro x
  simp [besselJ_int_neg, ha.neg_zpow]

theorem odd_besselI {a : ℤ} (ha : Odd a) : Function.Odd (I' a) := by
  intro x
  simp [besselI_int_neg, ha.neg_zpow]

theorem even_besselJ {a : ℤ} (ha : Even a) : Function.Even (J a) := by
  intro x
  simp [besselJ_int_neg, ha.neg_zpow]

theorem even_besselI {a : ℤ} (ha : Even a) : Function.Even (I' a) := by
  intro x
  simp [besselI_int_neg, ha.neg_zpow]

/-- `J a` is analytic outside of the branch cut on the negative real axis. -/
@[fun_prop]
theorem analyticAt_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) : AnalyticAt ℂ (J a) x := by
  fun_prop (disch := simpa [slitPlane] using h) [besselJ]

/-- `I a` is analytic outside of the branch cut on the negative real axis. -/
@[fun_prop]
theorem analyticAt_besselI (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) : AnalyticAt ℂ (I' a) x := by
  fun_prop (disch := simpa [slitPlane] using h) [besselI]

@[fun_prop]
theorem analyticOnNhd_besselJ (a : ℂ) : AnalyticOnNhd ℂ (J a) slitPlane :=
  fun _ hz ↦ analyticAt_besselJ a hz

@[fun_prop]
theorem analyticOnNhd_besselI (a : ℂ) : AnalyticOnNhd ℂ (I' a) slitPlane :=
  fun _ hz ↦ analyticAt_besselI a hz

/-- For integer `a`, `J a` and `J (-a)` are related by a sign. -/
@[dlmf 10.4.E1]
theorem besselJ_neg_int (a : ℤ) (x : ℂ) : J (-a) x = (-1) ^ a * J a x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    simp only [Int.cast_neg, neg_neg, zpow_neg] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by simp)), one_mul]
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  push_cast
  have h : (x / 2) ^ (a : ℂ) = (x / 2) ^ (-a : ℂ) * ((x / 2) ^ 2) ^ a := by
    by_cases hx : x = 0
    · by_cases ha : a = 0 <;> simp [hx, ha]
    rw [← pow_mul, ← cpow_natCast, ← cpow_add _ _ (by simpa using hx)]
    grind
  unfold besselJ
  rw [regularizedHGFun_zero_singleton_neg_nat_add_one, neg_pow, h, zpow_natCast]
  ring

/-- For integer `a`, `I a` and `I (-a)` are equal. -/
@[dlmf 10.27.E1]
theorem besselI_neg_int (a : ℤ) (x : ℂ) : I' (-a) x = I' a x := by
  rw [← Int.cast_neg, besselI_int_eq_mul_besselJ, besselI_int_eq_mul_besselJ, Int.cast_neg,
    besselJ_neg_int, zpow_neg, ← inv_zpow, inv_neg, inv_I, neg_neg, ← mul_assoc, ← mul_zpow,
    mul_neg_one]

theorem besselJ_neg_comm (a : ℤ) (x : ℂ) : J (-a) x = J a (-x) := by
  rw [besselJ_neg_int, ← besselJ_int_neg]

/-- `J a` is analytic for integer `a`. -/
@[fun_prop]
theorem analyticAt_besselJ_int (a : ℤ) (x : ℂ) : AnalyticAt ℂ (J a) x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    have : AnalyticAt ℂ (fun x ↦ ((-1) ^ a)⁻¹ * J (↑(-a)) x) x := by fun_prop
    have ha' : (-1 : ℂ) ^ a ≠ 0 := by grind [zpow_ne_zero]
    simpa [besselJ_neg_int, ← mul_assoc, inv_mul_cancel₀ ha']
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  have : AnalyticAt ℂ (fun x ↦ (x / 2) ^ a * F₀₁(a + 1) (- (x / 2) ^ 2)) x := by fun_prop
  simpa [besselJ_def]

/-- `I a` is analytic for integer `a`. -/
@[fun_prop]
theorem analyticAt_besselI_int (a : ℤ) (x : ℂ) : AnalyticAt ℂ (I' a) x := by
  suffices AnalyticAt ℂ (I' a ·) x by simpa
  simp_rw [besselI_int_eq_mul_besselJ]
  fun_prop

@[fun_prop]
theorem analyticOnNhd_besselJ_int (a : ℤ) : AnalyticOnNhd ℂ (J a) .univ :=
  fun z _ ↦ analyticAt_besselJ_int a z

@[fun_prop]
theorem analyticOnNhd_besselI_int (a : ℤ) : AnalyticOnNhd ℂ (I' a) .univ :=
  fun z _ ↦ analyticAt_besselI_int a z

theorem besselJ_zero (a : ℂ) : J a 0 = if a = 0 then 1 else 0 := by
  split_ifs with h <;> simp [besselJ, h, regularizedHGFunCoeff]

theorem besselI_zero (a : ℂ) : I' a 0 = if a = 0 then 1 else 0 := by
  split_ifs with h <;> simp [besselI, h, regularizedHGFunCoeff]

@[dlmf 10.6.E1]
theorem two_mul_self_mul_besselJ (a : ℂ) (x : ℂ) :
    2 * a * J a x = x * J (a - 1) x + x * J (a + 1) x := by
  by_cases! h : x = 0
  · simp [h, besselJ_zero]
  have h : x / 2 ≠ 0 := by grind
  unfold besselJ
  calc
    _ = 2 * (x / 2) ^ a * (a * F₀₁(a + 1) (-(x / 2) ^ 2)) := by
      ring
    _ = 2 * (x / 2) ^ a * F₀₁(a) (-(x / 2) ^ 2) +
        2 * (x / 2) ^ a * (x / 2) ^ 2 * F₀₁(a + 2) (-(x / 2) ^ 2) := by
      grind [regularizedHGFun_zero_singleton_eq_mul_add_mul]
    _ = 2 * ((x / 2) ^ (a - 1) * (x / 2) ^ (1 : ℂ)) * F₀₁(a) (-(x / 2) ^ 2) +
        2 * (x / 2) ^ (a + 1) * (x / 2) * F₀₁(a + 2) (-(x / 2) ^ 2) := by
      grind [sub_add_cancel, cpow_add, cpow_one]
    _ = _ := by
      grind [cpow_one]

@[dlmf 10.29.E1]
theorem two_mul_self_mul_besselI (a : ℂ) (x : ℂ) :
    2 * a * I' a x = x * I' (a - 1) x - x * I' (a + 1) x := by
  have hI : -I ≠ 0 := neg_ne_zero.mpr I_ne_zero
  simp_rw [besselI_eq_mul_besselJ, cpow_add _ _ hI, cpow_sub _ _ hI, cpow_one, div_neg, div_I]
  by_cases h : x.arg ≤ π / 2
  · simp_rw [ite_eq_left h]
    linear_combination (-I) ^ a * two_mul_self_mul_besselJ a (x * I)
  · simp_rw [ite_eq_right h, sub_mul, add_mul, exp_sub, exp_add, one_mul, exp_two_pi_mul_I]
    linear_combination (-I) ^ a * exp (a * (2 * π * I)) * two_mul_self_mul_besselJ a (x * I)

end Complex
