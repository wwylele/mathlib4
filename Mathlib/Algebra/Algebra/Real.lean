/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Quaternion
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!

-/

-- See Irreducible.degree_le_two


open Quaternion

variable (D : Type) [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]

abbrev lm (a : D) := Algebra.lmul ℝ D a

noncomputable
abbrev charpoly (a : D) := (lm D a).charpoly

lemma aeval_self (a : D) : (charpoly D a).aeval (lm D a) = 0 := by
  apply LinearMap.aeval_self_charpoly

lemma aeval_self' (a : D) : (charpoly D a).aeval a = 0 := by
  obtain h := aeval_self D a
  rw [Polynomial.aeval_algHom] at h
  simp  at h
  have h : ((LinearMap.mul ℝ D) ((Polynomial.aeval a) (charpoly D a))) 1
    = (0 : Module.End ℝ D) 1 := by exact congrFun (congrArg DFunLike.coe h) 1
  simpa using h

lemma is_integral (a : D) : IsIntegral ℝ a := by
  exact Algebra.IsIntegral.isIntegral a

lemma irreducible (a : D): Irreducible (minpoly ℝ a) := minpoly.irreducible (is_integral D a)



theorem exist_l (x : D) : ∃ (l : ℝ), x ^ 2 + l • x ∈ (⊥ : Subalgebra ℝ D) := by
  let n := (minpoly ℝ x).natDegree
  have hn : n = (minpoly ℝ x).natDegree := rfl
  have hdegree : n ≤ 2 := by
    apply Irreducible.natDegree_le_two
    apply minpoly.irreducible
    apply Algebra.IsIntegral.isIntegral
  have h0 : 0 < n := by
    apply minpoly.natDegree_pos
    apply Algebra.IsIntegral.isIntegral
  have hmonic : (minpoly ℝ x).Monic := by
    apply minpoly.monic
    apply Algebra.IsIntegral.isIntegral
  have heval := minpoly.aeval ℝ x
  match n with
  | 0 => simp at h0
  | 1 =>
    use 0
    rw [Algebra.mem_bot]
    simp only [zero_smul, add_zero, RingHom.mem_range]
    use (-(minpoly ℝ x).coeff 0) ^ 2
    rw [map_pow]
    suffices (algebraMap ℝ D) (-(minpoly ℝ x).coeff 0) = x by rw [this]
    refine minpoly.root ?_ ?_
    · apply Algebra.IsIntegral.isIntegral
    · refine Polynomial.IsRoot.def.mpr ?_
      rw [Polynomial.Monic.eq_X_add_C hmonic hn.symm]
      simp
  | 2 =>
    use (minpoly ℝ x).coeff 1
    rw [Algebra.mem_bot]
    simp only [Set.mem_range]
    use -(minpoly ℝ x).coeff 0
    rw [Polynomial.Monic.eq_X_sqr_add_C_mul_X_add_C hmonic hn.symm] at heval
    simp only [map_add, map_pow, Polynomial.aeval_X, map_mul, Polynomial.aeval_C] at heval
    simp only [map_neg]
    refine neg_eq_of_add_eq_zero_left ?_
    convert heval using 3
    exact Algebra.smul_def ((minpoly ℝ x).coeff 1) x
  | n + 3 => simp at hdegree

abbrev purelyImaginarySet : Set D := (fun v ↦ v ^ 2) ⁻¹' (algebraMap ℝ D '' (Set.Iic 0))

omit [FiniteDimensional ℝ D] in
theorem purelyImaginarySet_inter_bot : purelyImaginarySet D ∩ (⊥ : Subalgebra ℝ D) = {0} := by
  ext a
  constructor
  · intro ⟨h1, h2⟩
    simp at h1
    obtain ⟨x, hneg, hx⟩ := h1
    simp at h2
    obtain ⟨y, hy⟩ := h2
    rw [← hy, ← map_pow] at hx
    have hxy : x = y ^ 2 := FaithfulSMul.algebraMap_injective ℝ D hx
    have : x = 0 := by
      apply le_antisymm hneg
      rw [hxy]
      exact sq_nonneg y
    rw [this] at hxy
    have : y = 0 := by exact pow_eq_zero hxy.symm
    rw [← hy, this]
    simp
  · intro h
    obtain rfl : a = 0 := Set.eq_of_mem_singleton h
    simp

omit [FiniteDimensional ℝ D] in
theorem smul_mem_purelyImaginarySet (a : ℝ) {x : D} (hx : x ∈ purelyImaginarySet D) :
    a • x ∈ purelyImaginarySet D := by
  simp at hx
  obtain ⟨y, hy0, hy⟩ := hx
  simp
  use (a * a) * y
  constructor
  · apply mul_nonpos_of_nonneg_of_nonpos (by exact mul_self_nonneg a) hy0
  · rw [map_mul]
    rw [hy]
    rw [smul_pow, sq a]
    exact Eq.symm (Algebra.smul_def (a * a) _)

theorem add_mem_purelyImaginarySet {u v : D}
    (hu : u ∈ purelyImaginarySet D) (hv : v ∈ purelyImaginarySet D) :
    u + v ∈ purelyImaginarySet D := by
  have hu' := hu
  have hv' := hv
  simp at hu hv
  obtain ⟨u2, hu2neg, hu2⟩ := hu
  obtain ⟨v2, hv2neg, hv2⟩ := hv
  have hu2' : u ^ 2 ∈ (⊥ : Subalgebra ℝ D) := by
    rw [Algebra.mem_bot, Set.mem_range]
    exact ⟨u2, hu2⟩
  have hv2' : v ^ 2 ∈ (⊥ : Subalgebra ℝ D) := by
    rw [Algebra.mem_bot, Set.mem_range]
    exact ⟨v2, hv2⟩
  obtain ⟨l, hl⟩ := exist_l D (u + v)
  obtain ⟨m, hm⟩ := exist_l D (u - v)
  have : ((u + v) ^ 2 + l • (u + v)) + ((u - v) ^ 2 + m • (u - v)) ∈ (⊥ : Subalgebra ℝ D) :=
    Subalgebra.add_mem ⊥ hl hm
  have : (l + m) • u - (m - l) • v + 2 • (u ^ 2 + v ^ 2) ∈ (⊥ : Subalgebra ℝ D) := by
    convert this using 1
    simp_rw [add_smul, sub_smul, smul_add, smul_sub, sq, add_mul, mul_add, sub_mul, mul_sub]
    abel
  have : (l + m) • u - (m - l) • v ∈ (⊥ : Subalgebra ℝ D) := by
    suffices (l + m) • u - (m - l) • v + 2 • (u ^ 2 + v ^ 2) - 2 • (u ^ 2 + v ^ 2)
        ∈ (⊥ : Subalgebra ℝ D) by
      rw [add_sub_cancel_right] at this
      exact this
    apply Subalgebra.sub_mem _ this
    apply Subalgebra.nsmul_mem
    apply Subalgebra.add_mem _ hu2' hv2'
  rw [Algebra.mem_bot, Set.mem_range] at this
  obtain ⟨w, hw⟩ := this
  have : ((algebraMap ℝ D) w + (m - l) • v) ^ 2 = ((l + m) • u) ^ 2 := by
    rw [hw]
    rw [sub_add_cancel]
  have : 2 • w • (m - l) • v =
      ((l + m) • u) ^ 2 - ((algebraMap ℝ D) w) ^ 2 - ((m - l) • v) ^ 2 := by
    rw [← this]
    simp_rw [sq, add_mul, mul_add]
    suffices 2 • w • (m - l) • v =
        (algebraMap ℝ D) w * (m - l) • v + (m - l) • v * (algebraMap ℝ D) w by
      rw [this]
      abel
    rw [← Algebra.commutes]
    rw [← two_smul ℕ]
    rw [← Algebra.smul_def]
  have : 2 • w • (m - l) • v ∈ (⊥ : Subalgebra ℝ D) := by
    rw [this]
    apply Subalgebra.sub_mem
    · apply Subalgebra.sub_mem
      · rw [smul_pow]
        exact Subalgebra.smul_mem _ hu2' _
      · rw [← map_pow]
        exact Subalgebra.algebraMap_mem _ _
    · rw [smul_pow]
      exact Subalgebra.smul_mem _ hv2' _
  have : w • (m - l) • v ∈ (⊥ : Subalgebra ℝ D) := by
    suffices (2⁻¹ * 2 : ℝ) • w • (m - l) • v ∈ (⊥ : Subalgebra ℝ D) by
      rw [inv_mul_cancel_of_invertible, one_smul] at this
      exact this
    rw [← smul_smul]
    apply Subalgebra.smul_mem
    convert this using 1
    exact ofNat_smul_eq_nsmul _ _ _
  have : w • (m - l) • v = 0 := by
    apply Set.mem_singleton_iff.mp
    rw [← purelyImaginarySet_inter_bot]
    refine Set.mem_inter ?_ this
    apply smul_mem_purelyImaginarySet
    apply smul_mem_purelyImaginarySet
    exact hv'

  have huvqr (h : (u + v) ^ 2 ∈ (⊥ : Subalgebra ℝ D)) : u + v ∈ purelyImaginarySet D := by
    rw [Algebra.mem_bot, Set.mem_range] at h
    obtain ⟨x, hx⟩ := h
    obtain hx0 | hx0 := le_total x 0
    · simpa using ⟨x, hx0, hx⟩
    · let xpoly : Polynomial ℝ := Polynomial.X ^ 2 - Polynomial.C x
      have hdegree : xpoly.natDegree = 2 := by
        unfold xpoly
        compute_degree
        norm_num
      have h0 : xpoly ≠ 0 := by
        apply Polynomial.ne_zero_of_natDegree_gt
        show 0 < xpoly.natDegree
        rw [hdegree]
        norm_num
      have hxpoly : xpoly.aeval (u + v) = 0 := by
        unfold xpoly
        suffices (u + v) ^ 2 - (algebraMap ℝ D) x = 0 by simpa using this
        rw [← hx]
        simp
      have hdvd : minpoly ℝ (u + v) ∣ xpoly := by
        exact minpoly.dvd_iff.mpr hxpoly
      have hroot : xpoly.eval (Real.sqrt x) = 0 := by
        unfold xpoly
        simp [hx0]
      have hsplits : xpoly.Splits (RingHom.id _) := by
        unfold xpoly
        apply Polynomial.splits_of_natDegree_eq_two _ hdegree hroot
      have hsplits' : (minpoly ℝ (u + v)).Splits (RingHom.id _) := by
        apply Polynomial.splits_of_splits_of_dvd _ h0 hsplits hdvd
      have hdegree : (minpoly ℝ (u + v)).degree = 1 := by
        refine Polynomial.degree_eq_one_of_irreducible_of_splits ?_ hsplits'
        exact irreducible D (u + v)
      have hmem: (u + v) ∈ Set.range (algebraMap ℝ D) :=  minpoly.degree_eq_one_iff.mp hdegree
      rw [Set.mem_range] at hmem
      obtain ⟨x, hx⟩ := hmem
      have : ((algebraMap ℝ D) x - v) ^ 2 = u ^ 2 := by
        rw [hx]
        simp
      have hxuv : ((algebraMap ℝ D) x) ^ 2 - 2 • x • v + v ^ 2 = u ^ 2 := by
        rw [← this]
        simp_rw [sq, mul_sub, sub_mul]
        rw [← Algebra.commutes x v, Algebra.smul_def x]
        abel
      have : 2 • x • v = 0 := by
        apply Set.mem_singleton_iff.mp
        rw [← purelyImaginarySet_inter_bot]
        refine Set.mem_inter ?_ ?_
        · suffices (2 : ℝ) • x • v ∈ purelyImaginarySet D by
            convert this using 1
            exact Eq.symm (ofNat_smul_eq_nsmul ℝ 2 (x • v))
          apply smul_mem_purelyImaginarySet
          apply smul_mem_purelyImaginarySet
          exact hv'
        · suffices (algebraMap ℝ D) x ^ 2 + v ^ 2 - u ^ 2 ∈ (⊥ : Subalgebra ℝ D) by
            convert this using 1
            rw [← hxuv]
            abel
          apply Subalgebra.sub_mem
          · apply Subalgebra.add_mem
            · rw [← map_pow]
              exact Subalgebra.algebraMap_mem ⊥ (x ^ 2)
            · exact hv2'
          · exact hu2'
      have : x • v = 0 := (two_nsmul_eq_zero ℝ _).mp this
      obtain rfl | rfl := smul_eq_zero.mp this
      · have : u + v = 0 := by
          rw [← hx]
          simp
        rw [this]
        simp
      · simpa using hu'


  obtain rfl | hmlv := smul_eq_zero.mp this
  · obtain rfl | hlm := eq_or_ne l m
    · have : 0 = (l + l) • u := by simpa using hw
      rw [← two_smul ℕ, smul_assoc] at this
      have : l • u = 0 := (two_nsmul_eq_zero ℝ _).mp this.symm
      obtain rfl | rfl := smul_eq_zero.mp this
      · exact huvqr (by simpa using hl)
      · simpa using hv'
    · have : v = (m - l)⁻¹ • (l + m) • u := by
        rw [eq_inv_smul_iff₀ (sub_ne_zero.mpr hlm.symm)]
        refine (sub_eq_zero.mp (Eq.symm ?_)).symm
        simpa using hw
      rw [this, smul_smul]
      nth_rw 1 [← one_smul ℝ u]
      rw [← add_smul]
      apply smul_mem_purelyImaginarySet
      exact hu'
  · obtain hml | rfl := smul_eq_zero.mp hmlv
    · rw [hml] at hw
      have : (algebraMap ℝ D) w = (l + m) • u := by simpa using hw
      obtain hlm | hlm := eq_or_ne (l + m) 0
      · have : m = l := sub_eq_zero.mp hml
        rw [this] at hlm
        have : l = 0 := add_self_eq_zero.mp hlm
        rw [this] at hl
        exact huvqr (by simpa using hl)
      · have : (l + m)⁻¹ • (algebraMap ℝ D) w = u := by
          symm
          rw [eq_inv_smul_iff₀ hlm]
          exact this.symm
        have : u = 0 := by
          apply Set.mem_singleton_iff.mp
          rw [← purelyImaginarySet_inter_bot]
          refine Set.mem_inter hu' ?_
          rw [← this]
          apply Subalgebra.smul_mem
          exact Subalgebra.algebraMap_mem ⊥ w
        rw [this]
        simpa using hv'
    · simpa using hu'




abbrev PurelyImaginary : Submodule ℝ D where
  carrier := purelyImaginarySet D
  zero_mem' := by simp
  smul_mem' := smul_mem_purelyImaginarySet D
  add_mem' := add_mem_purelyImaginarySet D



theorem frobenius_theorem :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℂ) ∨ Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by


  sorry
