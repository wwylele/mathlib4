/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.Quaternion
import Mathlib.Data.Complex.Module
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!

-/

def AlgEquiv.ofLinearEquiv_basis {R : Type*} {A₁ : Type*} {A₂ : Type*}
    [CommSemiring R] [Semiring A₁] [Semiring A₂] [Algebra R A₁] [Algebra R A₂]
    (l : A₁ ≃ₗ[R] A₂) (map_one : l 1 = 1) {ι : Type*} (b : Basis ι R A₁)
    (h : ∀ (i j : ι), l (b i * b j) = l (b i) * l (b j))
    : A₁ ≃ₐ[R] A₂ := by
  refine AlgEquiv.ofLinearEquiv l map_one ?_
  intro x y
  rw [← Basis.linearCombination_repr b x]
  rw [← Basis.linearCombination_repr b y]
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, map_sum, Finset.sum_mul_sum,
    smul_mul_smul, map_smul, h]


namespace QuaternionAlgebra
variable {R : Type*} [CommRing R]
variable (c₁ c₂ c₃ : R)

theorem basisOneIJK_zero : (basisOneIJK c₁ c₂ c₃) 0 = 1 := by
  unfold basisOneIJK
  show ⇑(Basis.ofEquivFun (QuaternionAlgebra.linearEquivTuple _ _ _)) _ = _
  rw [Basis.coe_ofEquivFun]
  rfl

theorem basisOneIJK_one : (basisOneIJK c₁ c₂ c₃) 1 = ⟨0, 1, 0, 0⟩ := by
  unfold basisOneIJK
  show ⇑(Basis.ofEquivFun (QuaternionAlgebra.linearEquivTuple _ _ _)) _ = _
  rw [Basis.coe_ofEquivFun]
  rfl

theorem basisOneIJK_two : (basisOneIJK c₁ c₂ c₃) 2 = ⟨0, 0, 1, 0⟩ := by
  unfold basisOneIJK
  show ⇑(Basis.ofEquivFun (QuaternionAlgebra.linearEquivTuple _ _ _)) _ = _
  rw [Basis.coe_ofEquivFun]
  rfl

theorem basisOneIJK_three : (basisOneIJK c₁ c₂ c₃) 3 = ⟨0, 0, 0, 1⟩ := by
  unfold basisOneIJK
  show ⇑(Basis.ofEquivFun (QuaternionAlgebra.linearEquivTuple _ _ _)) _ = _
  rw [Basis.coe_ofEquivFun]
  rfl

--theorem basisOneIJK_zero_mul


end QuaternionAlgebra

namespace Quaternion
variable (R : Type*) [CommRing R]



noncomputable
abbrev basisOneIJK : Basis (Fin 4) R ℍ[R] := QuaternionAlgebra.basisOneIJK (-1) 0 (-1)

theorem basisOneIJK_zero : (basisOneIJK R) 0 = 1 := QuaternionAlgebra.basisOneIJK_zero _ _ _

theorem basisOneIJK_one : (basisOneIJK R) 1 = ⟨0, 1, 0, 0⟩ :=
  QuaternionAlgebra.basisOneIJK_one _ _ _

theorem basisOneIJK_two : (basisOneIJK R) 2 = ⟨0, 0, 1, 0⟩ :=
  QuaternionAlgebra.basisOneIJK_two _ _ _

theorem basisOneIJK_three : (basisOneIJK R) 3 = ⟨0, 0, 0, 1⟩ :=
  QuaternionAlgebra.basisOneIJK_three _ _ _

theorem basisOneIJK00 : basisOneIJK R 0 * basisOneIJK R 0 = basisOneIJK R 0 := by
  simp [basisOneIJK_zero]
theorem basisOneIJK01 : basisOneIJK R 0 * basisOneIJK R 1 = basisOneIJK R 1 := by
  simp [basisOneIJK_zero]
theorem basisOneIJK02 : basisOneIJK R 0 * basisOneIJK R 2 = basisOneIJK R 2 := by
  simp [basisOneIJK_zero]
theorem basisOneIJK03 : basisOneIJK R 0 * basisOneIJK R 3 = basisOneIJK R 3 := by
  simp [basisOneIJK_zero]
theorem basisOneIJK10 : basisOneIJK R 1 * basisOneIJK R 0 = basisOneIJK R 1 := by
  simp [basisOneIJK_zero]
theorem basisOneIJK11 : basisOneIJK R 1 * basisOneIJK R 1 = -basisOneIJK R 0 := by
  simp [basisOneIJK_zero, basisOneIJK_one]
  ext <;> simp
theorem basisOneIJK12 : basisOneIJK R 1 * basisOneIJK R 2 = basisOneIJK R 3 := by
  simp [basisOneIJK_one, basisOneIJK_two, basisOneIJK_three]
  ext <;> simp
theorem basisOneIJK13 : basisOneIJK R 1 * basisOneIJK R 3 = -basisOneIJK R 2 := by
  simp [basisOneIJK_one, basisOneIJK_two, basisOneIJK_three]
  ext <;> simp
theorem basisOneIJK20 : basisOneIJK R 2 * basisOneIJK R 0 = basisOneIJK R 2 := by
  simp [basisOneIJK_zero]
theorem basisOneIJK21 : basisOneIJK R 2 * basisOneIJK R 1 = -basisOneIJK R 3 := by
  simp [basisOneIJK_one, basisOneIJK_two, basisOneIJK_three]
  ext <;> simp
theorem basisOneIJK22 : basisOneIJK R 2 * basisOneIJK R 2 = -basisOneIJK R 0 := by
  simp [basisOneIJK_zero, basisOneIJK_two]
  ext <;> simp
theorem basisOneIJK23 : basisOneIJK R 2 * basisOneIJK R 3 = basisOneIJK R 1 := by
  simp [basisOneIJK_one, basisOneIJK_two, basisOneIJK_three]
  ext <;> simp
theorem basisOneIJK30 : basisOneIJK R 3 * basisOneIJK R 0 = basisOneIJK R 3 := by
  simp [basisOneIJK_zero]
theorem basisOneIJK31 : basisOneIJK R 3 * basisOneIJK R 1 = basisOneIJK R 2 := by
  simp [basisOneIJK_one, basisOneIJK_two, basisOneIJK_three]
  ext <;> simp
theorem basisOneIJK32 : basisOneIJK R 3 * basisOneIJK R 2 = -basisOneIJK R 1 := by
  simp [basisOneIJK_one, basisOneIJK_two, basisOneIJK_three]
  ext <;> simp
theorem basisOneIJK33 : basisOneIJK R 3 * basisOneIJK R 3 = -basisOneIJK R 0 := by
  simp [basisOneIJK_zero, basisOneIJK_three]
  ext <;> simp

end Quaternion

open Quaternion




variable (D : Type) [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D]


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
        apply minpoly.irreducible
        apply Algebra.IsIntegral.isIntegral
      have hmem: (u + v) ∈ Set.range (algebraMap ℝ D) := minpoly.degree_eq_one_iff.mp hdegree
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

theorem mem_purelyImaginary_iff {x : D} :
    x ∈ PurelyImaginary D ↔ ∃ y ≤ 0, algebraMap ℝ D y = x ^ 2 := by
  simp

theorem compl : IsCompl ((⊥ : Subalgebra ℝ D).toSubmodule) (PurelyImaginary D) := by
  refine isCompl_iff.mpr ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x h1 h2
    apply Set.mem_singleton_iff.mp
    rw [← purelyImaginarySet_inter_bot]
    exact Set.mem_inter h2 h1
  · rw [codisjoint_iff]
    rw [Submodule.sup_eq_top_iff]
    intro x
    obtain ⟨l, hl⟩ := exist_l D x
    rw [Algebra.mem_bot, Set.mem_range] at hl
    obtain ⟨m, hm⟩ := hl
    have hlx : l • x = 2 • ((algebraMap ℝ D (l / 2)) * x) := by
      suffices l • x = (2 : ℝ) • ((algebraMap ℝ D (l / 2)) * x) by
        rw [this]
        exact ofNat_smul_eq_nsmul ℝ 2 _
      rw [← Algebra.smul_def, smul_smul]
      rw [mul_div_cancel₀ _ (by norm_num)]
    have hlx2 : (x + algebraMap ℝ D (l / 2)) ^ 2 =
        x ^ 2 + l • x + (algebraMap ℝ D (l / 2)) ^ 2 := by
      rw [hlx]
      simp_rw [sq, mul_add, add_mul]
      rw [← Algebra.commutes]
      abel

    obtain hlm | hlm := le_total (m + (l / 2) ^ 2) 0
    · refine ⟨-algebraMap ℝ D (l / 2), ?_, x + algebraMap ℝ D (l / 2), ?_, by simp⟩
      · show -(algebraMap ℝ D) (l / 2) ∈ (⊥ : Subalgebra ℝ D)
        apply Subalgebra.neg_mem
        apply Subalgebra.algebraMap_mem
      · suffices ∃ y ≤ 0, (algebraMap ℝ D) y = (x + (algebraMap ℝ D) (l / 2)) ^ 2 by
          simpa using this
        refine ⟨m + (l / 2) ^ 2, hlm, ?_⟩
        rw [hlx2, map_add, hm, map_pow]
    · have : (x + algebraMap ℝ D (l / 2)) ^ 2 ∈ (⊥ : Subalgebra ℝ D) := by
        rw [hlx2]
        rw [← hm, ← map_pow, ← map_add]
        exact Subalgebra.algebraMap_mem ⊥ (m + (l / 2) ^ 2)
      rw [Algebra.mem_bot, Set.mem_range] at this
      obtain ⟨y, hy⟩ := this
      have hy0 : 0 ≤ y := by
        convert hlm
        apply FaithfulSMul.algebraMap_injective ℝ D
        rw [map_add, hm, hy, hlx2, map_pow]

      let xpoly : Polynomial ℝ := (Polynomial.X + Polynomial.C (l / 2)) ^ 2 - Polynomial.C y
      have hdegree : xpoly.natDegree = 2 := by
        unfold xpoly
        compute_degree
        norm_num
      have h0 : xpoly ≠ 0 := by
        apply Polynomial.ne_zero_of_natDegree_gt
        show 0 < xpoly.natDegree
        rw [hdegree]
        norm_num
      have hxpoly : xpoly.aeval x = 0 := by
        unfold xpoly
        simp [hy]
      have hdvd : minpoly ℝ x ∣ xpoly := by
        exact minpoly.dvd_iff.mpr hxpoly
      have hroot : xpoly.eval (Real.sqrt y - l / 2) = 0 := by
        unfold xpoly
        simp [hy0]
      have hsplits : xpoly.Splits (RingHom.id _) := by
        unfold xpoly
        apply Polynomial.splits_of_natDegree_eq_two _ hdegree hroot
      have hsplits' : (minpoly ℝ x).Splits (RingHom.id _) := by
        apply Polynomial.splits_of_splits_of_dvd _ h0 hsplits hdvd

      have hdegree : (minpoly ℝ x).natDegree = 1 := by
        suffices (minpoly ℝ x).degree = 1 by
          exact Polynomial.natDegree_eq_of_degree_eq_some this
        refine Polynomial.degree_eq_one_of_irreducible_of_splits ?_ hsplits'
        apply minpoly.irreducible
        apply Algebra.IsIntegral.isIntegral
      refine ⟨-algebraMap ℝ D ((minpoly ℝ x).coeff 0), ?_, 0, by simp, ?_⟩
      · apply Subalgebra.neg_mem
        apply Subalgebra.algebraMap_mem
      · obtain heval := minpoly.aeval ℝ x
        rw [Polynomial.Monic.eq_X_add_C (minpoly.monic (Algebra.IsIntegral.isIntegral _)) hdegree]
          at heval
        rw [add_zero, ← sub_eq_zero, sub_neg_eq_add]
        simpa using heval

theorem mul_mul_mem {x y : D} (hx : x ∈ PurelyImaginary D) (hy : y ∈ PurelyImaginary D):
    x * y * x ∈ PurelyImaginary D := by
  rw [mem_purelyImaginary_iff] at hx hy ⊢
  obtain ⟨x', hx', hxx⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hy
  refine ⟨x' * y' * x', ?_, ?_⟩
  · apply mul_nonpos_of_nonneg_of_nonpos
    · apply mul_nonneg_of_nonpos_of_nonpos hx' hy'
    exact hx'
  · symm
    calc
      (x * y * x) ^ 2 = x * y * (x ^ 2) * y * x := by
        simp_rw [sq]
        group
      _ = x * y * ((algebraMap ℝ D) x') * y * x := by
        rw [hxx]
      _ = ((algebraMap ℝ D) x') * x * y ^ 2 * x := by
        rw [sq, ← Algebra.commutes]
        group
      _ = ((algebraMap ℝ D) x') * x * ((algebraMap ℝ D) y') * x := by
        rw [hyy]
      _ = ((algebraMap ℝ D) x') * ((algebraMap ℝ D) y') * x ^ 2 := by
        simp_rw [sq, ← Algebra.commutes y']
        group
      _ = ((algebraMap ℝ D) x') * ((algebraMap ℝ D) y') * ((algebraMap ℝ D) x') := by
        rw [hxx]
      _ = (algebraMap ℝ D) (x' * y' * x') := by
        simp

abbrev circle {D : Type*} [Ring D] (x y : D) := x * y + y * x

theorem circle_right_distrib {D : Type*} [Ring D] (x y z : D) :
    circle (x + y) z = circle x z + circle y z := by
  unfold circle
  simp_rw [mul_add, add_mul]
  abel

theorem circle_left_distrib {D : Type*} [Ring D] (x y z : D) :
    circle x (y + z) = circle x y + circle x z := by
  unfold circle
  simp_rw [mul_add, add_mul]
  abel

omit [FiniteDimensional ℝ D] in
variable {D} in
theorem circle_left_smul (a : ℝ) (x y : D) :
    circle (a • x) y = a • circle x y := by
  unfold circle
  rw [smul_add, smul_mul_assoc, mul_smul_comm a y x]

theorem circle_real {x y : D} (hx : x ∈ PurelyImaginary D) (hy : y ∈ PurelyImaginary D) :
    ∃ z, algebraMap ℝ D z = circle x y := by
  unfold circle
  have hxy : x + y ∈ PurelyImaginary D := Submodule.add_mem _ hx hy
  rw [mem_purelyImaginary_iff] at hx hy hxy
  obtain ⟨x', hx', hxx⟩ := hx
  obtain ⟨y', hy', hyy⟩ := hy
  obtain ⟨xy', hxy', hxyxy⟩ := hxy
  use xy' - x' - y'
  simp only [map_sub, hxyxy, sq, mul_add, add_mul, hxx, hyy]
  abel

set_option maxHeartbeats 800000

theorem frobenius_theorem (D : Type) [DivisionRing D] [Algebra ℝ D] [FiniteDimensional ℝ D] :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℂ) ∨ Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by
  obtain hcompl := compl D
  by_cases hbot : PurelyImaginary D = ⊥
  · rw [hbot] at hcompl
    obtain htop := hcompl.sup_eq_top
    simp only [bot_le, sup_of_le_left, Algebra.toSubmodule_eq_top] at htop
    obtain hequiv : D ≃ₐ[ℝ] ℝ :=
      ((Subalgebra.equivOfEq _ _ htop).trans Subalgebra.topEquiv).symm.trans (Algebra.botEquiv ℝ D)
    left
    exact Nonempty.intro hequiv
  · obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp hbot
    obtain ⟨u', hu', huu⟩ := (mem_purelyImaginary_iff D).mp hu
    let i := (Real.sqrt (-u'))⁻¹ • u
    have hi : i ^ 2 = algebraMap ℝ D (-1) := by
      rw [smul_pow, ← huu, Algebra.smul_def, ← map_mul, inv_pow, Real.sq_sqrt (by simpa using hu')]
      rw [inv_neg, neg_mul, inv_mul_cancel₀ ?_]
      contrapose! hu0
      rw [hu0] at huu
      exact pow_eq_zero (n := 2) (by simpa using huu.symm)

    by_cases hspan : PurelyImaginary D = ℝ ∙ i
    · rw [hspan] at hcompl
      let basisSet := ![1, i]
      have honespan : ((⊥ : Subalgebra ℝ D).toSubmodule) = Submodule.span ℝ {1} := by
        ext x
        rw [Submodule.mem_span_singleton]
        rw [Subalgebra.mem_toSubmodule, Algebra.mem_bot, Set.mem_range]
        constructor
        · intro ⟨a, ha⟩
          use a
          rw [← ha]
          rw [Algebra.smul_def, mul_one]
        · intro ⟨a, ha⟩
          use a
          rw [← ha]
          rw [Algebra.smul_def, mul_one]
      have hindep : LinearIndependent ℝ basisSet := by
        rw [LinearIndependent.pair_iff' (by simp)]
        intro a
        by_contra!
        have hi0 : i ∈ ((⊥ : Subalgebra ℝ D).toSubmodule) := by
          rw [← this]
          apply Submodule.smul_mem
          exact Subalgebra.one_mem _
        have hi1 : i ∈ (Submodule.span ℝ {i}) := by simp
        have hizero := Submodule.disjoint_def.mp hcompl.disjoint i hi0 hi1
        rw [hizero] at hi
        simp at hi

      have hspan : ⊤ ≤ Submodule.span ℝ (Set.range basisSet) := by
        rw [Submodule.span_range_eq_iSup]
        rw [top_le_iff]
        convert hcompl.sup_eq_top
        unfold basisSet
        rw [← iSup_univ, honespan]
        convert iSup_pair (a := 0) (b := 1) (f := fun n ↦ Submodule.span ℝ {![1, i] n})
        ext x
        fin_cases x <;> simp

      let basis := Basis.mk hindep hspan

      right
      left
      let linEquiv := Basis.equiv basis Complex.basisOneI (Equiv.refl _)
      refine Nonempty.intro (AlgEquiv.ofLinearEquiv_basis linEquiv ?_ basis ?_)
      · rw [show (1 : D) = basis 0 by unfold basis basisSet; simp]
        rw [show (1 : ℂ) = Complex.basisOneI 0 by simp]
        unfold linEquiv
        simp
      · have basis00 : basis 0 * basis 0 = basis 0 := by
          simp [basis, basisSet]
        have basis01 : basis 0 * basis 1 = basis 1 := by
          simp [basis, basisSet]
        have basis10 : basis 1 * basis 0 = basis 1 := by
          simp [basis, basisSet]
        have basis11 : basis 1 * basis 1 = -basis 0 := by
          suffices i * i = -1 by simpa [basis, basisSet] using this
          rw [← sq, hi, map_neg]
          simp

        intro i j
        fin_cases i <;> fin_cases j <;> unfold linEquiv <;>
          simp [basis00, basis01, basis10, basis11]
    · have himem : i ∈ PurelyImaginary D := Submodule.smul_mem _ _ hu
      have hle : Submodule.span ℝ {i} ≤ PurelyImaginary D :=
        (Submodule.span_singleton_le_iff_mem i (PurelyImaginary D)).mpr himem
      have hlt : Submodule.span ℝ {i} < PurelyImaginary D := by
        exact lt_of_le_of_ne hle (hspan ·.symm)
      have hw : ∃ w ∈ PurelyImaginary D, w ∉ Submodule.span ℝ {i} := by
        exact Set.exists_of_ssubset hlt
      obtain ⟨w, hwmem, hwnmem⟩ := hw
      let J := i * w * i + w
      let K := i * w - w * i
      have hJmem : J ∈ PurelyImaginary D := by
        refine Submodule.add_mem _ ?_ hwmem
        exact mul_mul_mem D himem hwmem
      obtain ⟨w', hw'0, hw'⟩ := (mem_purelyImaginary_iff D).mp hwmem

      have hiw := calc
        i * w * i * (i * w * i) = i * w * i ^ 2 * w * i := by
          rw [sq]
          group
        _ = i * w * (algebraMap ℝ D (-1)) * w * i := by rw [hi]
        _ = (algebraMap ℝ D (-1)) * i * w ^ 2 * i := by
          simp_rw [sq, ← Algebra.commutes]
          group
        _ = (algebraMap ℝ D (-1)) * i * (algebraMap ℝ D w') * i := by rw [hw']
        _ = (algebraMap ℝ D w') * (algebraMap ℝ D (-1)) * i ^ 2 := by
          simp_rw [sq, ← Algebra.commutes w']
          group
        _ = (algebraMap ℝ D w') * (algebraMap ℝ D (-1)) * (algebraMap ℝ D (-1)) := by rw [hi]
        _ = (algebraMap ℝ D w') * (algebraMap ℝ D 1) := by
          rw [mul_assoc, ← map_mul, neg_one_mul, neg_neg]
        _ = (algebraMap ℝ D w') := by simp
        _ = w ^ 2 := hw'
      have hiw' := calc
        w * i * (i * w) = w * i ^ 2 * w := by
          rw [sq]
          group
        _ = w * (algebraMap ℝ D (-1)) * w := by rw [hi]
        _ = (algebraMap ℝ D (-1)) * w ^ 2 := by
          simp_rw [sq, ← Algebra.commutes]
          group
        _ = - w ^ 2 := by simp
      have hiw'' := calc
        i * w * (w * i) = i * w ^ 2 * i := by
          rw [sq]
          group
        _ = i * (algebraMap ℝ D w') * i := by rw [hw']
        _ = (algebraMap ℝ D w') * i ^ 2 := by
          simp_rw [sq, ← Algebra.commutes]
          group
        _ = (algebraMap ℝ D w') * (algebraMap ℝ D (-1)) := by rw [hi]
        _ = w ^ 2 * (algebraMap ℝ D (-1)) := by rw [hw']
        _ = - w ^ 2 := by simp

      have hJK : J ^ 2 = K ^ 2 := by
        simp_rw [J, K, sq, mul_add, add_mul, mul_sub, sub_mul]
        rw [hiw, hiw', hiw'']
        simp_rw [sq]
        group
        abel
      have hKmem : K ∈ PurelyImaginary D := by
        rw [mem_purelyImaginary_iff] at ⊢ hJmem
        rw [← hJK]
        exact hJmem

      obtain ⟨s, hs⟩ := circle_real D hwmem himem
      have hJeq : J = (2 : ℝ) • w + s • i := by
        symm
        calc
          (2 : ℝ) • w + s • i = (2 : ℝ) • w + (w * i + i * w) * i := by rw [Algebra.smul_def s, hs]
          _ = (2 : ℝ) • w + w * i ^ 2 + i * w * i := by
            rw [sq, add_mul]
            group
            abel
          _ = (2 : ℝ) • w + (-1 : ℝ) • w + i * w * i := by
            rw [hi]
            simp
          _ = J := by
            rw [← add_smul, add_comm _ (i * w * i)]
            norm_num
            rfl

      have hJ0 : J ≠ 0 := by
        contrapose! hwnmem with hJ0
        rw [hJ0] at hJeq
        have hwsi : - (s • i) = (2 : ℝ) • w := neg_eq_of_add_eq_zero_left hJeq.symm
        rw [Submodule.mem_span_singleton]
        use -s / 2
        rw [div_eq_inv_mul, ← smul_smul, neg_smul, hwsi, smul_smul, inv_mul_cancel₀ (by simp),
          one_smul]

      obtain ⟨J', hJ'0, hJ'⟩ := (mem_purelyImaginary_iff D).mp hJmem

      let j := (Real.sqrt (-J'))⁻¹ • J
      let k := (Real.sqrt (-J'))⁻¹ • K
      have hjmem : j ∈ PurelyImaginary D := Submodule.smul_mem _ _ hJmem
      have hkmem : k ∈ PurelyImaginary D := Submodule.smul_mem _ _ hKmem

      have hj : j ^ 2 = algebraMap ℝ D (-1) := by
        rw [smul_pow, ← hJ', Algebra.smul_def, ← map_mul, inv_pow,
          Real.sq_sqrt (by simpa using hJ'0)]
        rw [inv_neg, neg_mul, inv_mul_cancel₀ ?_]
        contrapose! hJ0
        rw [hJ0] at hJ'
        exact pow_eq_zero (n := 2) (by simpa using hJ'.symm)
      have hk : k ^ 2 = algebraMap ℝ D (-1) := by
        rw [smul_pow, ← hJK, ← smul_pow]
        exact hj

      have hij : i * j = k := calc
        i * j = (Real.sqrt (-J'))⁻¹ • (i * (i * w * i + w)) := by apply mul_smul_comm
        _ = (Real.sqrt (-J'))⁻¹ • (i ^ 2 * w * i + i * w) := by
          rw [sq, mul_add]
          group
        _ = (Real.sqrt (-J'))⁻¹ • (-(w * i) + i * w) := by
          rw [hi]
          simp
        _ = (Real.sqrt (-J'))⁻¹ • (i * w - w * i) := by rw [neg_add_eq_sub]
        _ = k := rfl

      have hji : j * i = -k := calc
        j * i = (Real.sqrt (-J'))⁻¹ • ((i * w * i + w) * i) := by apply smul_mul_assoc
        _ = (Real.sqrt (-J'))⁻¹ • (i * w * i ^ 2 + w * i) := by
          rw [sq, add_mul]
          group
        _ = (Real.sqrt (-J'))⁻¹ • (- (i * w) + w * i) := by
          rw [hi]
          simp
        _ = -((Real.sqrt (-J'))⁻¹ • (i * w - w * i)) := by
          rw [← smul_neg (Real.sqrt (-J'))⁻¹, neg_sub, neg_add_eq_sub]
        _ = -k := rfl

      have hjk : j * k = i := calc
        j * k = -(j * (-k)) := by simp
        _ = -(j ^ 2 * i) := by
          rw [sq, ← hji]
          group
        _ = -(algebraMap ℝ D (-1) * i) := by rw [hj]
        _ = i := by simp

      have hkj : k * j = -i := calc
        k * j = i * j ^ 2 := by
          rw [sq, ← hij]
          group
        _ = i * algebraMap ℝ D (-1) := by rw [hj]
        _ = -i := by simp

      have hki : k * i = j := calc
        k * i = -((-k) * i) := by simp
        _ = -(j * i ^ 2) := by
          rw [sq, ← hji]
          group
        _ = -(j * algebraMap ℝ D (-1)) := by rw [hi]
        _ = j := by simp

      have hik : i * k = -j := calc
        i * k = i ^ 2 * j := by
          rw [sq, ← hij]
          group
        _ = algebraMap ℝ D (-1) * j := by rw [hi]
        _ = -j := by simp

      have hcii : circle i i = algebraMap ℝ D (-2) := by
        unfold circle
        simp_rw [← sq, hi]
        rw [← map_add]
        norm_num

      have hcjj : circle j j = algebraMap ℝ D (-2) := by
        unfold circle
        simp_rw [← sq, hj]
        rw [← map_add]
        norm_num

      have hckk : circle k k = algebraMap ℝ D (-2) := by
        unfold circle
        simp_rw [← sq, hk]
        rw [← map_add]
        norm_num

      have hcij : circle i j = 0 := by
        unfold circle
        rw [hij, hji]
        simp

      have hcji : circle j i = 0 := by
        unfold circle
        rw [hij, hji]
        simp

      have hcjk : circle j k = 0 := by
        unfold circle
        rw [hjk, hkj]
        simp

      have hckj : circle k j = 0 := by
        unfold circle
        rw [hjk, hkj]
        simp

      have hcik : circle i k = 0 := by
        unfold circle
        rw [hik, hki]
        simp

      have hcki : circle k i = 0 := by
        unfold circle
        rw [hik, hki]
        simp

      have hnorm (a b c d : ℝ) : (a • 1 + b • i + c • j + d • k) *
          (a • 1 - b • i - c • j - d • k) =
          algebraMap ℝ D (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
        simp_rw [add_mul, mul_sub, smul_mul_smul, ← sq, hi, hj, hk, hji, hij, hjk, hkj, hki, hik]
        simp_rw [mul_comm b a, mul_comm c a, mul_comm d a, mul_comm c b, mul_comm d b, mul_comm d c]
        simp_rw [map_add]
        rw [Algebra.algebraMap_eq_smul_one (a ^ 2)]
        rw [Algebra.algebraMap_eq_smul_one (b ^ 2)]
        rw [Algebra.algebraMap_eq_smul_one (c ^ 2)]
        rw [Algebra.algebraMap_eq_smul_one (d ^ 2)]
        simp
        abel

      let basisSet := ![1, i, j, k]
      have hindep : LinearIndependent ℝ basisSet := by
        rw [Fintype.linearIndependent_iff']
        rw [← le_bot_iff]
        intro x hx
        rw [LinearMap.mem_ker] at hx
        suffices x = 0 by simpa using this
        have hx : ∑ n, x n • basisSet n = 0 := by simpa using hx
        have h0 : x 0 • (1 : D) + x 1 • i + x 2 • j + x 3 • k = 0 := by
          convert hx
          symm
          apply Fin.sum_univ_four
        have h0 : algebraMap ℝ D (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2) = 0 := by
          rw [← hnorm, h0]
          simp
        have h0 : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + x 3 ^ 2 = 0 := by
          apply FaithfulSMul.algebraMap_injective ℝ D
          simpa using h0
        have h0 : ∑ n : Fin 4, (x n) ^ 2 = 0 := by
          convert h0
          apply Fin.sum_univ_four
        rw [Fintype.sum_eq_zero_iff_of_nonneg (by
          rw [Pi.le_def]
          intro n
          simpa using sq_nonneg (x n))] at h0
        ext n
        simpa using congrFun h0 n

      have hspan : ⊤ ≤ Submodule.span ℝ (Set.range basisSet) := by
        intro v _
        refine (Submodule.mem_span_range_iff_exists_fun ℝ).mpr ?_
        obtain ⟨v0, hv0, v123, hv123, hv⟩ := (Submodule.sup_eq_top_iff _ _).mp hcompl.sup_eq_top v
        obtain ⟨x0, h0⟩ := Set.mem_range.mp <| Algebra.mem_bot.mp hv0
        obtain ⟨x1, h1⟩ := circle_real D hv123 himem
        obtain ⟨x2, h2⟩ := circle_real D hv123 hjmem
        obtain ⟨x3, h3⟩ := circle_real D hv123 hkmem
        use ![x0, -2⁻¹ * x1, -2⁻¹ * x2, -2⁻¹ * x3]
        rw [Fin.sum_univ_four]
        unfold basisSet
        suffices x0 • 1 + -((2⁻¹ * x1) • i) + -((2⁻¹ * x2) • j) + -((2⁻¹ * x3) • k) = v by
          simpa using this
        simp_rw [← smul_smul]
        rw [Algebra.smul_def x0, Algebra.smul_def x1, Algebra.smul_def x2, Algebra.smul_def x3]
        rw [h0, h1, h2, h3, hv]
        rw [add_assoc, add_assoc, mul_one]
        apply add_left_cancel_iff.mpr
        let e := (2 : ℝ) • v123 +
          (circle v123 i) * i + (circle v123 j) * j + (circle v123 k) * k
        suffices e = 0 by
          unfold e at this
          rw [add_assoc, add_assoc, add_comm ((2 : ℝ) • v123), ← neg_eq_iff_add_eq_zero] at this
          rw [← inv_smul_eq_iff₀ (by simp)] at this
          simp only [smul_neg, smul_add] at this
          convert this using 1
          abel
        have hei : circle e i = 0 := by
          unfold e
          simp only [circle_right_distrib, ← h1, ← h2, ← h3, ← Algebra.smul_def, circle_left_smul,
            hcii, hcji, hcki, smul_zero, add_zero]
          simp_rw [Algebra.smul_def, ← map_mul, ← map_add]
          suffices 2 * x1 + x1 * -2 = 0 by
            rw [this]
            simp
          rw [mul_comm x1, neg_mul, ← sub_eq_add_neg, sub_self]

        have hej : circle e j = 0 := by
          unfold e
          simp only [circle_right_distrib, ← h1, ← h2, ← h3, ← Algebra.smul_def, circle_left_smul,
            hcjj, hcij, hckj, smul_zero, add_zero]
          simp_rw [Algebra.smul_def, ← map_mul, ← map_add]
          suffices 2 * x2 + x2 * -2 = 0 by
            rw [this]
            simp
          rw [mul_comm x2, neg_mul, ← sub_eq_add_neg, sub_self]

        have hek : circle e k = 0 := by
          unfold e
          simp only [circle_right_distrib, ← h1, ← h2, ← h3, ← Algebra.smul_def, circle_left_smul,
            hckk, hcik, hcjk, smul_zero, add_zero]
          simp_rw [Algebra.smul_def, ← map_mul, ← map_add]
          suffices 2 * x3 + x3 * -2 = 0 by
            rw [this]
            simp
          rw [mul_comm x3, neg_mul, ← sub_eq_add_neg, sub_self]

        have := calc
          e * k = e * i * j := by
            rw [← hij]
            group
          _ = (-(i * e)) * j := by
            congr 1
            apply (neg_eq_iff_add_eq_zero.mpr ?_).symm
            rw [add_comm]
            exact hei
          _ = i * (-(e * j)) := by
            simp only [neg_mul, mul_neg, neg_inj]
            group
          _ = i * j * e := by
            rw [neg_eq_iff_add_eq_zero.mpr hej]
            group
          _ = k * e := by rw [hij]

        have hek' : e * k + k * e = 0 := hek
        rw [this, ← two_smul ℝ, smul_eq_zero, mul_eq_zero] at hek'
        have hk0 : k ≠ 0 := by
          contrapose! hk
          rw [hk]
          simp
        simpa [hk0] using hek'

      let basis := Basis.mk hindep hspan
      have basis00 : basis 0 * basis 0 = basis 0 := by simp [basis, basisSet]
      have basis01 : basis 0 * basis 1 = basis 1 := by simp [basis, basisSet]
      have basis02 : basis 0 * basis 2 = basis 2 := by simp [basis, basisSet]
      have basis03 : basis 0 * basis 3 = basis 3 := by simp [basis, basisSet]
      have basis10 : basis 1 * basis 0 = basis 1 := by simp [basis, basisSet]
      have basis11 : basis 1 * basis 1 = -basis 0 := by simp [basis, basisSet, ← sq, hi]
      have basis12 : basis 1 * basis 2 = basis 3 := by simp [basis, basisSet, hij]
      have basis13 : basis 1 * basis 3 = -basis 2 := by simp [basis, basisSet, hik]
      have basis20 : basis 2 * basis 0 = basis 2 := by simp [basis, basisSet]
      have basis21 : basis 2 * basis 1 = -basis 3 := by simp [basis, basisSet, hji]
      have basis22 : basis 2 * basis 2 = -basis 0 := by simp [basis, basisSet, ← sq, hj]
      have basis23 : basis 2 * basis 3 = basis 1 := by simp [basis, basisSet, hjk]
      have basis30 : basis 3 * basis 0 = basis 3 := by simp [basis, basisSet]
      have basis31 : basis 3 * basis 1 = basis 2 := by simp [basis, basisSet, hki]
      have basis32 : basis 3 * basis 2 = -basis 1 := by simp [basis, basisSet, hkj]
      have basis33 : basis 3 * basis 3 = -basis 0 := by simp [basis, basisSet, ← sq, hk]


      right
      right

      have q0 : basisOneIJK ℝ 0 = 1 := by
        unfold basisOneIJK QuaternionAlgebra.basisOneIJK
        show ⇑(Basis.ofEquivFun (QuaternionAlgebra.linearEquivTuple (-1) 0 (-1))) 0 = 1
        rw [Basis.coe_ofEquivFun]
        rfl

      let linEquiv : D ≃ₗ[ℝ] ℍ[ℝ] := Basis.equiv basis (basisOneIJK ℝ) (Equiv.refl _)
      refine Nonempty.intro (AlgEquiv.ofLinearEquiv_basis linEquiv ?_ basis ?_)
      · rw [show (1 : D) = basis 0 by
          unfold basis basisSet;
          simp
        ]
        rw [Basis.equiv_apply basis 0 _ _]
        simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Equiv.refl_apply]
        rw [q0]
      ·
        intro i j
        rw [Basis.equiv_apply basis i, Basis.equiv_apply basis j]
        simp
        fin_cases i
        · fin_cases j
          · rw [show basis _ * basis _ = _ by exact basis00]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK00 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis01]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK01 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis02]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK02 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis03]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK03 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
        · fin_cases j
          · rw [show basis _ * basis _ = _ by exact basis10]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK10 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis11]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK11 ℝ]
            rw [map_neg, Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis12]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK12 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis13]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK13 ℝ]
            rw [map_neg, Basis.equiv_apply basis]
            rfl
        · fin_cases j
          · rw [show basis _ * basis _ = _ by exact basis20]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK20 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis21]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK21 ℝ]
            rw [map_neg, Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis22]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK22 ℝ]
            rw [map_neg, Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis23]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK23 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
        · fin_cases j
          · rw [show basis _ * basis _ = _ by exact basis30]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK30 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis31]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK31 ℝ]
            rw [Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis32]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK32 ℝ]
            rw [map_neg, Basis.equiv_apply basis]
            rfl
          · rw [show basis _ * basis _ = _ by exact basis33]
            rw [show basisOneIJK ℝ _ * basisOneIJK ℝ _ = _ by exact basisOneIJK33 ℝ]
            rw [map_neg, Basis.equiv_apply basis]
            rfl
