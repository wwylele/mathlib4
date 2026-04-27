/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

module

public import Mathlib.Analysis.InnerProductSpace.NormDet
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


open MeasureTheory RealInnerProductSpace Module LinearMap
section random

variable {𝕜 U V W : Type*} [RCLike 𝕜] [NormedAddCommGroup U] [InnerProductSpace 𝕜 U]
  [FiniteDimensional 𝕜 U] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V] [NormedAddCommGroup W]
  [InnerProductSpace 𝕜 W]

theorem eixsts_polar_decomposition (f : U →ₗ[𝕜] V) (h : f.ker = ⊥) :
    ∃ (u : U →ₗᵢ[𝕜] V) (p : U →ₗ[𝕜] U),
    u.toLinearMap ∘ₗ p = f ∧ p.ker = ⊥ := by
  have hrank : finrank 𝕜 f.range = finrank 𝕜 U := by
    obtain hrank := f.finrank_range_add_finrank_ker
    rw [h] at hrank
    simpa [h] using hrank
  let bu : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 U := stdOrthonormalBasis 𝕜 U
  let bv : OrthonormalBasis (Fin (finrank 𝕜 U)) 𝕜 f.range :=
    (stdOrthonormalBasis 𝕜 f.range).reindex (by rw [hrank])
  let g := OrthonormalBasis.equiv bu bv (Equiv.refl _)
  use (Submodule.subtypeₗᵢ f.range).comp g.toLinearIsometry, g.symm.toLinearMap.comp f.rangeRestrict
  constructor
  · change f.range.subtype ∘ₗ (g.toLinearMap ∘ₗ g.symm.toLinearMap) ∘ₗ f.rangeRestrict = f
    simp
  · simpa using h

end random


variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

omit [FiniteDimensional ℝ U] in
theorem image_ball {r : ℝ} (hr : 0 < r) : (r • LinearMap.id : U →ₗ[ℝ] U) '' Metric.ball 0 1 =
    Metric.ball 0 r := by
  ext x
  simp only [smul_apply, id_coe, id_eq, Set.mem_image, Metric.mem_ball, dist_zero_right]
  constructor
  · intro ⟨y, h1, h2⟩
    rw [← h2, norm_smul]
    rw [Real.norm_eq_abs, abs_of_nonneg hr.le]
    apply mul_lt_of_lt_one_right hr h1
  · intro h
    use r⁻¹ • x
    constructor
    · rw [norm_smul]
      rw [norm_inv, Real.norm_eq_abs, abs_of_nonneg hr.le]
      exact (inv_mul_lt_one₀ hr).mpr h
    · simp [smul_smul, hr.ne.symm]

theorem volume_ball_ne_zero [MeasurableSpace U] [BorelSpace U] [Nontrivial U] :
    volume (Metric.ball 0 1 : Set U) ≠ 0 := by
  rw [InnerProductSpace.volume_ball]
  positivity

theorem volume_ball_ne_top [MeasurableSpace U] [BorelSpace U] :
    volume (Metric.ball 0 1 : Set U) ≠ ⊤ := by
  nontriviality U
  rw [InnerProductSpace.volume_ball]
  simp

structure Eprop (B : Set U) (t ε : ℝ) (f : U → V) (c : U) (T : U →ₗ[ℝ] U) (i : PNat) (b : U) where
  mem_B : b ∈ B
  mem_ball : b ∈ Metric.ball c (1 / i : ℝ)
  h1left : ∀ u : U, (t⁻¹ + ε) * ‖T u‖ ≤ ‖fderiv ℝ f b u‖
  h1right : ∀ u : U, ‖fderiv ℝ f b u‖ ≤ (t - ε) * ‖T u‖
  h2 : ∀ a ∈ Metric.ball c (2 / i : ℝ), ‖f a - f b - fderiv ℝ f b (a - b)‖ ≤ ε * ‖T (a - b)‖

namespace Eprop

variable {B : Set U} {t ε : ℝ} {f : U → V} {c : U} {T : U →ₗ[ℝ] U} {i : PNat} {b : U}

omit [FiniteDimensional ℝ U] in
theorem h3left (hb : Eprop B t ε f c T i b) {a : U} (ha : a ∈ Metric.ball c (2 / i : ℝ)) :
    t⁻¹ * ‖T (a - b)‖ ≤ ‖f a - f b‖ := by
  obtain h := hb.h1left (a - b)
  rw [add_mul, ← le_sub_iff_add_le] at h
  apply h.trans
  rw [sub_le_comm]
  apply le_trans ?_ (hb.h2 a ha)
  apply (norm_sub_norm_le _ _).trans
  rw [norm_sub_rev]

omit [FiniteDimensional ℝ U] in
theorem h3right (hb : Eprop B t ε f c T i b) {a : U} (ha : a ∈ Metric.ball c (2 / i : ℝ)) :
    ‖f a - f b‖ ≤ t * ‖T (a - b)‖ := by
  obtain h := hb.h1right (a - b)
  rw [sub_mul, le_sub_iff_add_le] at h
  apply le_trans ?_ h
  rw [← sub_le_iff_le_add']
  apply le_trans ?_ (hb.h2 a ha)
  apply norm_sub_norm_le

omit [FiniteDimensional ℝ U] in
theorem inj (hker : ∀ x ∈ B, (fderiv ℝ f x).ker = ⊥) (ht : 1 < t)
    {a b : U} (ha : Eprop B t ε f c T i a) (hb : Eprop B t ε f c T i b) (h : f a = f b) :
    a = b := by
  have htpos : 0 < t := lt_trans (by norm_num) ht
  have htnonneg : 0 ≤ t := htpos.le
  have htnotnonpos : ¬ t ≤ 0 := by simpa using htpos
  have hac := ha.mem_ball
  have ha' : a ∈ Metric.ball c (2 / i : ℝ) := by
    rw [Metric.mem_ball] at ⊢ hac
    apply hac.trans_le
    apply (div_le_div_iff₀ (by simp) (by simp)).mpr
    grind
  obtain h3left := hb.h3left ha'
  rw [h, sub_self, norm_zero, mul_nonpos_iff] at h3left
  have hab : T (a - b) = 0 := by simpa [htnonneg, htnotnonpos] using h3left
  have h1right := hb.h1right (a - b)
  have hab' : a - b ∈ (fderiv ℝ f b).ker := by simpa [hab] using h1right
  rw [hker b hb.mem_B] at hab'
  simpa [sub_eq_zero] using hab'

theorem hclaimright [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    (hb : Eprop B t ε f c T i b) (hεright : 1 < t - ε) :
    (fderiv ℝ f b).normDet ≤ (t - ε) ^ finrank ℝ U * |T.det| := by
  nontriviality U
  by_cases hT : T.ker = ⊥
  · by_cases hf : (fderiv ℝ f b).ker = ⊥
    · let T' := LinearEquiv.ofInjectiveEndo T (LinearMap.ker_eq_bot.mp hT)
      have h (v : U) := hb.h1right (T'.symm v)
      have hsymm (v : U) : T (T'.symm v) = v := by
        change T' (T'.symm v) = v
        simp
      simp_rw [hsymm] at h
      obtain ⟨u, p, hu, _⟩ := eixsts_polar_decomposition (fderiv ℝ f b) (by simpa using hf)
      have hball : (p ∘ₗ T'.symm.toLinearMap) '' Metric.ball 0 1
          ⊆ ((t - ε) • LinearMap.id : U →ₗ[ℝ] U) '' Metric.ball 0 1 := by
        rw [image_ball (lt_trans (by norm_num) hεright)]
        intro v
        simp only [coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
          Set.mem_image, Metric.mem_ball, dist_zero_right, forall_exists_index, and_imp]
        intro x hx rfl
        suffices ‖fderiv ℝ f b (T'.symm x)‖ < ↑t - ε by
          change ‖(fderiv ℝ f b).toLinearMap (T'.symm x)‖ < ↑t - ε at this
          rw [← hu] at this
          simpa using this
        apply lt_of_le_of_lt (h x)
        exact mul_lt_of_lt_one_right (lt_trans (by norm_num) hεright) hx
      obtain hmeasure := MeasureTheory.measure_mono hball (μ := volume)
      simp_rw [MeasureTheory.Measure.addHaar_image_linearMap] at hmeasure
      rw [ENNReal.mul_le_mul_iff_left volume_ball_ne_zero volume_ball_ne_top] at hmeasure
      rw [ENNReal.ofReal_le_ofReal_iff (by simp)] at hmeasure
      simp only [det_comp, LinearEquiv.det_coe_symm, abs_mul, abs_inv] at hmeasure
      rw [mul_inv_le_iff₀ (by simp [← LinearEquiv.coe_det])] at hmeasure
      convert hmeasure
      · rw [← hu]
        rw [normDet_comp_of_finrank_eq _ _ (by simp)]
        simp [u.normDet_eq_one, normDet_eq_norm_det]
      · suffices (0 : ℝ) ≤ t - ε by simp [abs_of_nonneg this]
        apply (lt_trans (by norm_num) hεright).le
    · rw [LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hf]
      positivity
  · suffices (fderiv ℝ f b).normDet = 0 by
      simp [this, LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hT]
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hT
    rw [LinearMap.mem_ker] at hv
    obtain h := hb.h1right v
    rw [normDet_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
    refine ⟨v, ?_, hv0⟩
    simpa [hv] using h

theorem hclaimleft [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    (hb : Eprop B t ε f c T i b) (hεpos : 0 < t⁻¹ + ε) :
    (t⁻¹ + ε) ^ finrank ℝ U * |T.det| ≤ (fderiv ℝ f b).normDet := by
  nontriviality U
  by_cases hT : T.ker = ⊥
  · by_cases hf : (fderiv ℝ f b).ker = ⊥
    · let T' := LinearEquiv.ofInjectiveEndo T (LinearMap.ker_eq_bot.mp hT)
      obtain ⟨u, p, hu, hp⟩ := eixsts_polar_decomposition (fderiv ℝ f b) (by simpa using hf)
      have hball : ((t⁻¹ + ε) • LinearMap.id : U →ₗ[ℝ] U) '' Metric.ball 0 1 ⊆
          (p ∘ₗ T'.symm.toLinearMap) '' Metric.ball 0 1 := by
        rw [image_ball (hεpos)]
        intro v
        simp only [Metric.mem_ball, dist_zero_right, coe_comp, LinearEquiv.coe_coe,
          Function.comp_apply, Set.mem_image]
        intro hv
        obtain ⟨w, hw⟩ := LinearMap.surjective_of_injective (LinearMap.ker_eq_bot.mp hp) v
        use T' w
        simp only [LinearEquiv.symm_apply_apply, hw, and_true]
        obtain h : ∀ (u : U), (t⁻¹ + ε) * ‖T u‖ ≤ ‖(fderiv ℝ f b).toLinearMap u‖ := hb.h1left
        specialize h w
        simp_rw [← hu] at h
        simp only [coe_comp, LinearIsometry.coe_toLinearMap, Function.comp_apply, hw,
          LinearIsometry.norm_map] at h
        obtain h := h.trans_lt hv
        rw [mul_lt_iff_lt_one_right hεpos] at h
        exact h
      obtain hmeasure := MeasureTheory.measure_mono hball (μ := volume)
      simp_rw [MeasureTheory.Measure.addHaar_image_linearMap] at hmeasure
      rw [ENNReal.mul_le_mul_iff_left volume_ball_ne_zero volume_ball_ne_top] at hmeasure
      rw [ENNReal.ofReal_le_ofReal_iff (abs_nonneg _)] at hmeasure
      simp only [det_smul, det_id, mul_one, abs_pow, det_comp,
        LinearEquiv.det_coe_symm, abs_mul, abs_inv] at hmeasure
      rw [le_mul_inv_iff₀ (by simp [← LinearEquiv.coe_det])] at hmeasure
      convert hmeasure using 3
      · rw [abs_of_nonneg hεpos.le]
      · rw [← hu]
        rw [normDet_comp_of_finrank_eq _ _ (by simp)]
        simp [u.normDet_eq_one, normDet_eq_norm_det]
    · suffices LinearMap.det T = 0 by
        simp [this, LinearMap.normDet_eq_zero_iff_ker_ne_bot.mpr hf]
      obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hf
      rw [LinearMap.mem_ker] at hv
      obtain h := hb.h1left v
      rw [det_eq_zero_iff_ker_ne_bot, Submodule.ne_bot_iff]
      refine ⟨v, ?_, hv0⟩
      rw [ContinuousLinearMap.coe_coe] at hv
      rw [hv, norm_zero] at h
      obtain h := le_antisymm h (mul_nonneg hεpos.le (by simp))
      simpa [hεpos.ne.symm] using h
  · simpa [LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hT] using normDet_nonneg _

end Eprop

theorem lemma3_3 [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    (t : NNReal) (ht : 1 < t) (K : NNReal) (f : U → V) (B : Set U)
    (hf : LipschitzOnWith K f B)
    (hker : ∀ x ∈ B, (fderiv ℝ f x).ker = ⊥) :
    ∃ (E : ℕ → Set U) (T : ℕ → (U ≃ₗ[ℝ] U)),
      (B = ⋃ k, E k) ∧
      (∀ k, Set.InjOn f (E k)
        ∧ LipschitzOnWith t (f ∘ (T k).symm) (E k)
        ∧ LipschitzOnWith t (T k ∘ f.invFun) (f '' E k)
        ∧ ∀ x ∈ E k,
          t⁻¹ ^ finrank ℝ U * |(T k).toLinearMap.det| ≤ (fderiv ℝ f x).normDet
          ∧ (fderiv ℝ f x).normDet ≤ t ^ finrank ℝ U * |(T k).toLinearMap.det|)
    := by
  have ht' : (1 : ℝ) < t := by simpa using ht
  let ε : ℝ := (t - 1) / (2 * t)
  have hεleft : (↑t)⁻¹ + ε < 1 := by
    unfold ε
    refine lt_of_mul_lt_mul_left ?_ (show 0 ≤ (2 * t : ℝ) by positivity)
    rw [mul_add, mul_assoc, mul_inv_cancel₀ (by positivity)]
    rw [mul_div_cancel₀ _ (by positivity)]
    linarith
  have hεpos : 0 < (↑t)⁻¹ + ε := by
    unfold ε
    apply add_pos (by positivity)
    apply div_pos (by linarith) (by positivity)
  have hεright : 1 < t - ε := by
    unfold ε
    refine lt_of_mul_lt_mul_left ?_ (show 0 ≤ (2 * t : ℝ) by positivity)
    rw [mul_sub, mul_div_cancel₀ _ (by positivity)]
    apply lt_of_sub_pos
    suffices (0 : ℝ) < (t - 1) * (2 * t - 1) by
      convert this using 1
      ring
    apply mul_pos (by linarith) (by linarith)

  let E (c : U) (T : U →ₗ[ℝ] U) (i : PNat) : Set U := {b : U | Eprop B t ε f c T i b}

  let C : Set U := B ∩ (TopologicalSpace.exists_countable_dense U).choose
  let S : Set (U →L[ℝ] U) := (TopologicalSpace.exists_countable_dense (U →L[ℝ] U)).choose
  sorry


theorem area_formula [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    [CompleteSpace V]
    (K : NNReal) (f : U → V) (A : Set U)
    (hf : LipschitzOnWith K f A)
    (hker : ∀ x ∈ A, (fderiv ℝ f x).ker = ⊥) :
    ∫⁻ x in A, ENNReal.ofReal (fderiv ℝ f x).normDet =
    ∫⁻ (y : V),  (A ∩ f ⁻¹' {y}).encard.toENNReal ∂(μHE[finrank ℝ U]) := sorry
