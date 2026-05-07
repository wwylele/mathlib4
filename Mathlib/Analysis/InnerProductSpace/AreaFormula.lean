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
theorem mem_ball2 (hb : Eprop B t ε f c T i b) : b ∈ Metric.ball c (2 / i : ℝ) := by
  have hbc := hb.mem_ball
  rw [Metric.mem_ball] at ⊢ hbc
  apply hbc.trans_le
  apply (div_le_div_iff₀ (by simp) (by simp)).mpr
  grind

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
  obtain h3left := hb.h3left ha.mem_ball2
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

structure Piece (t : NNReal) (f : U → V) where
  E : Set U
  T : U ≃ₗ[ℝ] U
  injOn : Set.InjOn f E
  lipschitz : LipschitzOnWith t (f ∘ T.symm) (T '' E)
  lipschitz_inv : LipschitzOnWith t (T ∘ f.invFunOn E) (f '' E)
  det_le : ∀ x ∈ E, (↑t)⁻¹ ^ finrank ℝ U * |T.toLinearMap.det| ≤ (fderiv ℝ f x).normDet
  le_det : ∀ x ∈ E, (fderiv ℝ f x).normDet ≤ t ^ finrank ℝ U * |T.toLinearMap.det|

omit [FiniteDimensional ℝ U] in
theorem Piece.inj (B : Set U) (t : NNReal) (ht : 1 < t) (ε : ℝ) (f : U → V)
    (hker : ∀ x ∈ B, (fderiv ℝ f x).ker = ⊥) (c : U) (T : U ≃ₗ[ℝ] U) (i : PNat) :
    Set.InjOn f {b | Eprop B (↑t) ε f c (↑T) i b} := by
  intro a ha b hb h
  exact Eprop.inj hker ht ha hb h

def Piece.mk' [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    (B : Set U) (t : NNReal) (ht : 1 < t) (ε : ℝ)
    (hεpos : 0 < (↑t)⁻¹ + ε) (h0ε : 0 ≤ ε) (hεright : 1 < t - ε)
    (f : U → V) (hker : ∀ x ∈ B, (fderiv ℝ f x).ker = ⊥) (c : U) (T : U ≃ₗ[ℝ] U) (i : PNat) :
    Piece t f where
  E := {b | Eprop B t ε f c T i b}
  T := T
  injOn := by apply Piece.inj B t ht ε f hker
  lipschitz := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    simp only [Set.mem_image, Set.mem_setOf_eq] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply, dist_eq_norm, ← map_sub]
    apply hb.h3right ha.mem_ball2
  lipschitz_inv := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro a ha b hb
    simp only [Set.mem_image, Set.mem_setOf_eq] at ha hb
    obtain ⟨a, ha, rfl⟩ := ha
    obtain ⟨b, hb, rfl⟩ := hb
    simp only [Function.comp_apply, dist_eq_norm, ← map_sub]
    rw [Set.InjOn.leftInvOn_invFunOn (by apply Piece.inj B t ht ε f hker) (by simpa using ha)]
    rw [Set.InjOn.leftInvOn_invFunOn (by apply Piece.inj B t ht ε f hker) (by simpa using hb)]
    rw [← inv_mul_le_iff₀ (by
      rw [NNReal.coe_pos]
      apply lt_trans (by norm_num) ht
    )]
    apply hb.h3left ha.mem_ball2
  det_le x hx := by
    refine le_trans ?_ (Eprop.hclaimleft hx hεpos)
    refine mul_le_mul_of_nonneg_right ?_ (by simp)
    apply pow_le_pow_left₀ (by simp)
    simpa using h0ε
  le_det x hx := by
    apply (Eprop.hclaimright hx hεright).trans
    refine mul_le_mul_of_nonneg_right ?_ (by simp)
    have h := (show (0 : ℝ) < 1 by norm_num).trans hεright
    apply pow_le_pow_left₀ (by simpa using h.le)
    simpa using h0ε

-- begin Aristotle
lemma ContinuousLinearMap.exists_pos_lower_bound
    {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [FiniteDimensional ℝ U]
    {f : U →L[ℝ] U} (hf : f.ker = ⊥) :
    ∃ c : ℝ, 0 < c ∧ ∀ x : U, c * ‖x‖ ≤ ‖f x‖ := by
  -- Use the fact that a linear map on a finite-dimensional space is injective if and only if it
  -- is bounded below.
  have h_inj : Function.Injective f := by
    exact LinearMap.ker_eq_bot.mp hf;
  obtain ⟨ K, hK ⟩ := f.toLinearMap.injective_iff_antilipschitz.mp h_inj;
  refine ⟨ 1 / K, ?_, ?_ ⟩;
  · exact one_div_pos.mpr ( NNReal.coe_pos.mpr hK.1 );
  · intro x; have := hK.2.le_mul_dist x 0
    simp only [dist_zero_right, coe_coe, map_zero] at this
    simp only [gt_iff_lt, coe_coe] at hK
    simp only [div_eq_inv_mul, mul_one, ge_iff_le] ;
    rwa [ inv_mul_le_iff₀ ( NNReal.coe_pos.mpr hK.1 ) ]

theorem approx_linear_map {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
    [FiniteDimensional ℝ U]
    {s : Set (U →L[ℝ] U)} (hs : Dense s) {f : U →L[ℝ] U} (hf : f.ker = ⊥)
    {a b : ℝ} (ha : a < 1) (hb : 1 < b) :
    ∃ g ∈ s, (∀ x, a * ‖g x‖ ≤ ‖f x‖) ∧ (∀ x, ‖f x‖ ≤ b * ‖g x‖) := by
  -- Use `ContinuousLinearMap.exists_pos_lower_bound` to get c > 0 with c * ‖x‖ ≤ ‖f x‖ for all
  -- x.
  obtain ⟨c, hc⟩ : ∃ c > 0, ∀ x : U, c * ‖x‖ ≤ ‖f x‖ := by
    exact ContinuousLinearMap.exists_pos_lower_bound hf;
  -- Choose δ such that δ < c and δ < c*(1-a) and δ < c*(1-1/b).
  obtain ⟨δ, hδ_pos, hδ_lt_c, hδ_lt_ca, hδ_lt_cb⟩ : ∃ δ > 0, δ < c ∧ δ < c * (1 - a) ∧
      δ < c * (1 - 1 / b) := by
    obtain ⟨δ, hδ_pos, hδ_lt⟩ : ∃ δ > 0, δ < min (c * (1 - a)) (c * (1 - 1 / b)) := by
      exact exists_between ( lt_min ( mul_pos hc.1 ( sub_pos.2 ha ) ) ( mul_pos hc.1 ( sub_pos.2
        ( by rw [ div_lt_iff₀ ] <;> linarith ) ) ) );
    exact ⟨ Min.min δ c / 2, half_pos ( lt_min hδ_pos hc.1 ), by
      linarith [ min_le_left δ c, min_le_right δ c ],
      by linarith [ min_le_left δ c, min_le_right δ c,
        min_le_left ( c * ( 1 - a ) ) ( c * ( 1 - 1 / b ) ),
        min_le_right ( c * ( 1 - a ) ) ( c * ( 1 - 1 / b ) ) ],
      by linarith [ min_le_left δ c, min_le_right δ c,
        min_le_left ( c * ( 1 - a ) ) ( c * ( 1 - 1 / b ) ),
        min_le_right ( c * ( 1 - a ) ) ( c * ( 1 - 1 / b ) ) ] ⟩;
  -- Choose g ∈ s such that ‖g - f‖ < δ.
  obtain ⟨g, hg_s, hg_dist⟩ : ∃ g ∈ s, ‖g - f‖ < δ := by
    simpa [ dist_eq_norm' ] using hs.exists_dist_lt f hδ_pos;
  refine ⟨ g, hg_s, fun x => ?_, fun x => ?_ ⟩;
  · have := ContinuousLinearMap.le_opNorm ( g - f ) x;
    simp_all +decide;
    nlinarith [ norm_nonneg x, norm_nonneg ( g x - f x ), norm_nonneg ( g x ),
      norm_nonneg ( f x ), mul_inv_cancel₀ ( ne_of_gt ( zero_lt_one.trans hb ) ),
      hc.2 x, mul_le_mul_of_nonneg_left hg_dist.le ( norm_nonneg x ),
      mul_le_mul_of_nonneg_left hg_dist.le ( norm_nonneg ( g x - f x ) ),
      mul_le_mul_of_nonneg_left hg_dist.le ( norm_nonneg ( g x ) ),
      mul_le_mul_of_nonneg_left hg_dist.le ( norm_nonneg ( f x ) ),
      norm_sub_norm_le ( g x ) ( f x ) ];
  · -- Using the triangle inequality and the bounds on δ, we get:
    have h_triangle : ‖g x‖ ≥ ‖f x‖ - δ * ‖x‖ := by
      have := ContinuousLinearMap.le_of_opNorm_le _ hg_dist.le x;
      simpa using norm_sub_le ( g x ) ( ( g - f ) x ) |> le_trans <| by simpa using this;
    nlinarith [ hc.2 x, norm_nonneg x, norm_nonneg ( f x ), norm_nonneg ( g x ),
      mul_div_cancel₀ 1 ( by linarith : b ≠ 0 ),
      mul_le_mul_of_nonneg_left hδ_lt_cb.le ( norm_nonneg x ),
        mul_le_mul_of_nonneg_left hδ_lt_ca.le ( norm_nonneg x ),
        mul_le_mul_of_nonneg_left hδ_lt_c.le ( norm_nonneg x ) ]

-- end Aristotle

theorem lemma3_3 [Nontrivial U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace V]
    (t : NNReal) (ht : 1 < t) (f : U → V) (B : Set U)
    (hker : ∀ x ∈ B, (fderiv ℝ f x).ker = ⊥) :
    ∃ (Es : Set (Piece t f)), Es.Countable ∧ B = ⋃ p ∈ Es, p.E := by
  have ht' : (1 : ℝ) < t := by simpa using ht
  let ε : ℝ := (t - 1) / (2 * t)
  have h0ε' : 0 < ε := by
    unfold ε
    apply div_pos (by simpa using ht')
    positivity
  have h0ε : 0 ≤ ε := by
    unfold ε
    apply div_nonneg (by simpa using ht'.le)
    simp
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
  have hU := TopologicalSpace.exists_countable_dense B
  have hUU := TopologicalSpace.exists_countable_dense (U →L[ℝ] U)
  let C := hU.choose
  let S : Set (U ≃ₗ[ℝ] U) := LinearEquiv.toLinearMap ⁻¹'
    (ContinuousLinearMap.toLinearMap '' hUU.choose)
  use ⋃ c ∈ C, ⋃ T ∈ S, Set.range (Piece.mk' B t ht ε hεpos h0ε hεright f hker c T)
  constructor
  · rw [Set.Countable.biUnion_iff (by
      apply hU.choose_spec.1)]
    intro _ _
    rw [Set.Countable.biUnion_iff (by
      refine Set.Countable.preimage ?_ (LinearEquiv.toLinearMap_injective)
      apply hUU.choose_spec.1.image)]
    intro _ _
    apply Set.countable_range
  apply subset_antisymm
  · intro b hb
    have hdiff : DifferentiableAt ℝ f b := by
      specialize hker b hb
      contrapose! hker
      simp [fderiv_zero_of_not_differentiableAt hker]
    obtain ⟨o, s, hos, hs⟩ := eixsts_polar_decomposition (fderiv ℝ f b).toLinearMap (hker b hb)
    simp only [Set.mem_iUnion, Set.mem_range, exists_prop, Set.iUnion_exists, Set.biUnion_and',
      Set.iUnion_iUnion_eq', Piece.mk', Set.mem_setOf_eq]
    have hs' : s.toContinuousLinearMap.ker = ⊥ := hs
    obtain ⟨T', hT', hTleft, hTright⟩ := approx_linear_map hUU.choose_spec.2 hs' hεleft hεright
    have hTker : T'.ker = ⊥ := by
      contrapose! hTright with hker
      obtain ⟨x, hx, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
      use x
      rw [mem_ker, ContinuousLinearMap.coe_coe] at hx
      suffices x ∉ s.ker by
        simpa [hx]
      simpa [hs] using hx0
    let T : U ≃ₗ[ℝ] U := LinearEquiv.ofInjectiveEndo T'.toLinearMap (LinearMap.ker_eq_bot.mp hTker)
    have hTS : T ∈ S := by
      simp only [Set.mem_preimage, Set.mem_image, S]
      use T', hT'
      rfl
    have hT : T.symm.toLinearMap ≠ 0 := by
      intro h
      simpa using congr(LinearMap.ker $h)
    have hbound : 0 < ε / ‖T.symm.toContinuousLinearMap‖ := by
      apply div_pos h0ε'
      simpa using hT
    obtain ⟨r, hr0, hr⟩ := Metric.eventually_nhds_iff_ball.mp <|
      hdiff.hasFDerivAt.isLittleO.bound hbound
    let i := Nat.toPNat ⌈3 / r⌉₊ (by simpa using hr0)
    have hi : (0 : ℝ) < 1 / i := by simp
    obtain ⟨c, hcm, hc⟩ := Dense.exists_dist_lt hU.choose_spec.2 ⟨b, hb⟩ hi
    have hc : dist b c < 1 / i := hc
    use c, hcm, T, hTS, i
    exact {
      mem_B := hb
      mem_ball := by
        simpa using hc
      h1left u := by
        change ((↑t)⁻¹ + ε) * ‖T' u‖ ≤ ‖(fderiv ℝ f b).toLinearMap u‖
        rw [← hos]
        simpa using hTleft u
      h1right u := by
        change ‖(fderiv ℝ f b).toLinearMap u‖ ≤ (↑t - ε) * ‖T' u‖
        rw [← hos]
        simpa using hTright u
      h2 a ha := by
        have hab : a ∈ Metric.ball b r := by
          rw [Metric.mem_ball] at ⊢ ha
          rw [dist_comm] at hc
          apply (dist_triangle _ c.val _).trans_lt
          apply lt_of_lt_of_le (add_lt_add ha hc)
          rw [← add_div]
          norm_num
          change 3 / ⌈3 / r⌉₊ ≤ r
          rw [div_le_comm₀ (by simpa using hr0) hr0]
          exact Nat.le_ceil (3 / r)
        apply (hr a hab).trans
        rw [div_mul_eq_mul_div, div_le_iff₀ (by simpa using hT), mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ h0ε
        rw [mul_comm]
        convert ContinuousLinearMap.le_opNorm T.symm.toContinuousLinearMap (T.toLinearMap (a - b))
          using 1
        simp
    }
  simp [Piece.mk']
  grind [Eprop.mem_B]


theorem area_formula [MeasurableSpace U] [BorelSpace U] [MeasurableSpace V] [BorelSpace V]
    [CompleteSpace V]
    (K : NNReal) (f : U → V) (A : Set U)
    (hf : LipschitzOnWith K f A)
    (hker : ∀ x ∈ A, (fderiv ℝ f x).ker = ⊥) :
    ∫⁻ x in A, ENNReal.ofReal (fderiv ℝ f x).normDet =
    ∫⁻ (y : V),  (A ∩ f ⁻¹' {y}).encard.toENNReal ∂(μHE[finrank ℝ U]) := sorry
