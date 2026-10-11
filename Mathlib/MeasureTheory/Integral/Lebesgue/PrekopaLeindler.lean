/-
Copyright (c) 2026 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Measure.Haar.Disintegration
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Prékopa–Leindler inequality
-/

public section

open scoped ENNReal

namespace MeasureTheory

variable {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {f g j : ℝ → ℝ≥0∞} (hf : Measurable f)
  (hg : Measurable g) (hj : Measurable j)

include ha0 ha1 hf hg hj in
private theorem prekopa_leindler_real_of_iSup_eq_one (hf1 : ⨆ x, f x = 1) (hg1 : ⨆ x, g x = 1)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) * x + a * y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x := by
  open scoped Pointwise in
  have hsupport {e : ℝ → ℝ≥0∞} (he : ⨆ x, e x = 1) :
      Function.support (fun t ↦ volume {x | .ofReal t ≤ e x}) ⊆ Set.Iic 1 := by
    intro t
    contrapose
    suffices 1 < t → {x | .ofReal t ≤ e x} = ∅ by simp +contextual [this]
    intro ht
    ext x
    suffices e x < .ofReal t by simpa
    grw [le_iSup e, he]
    simpa using ht
  have hnonempty {t : ℝ} (ht : t ∈ Set.Ioo 0 1) {e : ℝ → ℝ≥0∞} (he : ⨆ x, e x = 1) :
      {x | .ofReal t ≤ e x}.Nonempty := by
    have h := not_imp_not.mpr <| le_iSup_iff.mp (he.symm.le) (.ofReal t)
    push Not at h
    obtain ⟨x, hx⟩ := h (by simpa using ht.2)
    exact ⟨x, hx.le⟩
  calc
    _ ≤ .ofReal (1 - a) * (∫⁻ x, f x) + .ofReal a * (∫⁻ x, g x) := by
      convert ENNReal.geom_mean_le_arith_mean2_weighted (1 - a).toNNReal a.toNNReal _ _ ?_
      · simp [ha1]
      · simp [ha0]
      · rw [ENNReal.ofNNReal_toNNReal]
      · rw [ENNReal.ofNNReal_toNNReal]
      · rw [← Real.toNNReal_add (by simp [ha1]) (by simp [ha0]), sub_add_cancel,
          Real.toNNReal_one]
    _ = (∫⁻ t in Set.Ioo 0 1, volume ((1 - a) • {x | .ofReal t ≤ f x})) +
        (∫⁻ t in Set.Ioo 0 1, volume (a • {x | .ofReal t ≤ g x})) := by
      simp_rw [Measure.addHaar_smul_of_nonneg _ ha0,
        Measure.addHaar_smul_of_nonneg _ (sub_nonneg.mpr ha1), Module.finrank_self, pow_one]
      rw [lintegral_eq_lintegral_measure_ofReal_le _ hf.aemeasurable,
        lintegral_eq_lintegral_measure_ofReal_le _ hg.aemeasurable,
        ← setLIntegral_eq_of_support_subset (hsupport hf1), Measure.restrict_restrict (by simp),
        ← setLIntegral_eq_of_support_subset (hsupport hg1), Measure.restrict_restrict (by simp),
        ← lintegral_const_mul' _ _ (by simp), ← lintegral_const_mul' _ _ (by simp)]
      congrm $(setLIntegral_congr ?set) + $(setLIntegral_congr ?set)
      exact (Ioo_ae_eq_Ioc.trans <| by simp [Set.Iic_inter_Ioi]).symm
    _ ≤ ∫⁻ t in Set.Ioo 0 1, volume {x | .ofReal t ≤ j x}  := by
      grw [le_lintegral_add]
      refine setLIntegral_mono' (by simp) fun t ht ↦ ?_
      grw [Real.volume_add_volume_le (hnonempty ht hf1).smul_set (hnonempty ht hg1).smul_set]
      refine measure_mono fun x hx ↦ ?_
      obtain ⟨y, hy, z, hz, rfl⟩ := Set.mem_add.mp hx
      obtain ⟨y', hy', rfl⟩ := Set.mem_smul_set.mp hy
      obtain ⟨z', hz', rfl⟩ := Set.mem_smul_set.mp hz
      simp only [Set.mem_ofPred_eq] at hy' hz' ⊢
      specialize h y' z'
      grw [← hy', ← hz', ← ENNReal.rpow_add_of_nonneg _ _ (by simpa using ha1) ha0,
        sub_add_cancel, ENNReal.rpow_one] at h
      exact h
    _ ≤ _ := by
      rw [lintegral_eq_lintegral_measure_ofReal_le _ hj.aemeasurable]
      exact lintegral_mono_set Set.Ioo_subset_Ioi_self

include ha0 ha1 hf hg hj in
private theorem prekopa_leindler_real_of_iSup_ne_top (hftop : ⨆ x, f x ≠ ∞) (hgtop : ⨆ x, g x ≠ ∞)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) * x + a * y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x := by
  by_cases hf0 : ⨆ x, f x = 0
  · rcases lt_or_eq_of_le ha1 with ha1 | rfl
    · simp [ENNReal.iSup_eq_zero.mp hf0, ha1]
    · have : ∀ x, g x ≤ j x := by simpa using h
      simpa using lintegral_mono this
  by_cases hg0 : ⨆ x, g x = 0
  · rcases lt_or_eq_of_le ha0 with ha0 | rfl
    · simp [ENNReal.iSup_eq_zero.mp hg0, ha0]
    · have : ∀ x, f x ≤ j x := by simpa using h
      simpa using lintegral_mono this
  have hj' : Measurable (j · * ((⨆ x, f x)⁻¹ ^ (1 - a) * (⨆ x, g x)⁻¹ ^ a)) := by fun_prop
  have hf1 : ⨆ x, f x * (⨆ x, f x)⁻¹ = 1 := by
    rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel hf0 hftop]
  have hg1 : ⨆ x, g x * (⨆ x, g x)⁻¹ = 1 := by
    rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel hg0 hgtop]
  have h' (x y) : (f x * (⨆ x, f x)⁻¹) ^ (1 - a) * (g y * (⨆ x, g x)⁻¹) ^ a ≤
      j ((1 - a) * x + a * y) * ((⨆ x, f x)⁻¹ ^ (1 - a) * (⨆ x, g x)⁻¹ ^ a) := by
    grw [← h x y, ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
      ENNReal.mul_rpow_of_nonneg _ _ (by positivity)]
    exact le_of_eq (by ring)
  have h := prekopa_leindler_real_of_iSup_eq_one ha0 ha1 (by fun_prop) (by fun_prop) hj' hf1 hg1 h'
  rw [lintegral_mul_const _ hf, lintegral_mul_const _ hg, lintegral_mul_const _ hj,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity)] at h
  exact (ENNReal.mul_le_mul_iff_left (by aesop) (by finiteness)).mp <| h.trans_eq' (by ring)

include ha0 ha1 hf hg hj in
/-- One-dimensional **Prékopa–Leindler inequality**. -/
theorem _root_.Real.lintegral_rpow_mul_lintegral_rpow_le
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) * x + a * y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x :=
  calc
    _ = (∫⁻ x, ⨆ t : ℕ, min (f x) t) ^ (1 - a) * (∫⁻ x, ⨆ t : ℕ, min (g x) t) ^ a := by
      simp_rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
    _ = (⨆ t : ℕ, (∫⁻ x, min (f x) t) ^ (1 - a)) * ⨆ t : ℕ, (∫⁻ x, min (g x) t) ^ a := by
      congr
      <;> rw [lintegral_iSup (by fun_prop) fun t u h x ↦ by simp [h],
        ENNReal.iSup_rpow_of_nonneg (by grind)]
    _ = ⨆ (s : ℕ) (t : ℕ), (∫⁻ x,  min (f x) t) ^ (1 - a) * (∫⁻ x, min (g x) s) ^ a := by
      simp_rw [ENNReal.mul_iSup, ENNReal.iSup_mul]
    _ ≤ _ := by
      refine iSup₂_le fun s t ↦ ?_
      apply prekopa_leindler_real_of_iSup_ne_top ha0 ha1 (by fun_prop) (by fun_prop) hj
      · exact lt_top_iff_ne_top.mp <| iSup_lt_iff.mpr ⟨t + 1, by simp⟩
      · exact lt_top_iff_ne_top.mp <| iSup_lt_iff.mpr ⟨s + 1, by simp⟩
      · intro x y
        grw [← h x y]
        gcongr <;> simp

include ha0 ha1 in
private theorem lintegral_rpow_mul_lintegral_rpow_le_pi {d : ℕ} {f g j : (Fin d → ℝ) → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hj : Measurable j)
    (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) • x + a • y)) :
    (∫⁻ x, f x) ^ (1 - a) * (∫⁻ x, g x) ^ a ≤ ∫⁻ x, j x := by
  induction d with
  | zero => simpa [lintegral_unique, volume_pi, Unique.eq_default] using h default default
  | succ d ih =>
    calc
      _ = (∫⁻ (x) (y), f (Fin.cons x y)) ^ (1 - a) * (∫⁻ (x) (y), g (Fin.cons x y)) ^ a := by
        simp_rw [volume_pi, (measurePreserving_piFinSuccAbove _ 0).symm.lintegral_map_equiv]
        simp (disch := fun_prop) [lintegral_prod]
      _ ≤ ∫⁻ (x) (y), j (Fin.cons x y) := by
        refine Real.lintegral_rpow_mul_lintegral_rpow_le ha0 ha1 (by fun_prop) (by fun_prop)
          (by fun_prop) fun x y ↦ ?_
        refine ih (by fun_prop) (by fun_prop) (by fun_prop) fun u v ↦ ?_
        convert h (Fin.cons x u) (Fin.cons y v)
        ext i
        cases i using Fin.cases <;> simp
      _ = ∫⁻ x, j x := by
        simp_rw [volume_pi, (measurePreserving_piFinSuccAbove _ 0).symm.lintegral_map_equiv _ _]
        simp (disch := fun_prop) [lintegral_prod]

/-- **Prékopa–Leindler inequality** for real vector space. -/
theorem lintegral_rpow_mul_lintegral_rpow_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) {f g j : E → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hj : Measurable j) (h : ∀ x y, f x ^ (1 - a) * g y ^ a ≤ j ((1 - a) • x + a • y)) :
    (∫⁻ x, f x ∂μ) ^ (1 - a) * (∫⁻ x, g x ∂μ) ^ a ≤ ∫⁻ x, j x ∂μ := by
  let e : (Fin (Module.finrank ℝ E) → ℝ) ≃L[ℝ] E := .ofFinrankEq (by simp)
  obtain ⟨c, _, hc⟩ :=
    e.symm.toLinearMap.exists_map_addHaar_eq_smul_addHaar μ volume e.symm.surjective
  suffices (c * ∫⁻ x, f (e x)) ^ (1 - a) * (c * ∫⁻ x, g (e x)) ^ a ≤ c * ∫⁻ x, j (e x) by
    simp_rw [← smul_eq_mul c, ← lintegral_smul_measure, ← hc] at this
    simpa (disch := fun_prop) [lintegral_map] using this
  calc
    _ = c * ((∫⁻ x, f (e x)) ^ (1 - a) * (∫⁻ x, g (e x)) ^ a) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by simp [ha1]),
        ENNReal.mul_rpow_of_nonneg _ _ ha0, mul_mul_mul_comm,
        ← ENNReal.rpow_add_of_nonneg _ _ (by simp [ha1]) ha0, sub_add_cancel, ENNReal.rpow_one]
    _ ≤ _ :=
      mul_le_mul_right (lintegral_rpow_mul_lintegral_rpow_le_pi ha0 ha1 (by fun_prop) (by fun_prop)
        (by fun_prop) fun x y ↦ by simpa using h (e x) (e y)) _

end MeasureTheory
