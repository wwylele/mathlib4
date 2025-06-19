/-
Copyright (c) 2025 Weiyi Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Weiyi Wang
-/

import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Algebra.Module.Submodule.Order
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.DFinsupp

/-!
# Further lemmas related to Archimedean classes for ordered module.

## Main definitions
* `ArchimedeanSubgroup.submodule`: `ArchimedeanSubgroup` as a submodule.
* `ArchimedeanGrade`: a submodule consisting of arbitrarily chosen representatives from
  the specified `ArchimedeanClass` of the module.
-/

section ToMove

theorem Submodule.exists_isCompl'
    {K : Type*} {V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    {p q : Submodule K V} (h : p ≤ q) :
    ∃ r : Submodule K V, p ⊓ r = ⊥ ∧ p ⊔ r = q := by
  obtain ⟨r, hr⟩ := Submodule.exists_isCompl (Submodule.comap q.subtype p)
  have : p = Submodule.map q.subtype (Submodule.comap q.subtype p) :=
    (Submodule.map_comap_eq_self (by simpa using h)).symm
  rw [this]
  refine ⟨Submodule.map q.subtype r, ?_, ?_⟩
  · rw [← Submodule.map_inf _ q.injective_subtype, hr.inf_eq_bot]
    simp
  · rw [← Submodule.map_sup, hr.sup_eq_top]
    simp


variable {M : Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable {K : Type*} [Ring K] [LinearOrder K] [IsOrderedRing K]
variable [Module K M] [PosSMulMono K M]

lemma abs_smul (k : K) (a : M) : |k • a| = |k| • |a| := by
  obtain ha | ha := le_total a 0 <;> obtain hq | hq := le_total k 0 <;>
    simp [*, abs_of_nonneg, abs_of_nonpos, smul_nonneg, smul_nonpos_of_nonneg_of_nonpos,
      smul_nonpos_of_nonpos_of_nonneg, smul_nonneg_of_nonpos_of_nonpos]

end ToMove

variable {M : Type*}
variable [AddCommGroup M] [LinearOrder M] [IsOrderedAddMonoid M]

variable (K : Type*) [DivisionRing K] [LinearOrder K] [IsOrderedRing K] [Archimedean K]
variable [Module K M] [PosSMulMono K M]

/-- For a ordered module with `Archimedean` scalar field, `ArchimedeanSubgroup`
 is also a submodule. -/
noncomputable
def ArchimedeanSubgroup.submodule (s : UpperSet (ArchimedeanClass M)) : Submodule K M where
  __ := ArchimedeanSubgroup s
  smul_mem' k {a} := by
    obtain rfl | hs := eq_or_ne s ⊤
    · suffices a = 0 → k • a = 0 by simpa using this
      intro ha
      simp [ha]
    · show a ∈ ArchimedeanSubgroup s → k • a ∈ ArchimedeanSubgroup s
      simp_rw [mem_iff_of_ne_top hs]
      intro ha
      obtain ⟨n, hn⟩ := Archimedean.arch |k| (show 0 < 1 by simp only [zero_lt_one])
      refine s.upper (ArchimedeanClass.mk_le_mk.mpr ⟨n, ?_⟩) ha
      have : n • |a| = (n • (1 : K)) • |a| := by rw [smul_assoc, one_smul]
      rw [this, abs_smul]
      exact smul_le_smul_of_nonneg_right hn (by simp)

variable (M) in
@[simp]
theorem ArchimedeanSubgroup.submodule_eq_bot:
    ArchimedeanSubgroup.submodule K (M := M) ⊤ = ⊥ := by
  rw [Submodule.eq_bot_iff]
  show ∀ x ∈ ArchimedeanSubgroup ⊤, x = 0
  simp

variable (M) in
@[simp]
theorem ArchimedeanSubgroup.submodule_eq_bot_of_Ici_top:
    ArchimedeanSubgroup.submodule K (M := M) (UpperSet.Ici ⊤) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  show ∀ x ∈ ArchimedeanSubgroup (UpperSet.Ici ⊤), x = 0
  simp

theorem ArchimedeanSubgroup.exist_compl_of_le {s t : UpperSet (ArchimedeanClass M)} (hst : s ≤ t) :
    ∃ A : Submodule K M, (submodule K t) ⊓ A = ⊥ ∧ submodule K t ⊔ A = submodule K s :=
  Submodule.exists_isCompl' (le_of_le hst)

variable (M) in
theorem ArchimedeanSubgroup.submodule_strictAntiOn :
    StrictAntiOn (ArchimedeanSubgroup.submodule (M := M) K) (Set.Iio ⊤) := by
  intro x hx y hy hxy
  exact ArchimedeanSubgroup.strictAntiOn M hx hy hxy

variable (M) in
theorem ArchimedeanSubgroup.submodule_antitone :
    Antitone (ArchimedeanSubgroup.submodule (M := M) K):= by
  intro x y hxy
  exact ArchimedeanSubgroup.antitone M hxy

/-- For a `A : ArchimedeanClass M`, arbitrarily choose a submodule `S` such that
* `submodule K (UpperSet.Ioi A) ⊓ S = ⊥`.
* `submodule K (UpperSet.Ioi A) ⊔ S = submodule K (UpperSet.Ici A)`.
This produces a family of disjoint submodules,
of which each is `Archimedean` and corresponds to a `ArchimedeanClass M`.

By convention, `ArchimedeanGrade ⊤ = ⊥`. -/
noncomputable
def ArchimedeanGrade (A : ArchimedeanClass M) :=
  (ArchimedeanSubgroup.exist_compl_of_le K (UpperSet.Ici_le_Ioi A)).choose

namespace ArchimedeanGrade

theorem inf_eq (A : ArchimedeanClass M) :
    (ArchimedeanSubgroup.submodule K (UpperSet.Ioi A)) ⊓ ArchimedeanGrade K A = ⊥ :=
  (ArchimedeanSubgroup.exist_compl_of_le K (UpperSet.Ici_le_Ioi A)).choose_spec.1

theorem sup_eq (A : ArchimedeanClass M) :
    (ArchimedeanSubgroup.submodule K (UpperSet.Ioi A)) ⊔ ArchimedeanGrade K A =
    (ArchimedeanSubgroup.submodule K (UpperSet.Ici A)) :=
  (ArchimedeanSubgroup.exist_compl_of_le K (UpperSet.Ici_le_Ioi A)).choose_spec.2

variable (M) in
@[simp]
theorem eq_bot_of_top : ArchimedeanGrade K (⊤ : ArchimedeanClass M) = ⊥ := by
  obtain hsup := sup_eq K (⊤ : ArchimedeanClass M)
  simpa using hsup

theorem nontrivial_of_ne_top {A : ArchimedeanClass M} (h : A ≠ ⊤) :
    Nontrivial (ArchimedeanGrade K A) := by
  obtain hcodisj := sup_eq K A
  contrapose! hcodisj with htrivial
  have hbot : ArchimedeanGrade K A = ⊥ := by
    simpa using Submodule.nontrivial_iff_ne_bot.not.mp htrivial
  have hA : UpperSet.Ioi A ∈ Set.Iio ⊤ := by
    suffices UpperSet.Ioi A < ⊤ by simpa using this
    refine Ne.lt_top (UpperSet.ext_iff.ne.mpr ?_)
    simpa using h
  rw [hbot, sup_bot_eq]
  rw [((ArchimedeanSubgroup.submodule_strictAntiOn M K).eq_iff_eq hA (by simp)).ne]
  rw [UpperSet.ext_iff.ne]
  by_contra!
  have h : Set.Ici A = Set.Ioi A := this
  have h' : A ∈ Set.Ici A := Set.left_mem_Ici
  rw [h] at h'
  simp at h'

theorem le_Ici (A : ArchimedeanClass M) :
    ArchimedeanGrade K A ≤ (ArchimedeanSubgroup.submodule K (UpperSet.Ici A)) := by
  rw [← sup_eq K A]
  simp

theorem class_eq_of_mem {A : ArchimedeanClass M} {a : M}
    (ha : a ∈ ArchimedeanGrade K A) (h0 : a ≠ 0) : ArchimedeanClass.mk a = A := by
  apply le_antisymm
  · have hA : (UpperSet.Ioi A) ≠ ⊤ := by
      contrapose! h0
      have : A = ⊤ := IsMax.eq_top (Set.Ioi_eq_empty_iff.mp (UpperSet.ext_iff.mp h0))
      rw [this, eq_bot_of_top] at ha
      exact (Submodule.mem_bot _).mp ha
    contrapose! h0 with hlt
    have ha' : a ∈ ArchimedeanSubgroup.submodule K (UpperSet.Ioi A) :=
      (ArchimedeanSubgroup.mem_iff_of_ne_top hA).mpr hlt
    exact (Submodule.disjoint_def.mp (disjoint_iff.mpr (inf_eq K A))) a ha' ha
  · apply (ArchimedeanSubgroup.mem_iff_of_ne_top (show (UpperSet.Ici A) ≠ ⊤ by simp)).mp
    exact Set.mem_of_subset_of_mem (le_Ici K A) ha

instance (A : ArchimedeanClass M) : Archimedean (ArchimedeanGrade K A) := by
  apply ArchimedeanClass.archimedean_of_mk_eq_mk
  intro a ha b hb
  suffices ArchimedeanClass.mk a.val = ArchimedeanClass.mk b.val by
    rw [ArchimedeanClass.mk_eq_mk] at this ⊢
    exact this
  rw [class_eq_of_mem K a.prop (by simpa using ha)]
  rw [class_eq_of_mem K b.prop (by simpa using hb)]

variable (M) in
theorem iSupIndep : iSupIndep (ArchimedeanGrade (M := M) K ·) := by
  rw [iSupIndep_def]
  intro A
  rw [Submodule.disjoint_def']
  intro a ha b hb hab
  obtain ⟨f, hf⟩ := (Submodule.mem_iSup_iff_exists_dfinsupp' _ b).mp hb
  obtain hf' := congrArg ArchimedeanClass.mk hf
  contrapose! hf' with h0
  rw [← hab, DFinsupp.sum]
  by_cases hnonempty : f.support.Nonempty
  · have hmem (x : ArchimedeanClass M) : (f x).val ∈ ArchimedeanGrade K x :=
      Set.mem_of_mem_of_subset (f x).prop (by simp)
    have hmono : StrictMonoOn (fun i ↦ ArchimedeanClass.mk (f i).val) f.support := by
      intro x hx y hy hxy
      show ArchimedeanClass.mk (f x).val < ArchimedeanClass.mk (f y).val
      rw [class_eq_of_mem K (hmem x) (by simpa using hx)]
      rw [class_eq_of_mem K (hmem y) (by simpa using hy)]
      exact hxy
    rw [ArchimedeanClass.mk_sum hnonempty hmono]
    rw [class_eq_of_mem K (hmem _) (by simpa using Finset.min'_mem f.support hnonempty)]
    by_contra!
    obtain h := this ▸ Finset.min'_mem f.support hnonempty
    contrapose! h
    rw [DFinsupp.mem_support_toFun, not_ne_iff, class_eq_of_mem K ha h0]
    simpa using (f A).prop
  · have : f.support = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnonempty
    rw [this]
    symm
    simpa using h0

end ArchimedeanGrade
