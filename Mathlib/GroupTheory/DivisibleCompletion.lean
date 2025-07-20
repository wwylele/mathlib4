import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Order.Archimedean.Class
import Mathlib.Algebra.Order.GroupWithZero.Submonoid
import Mathlib.Algebra.Order.Module.Defs
import Mathlib.RingTheory.Localization.FractionRing


instance : IsLocalization (Submonoid.pos ℤ) ℚ where
  map_units' a := by simpa using ne_of_gt a.prop
  surj' z := by
    obtain ⟨⟨x1, x2⟩, hx⟩ := IsLocalization.surj (nonZeroDivisors ℤ) z
    obtain hx2 | hx2 := lt_or_gt_of_ne (show x2.val ≠ 0 by simp)
    · exact ⟨⟨-x1, ⟨-x2.val, by simpa using hx2⟩⟩, by simpa using hx⟩
    · exact ⟨⟨x1, ⟨x2.val, hx2⟩⟩, hx⟩
  exists_of_eq {x y} h := by
    use 1
    simpa using Rat.intCast_inj.mp h

variable (M : Type*) [AddCommGroup M]
variable [LinearOrder M] [IsOrderedAddMonoid M]

abbrev DivisibleCompletion := LocalizedModule (Submonoid.pos ℤ) M

namespace DivisibleCompletion

instance : LE (DivisibleCompletion M) where
  le x y := LocalizedModule.liftOn₂ x y (fun x y ↦ y.2 • x.1 ≤ x.2 • y.1) fun x1 x2 y1 y2 hx hy ↦ by
    obtain ⟨xc, hxc⟩ := hx
    obtain ⟨yc, hyc⟩ := hy
    change xc.val • y1.2.val • x1.1 = xc.val • x1.2.val • y1.1 at hxc
    change yc.val • y2.2.val • x2.1 = yc.val • x2.2.val • y2.1 at hyc
    obtain hx := (smul_right_inj (ne_of_gt xc.prop)).mp hxc
    obtain hy := (smul_right_inj (ne_of_gt yc.prop)).mp hyc
    suffices x2.2.val • x1.1 ≤ x1.2.val • x2.1 ↔ y2.2.val • y1.1 ≤ y1.2.val • y2.1 by
      simpa using this
    rw [← zsmul_le_zsmul_iff_right (show 0 < y1.2.val * y2.2.val by
      apply mul_pos y1.2.prop y2.2.prop)]
    nth_rw 2 [← zsmul_le_zsmul_iff_right (show 0 < x1.2.val * x2.2.val by
      apply mul_pos x1.2.prop x2.2.prop)]
    simp_rw [← mul_smul]
    rw [show y1.2.val * y2.2.val * x2.2.val = y2.2.val * x2.2.val * y1.2.val by ring]
    rw [show y1.2.val * y2.2.val * x1.2.val = y1.2.val * x1.2.val * y2.2.val by ring]
    rw [show x1.2.val * x2.2.val * y2.2.val = y2.2.val * x2.2.val * x1.2.val by ring]
    rw [show x1.2.val * x2.2.val * y1.2.val = y1.2.val * x1.2.val * x2.2.val by ring]
    rw [mul_smul _ _ x1.1, mul_smul _ _ x2.1, mul_smul _ _ y1.1, mul_smul _ _ y2.1]
    rw [hx, hy]

variable {M} in
abbrev mk (m : M) (s : Submonoid.pos ℤ) : DivisibleCompletion M := LocalizedModule.mk m s

omit [LinearOrder M] [IsOrderedAddMonoid M] in
theorem ind {motive : DivisibleCompletion M → Prop} (mk : ∀ num den, motive (.mk num den)) :
    ∀ x, motive x := by
  apply LocalizedModule.induction_on
  intro a
  apply mk

omit [LinearOrder M] [IsOrderedAddMonoid M] in
variable {M} in
theorem mk_add_mk {m1 m2 : M} {s1 s2 : Submonoid.pos ℤ} :
    mk m1 s1 + mk m2 s2 = mk (s2 • m1 + s1 • m2) (s1 * s2) := LocalizedModule.mk_add_mk

variable {M} in
theorem mk_le_mk {m m' : M} {s s' : Submonoid.pos ℤ} :
    mk m s ≤ mk m' s' ↔ s' • m ≤ s • m' := by rfl

variable {M} in
theorem mk_le_mk_left {m m' : M} {s : Submonoid.pos ℤ} :
    mk m s ≤ mk m' s ↔ m ≤ m' := by
  rw [mk_le_mk]
  change s.val • m ≤ s.val • m' ↔ m ≤ m'
  exact zsmul_le_zsmul_iff_right s.prop

variable {M} in
theorem mk_eq_mk {m m' : M} {s s' : Submonoid.pos ℤ} :
    mk m s = mk m' s' ↔ s' • m = s • m' := by
  rw [LocalizedModule.mk_eq]
  constructor
  · intro ⟨u, h⟩
    change u.val • s' • m = u.val • s • m' at h
    exact (smul_right_inj (ne_of_gt u.prop)).mp h
  · intro hr
    use 1
    rw [hr]

instance : PartialOrder (DivisibleCompletion M) where
  le_refl a := by
    induction a using ind with | mk m s
    rw [mk_le_mk]
  le_trans a b c hab hbc := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    induction c using ind with | mk mc sc
    rw [mk_le_mk] at ⊢ hab hbc
    change sc.val • ma ≤ sa.val • mc
    change sb.val • ma ≤ sa.val • mb at hab
    change sc.val • mb ≤ sb.val • mc at hbc
    rw [← zsmul_le_zsmul_iff_right (show 0 < sb.val from sb.prop)]
    rw [← zsmul_le_zsmul_iff_right (show 0 < sc.val from sc.prop)] at hab
    rw [← zsmul_le_zsmul_iff_right (show 0 < sa.val from sa.prop)] at hbc
    rw [smul_comm _ _ ma, smul_comm _ _ mc]
    rw [smul_comm _ _ mb] at hab
    exact hab.trans hbc
  le_antisymm a b h h' := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    rw [mk_le_mk] at h h'
    rw [mk_eq_mk]
    exact le_antisymm h h'

noncomputable
instance : LinearOrder (DivisibleCompletion M) where
  le_total a b := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    exact le_total _ _
  toDecidableLE := Classical.decRel LE.le

noncomputable
instance : IsOrderedAddMonoid (DivisibleCompletion M) where
  add_le_add_left a b h c := by
    induction a using ind with | mk ma sa
    induction b using ind with | mk mb sb
    induction c using ind with | mk mc sc
    rw [mk_le_mk] at h
    simp_rw [mk_add_mk, mk_le_mk, smul_add, ← mul_smul]
    rw [mul_right_comm sc sa sb, add_le_add_iff_left]
    rw [mul_right_comm sc sa sc, mul_right_comm sc sb sc]
    rw [mul_smul _ _ ma, mul_smul _ _ mb]
    exact zsmul_le_zsmul_right (le_of_lt (sc * sc).prop) h

variable {M} in
omit [LinearOrder M] [IsOrderedAddMonoid M] in
theorem qsmul_mk (a : ℚ) (m : M) (s : Submonoid.pos ℤ) :
    a • mk m s = mk (a.num • m) (⟨a.den, Int.natCast_pos.mpr a.den_pos⟩ * s) := by
  convert LocalizedModule.mk'_smul_mk ℚ a.num m ⟨a.den, Int.natCast_pos.mpr a.den_pos⟩ s
  rw [IsLocalization.eq_mk'_iff_mul_eq]
  simp

variable {M} in
omit [LinearOrder M] [IsOrderedAddMonoid M] in
theorem zsmul_mk (a : ℤ) (m : M) (s : Submonoid.pos ℤ) : a • mk m s = mk (a • m) s := by
  suffices (a : ℚ) • mk m s = mk (a • m) s by
    rw [Int.cast_smul_eq_zsmul] at this
    exact this
  rw [qsmul_mk]
  exact congrArg _ <| Subtype.eq (by simp)

variable {M} in
omit [LinearOrder M] [IsOrderedAddMonoid M] in
theorem nsmul_mk (a : ℕ) (m : M) (s : Submonoid.pos ℤ) : a • mk m s = mk (a • m) s := by
  suffices (a : ℤ) • mk m s = mk ((a : ℤ) • m) s by simpa using this
  exact zsmul_mk _ _ _

noncomputable
instance : PosSMulStrictMono ℚ (DivisibleCompletion M) where
  elim a ha b c h := by
    induction b using ind with | mk mb sb
    induction c using ind with | mk mc sc
    contrapose! h
    simp_rw [qsmul_mk, mk_le_mk] at h
    change (a.den * sb.val) • a.num • mc ≤ (a.den * sc.val) • a.num • mb at h
    simp_rw [← mul_smul, mul_right_comm _ _ a.num, mul_smul _ _ mc, mul_smul _ _ mb] at h
    rw [mk_le_mk]
    refine (zsmul_le_zsmul_iff_right ?_).mp h
    exact mul_pos (Int.natCast_pos.mpr a.den_pos) (Rat.num_pos.mpr ha)

noncomputable
def orderAddMonoidHom : M →+o DivisibleCompletion M where
  __ := LocalizedModule.mkLinearMap _ _
  map_zero' := by simp
  monotone' := by
    intro a b h
    suffices mk a 1 ≤ mk b 1 by simpa using this
    rw [mk_le_mk]
    simpa using h

@[simp]
theorem orderAddMonoidHom_apply (a : M) :
    (orderAddMonoidHom M) a = mk a 1 := by rfl

theorem orderAddMonoidHom_injective : Function.Injective (orderAddMonoidHom M) := by
  intro a b
  simp [mk_eq_mk]

variable {M} in
omit [LinearOrder M] [IsOrderedAddMonoid M] in
theorem mk_neg (m : M) (s : Submonoid.pos ℤ) : mk (-m) s = -mk m s := LocalizedModule.mk_neg

variable {M} in
theorem mk_max (m1 m2 : M) (s : Submonoid.pos ℤ) : mk (max m1 m2) s = max (mk m1 s) (mk m2 s) := by
  obtain h | h := le_total m1 m2
  all_goals simpa [h] using mk_le_mk_left.mpr h

variable {M} in
theorem mk_min (m1 m2 : M) (s : Submonoid.pos ℤ) : mk (min m1 m2) s = min (mk m1 s) (mk m2 s) := by
  obtain h | h := le_total m1 m2
  all_goals simpa [h] using mk_le_mk_left.mpr h

variable {M} in
theorem mk_abs (m : M) (s : Submonoid.pos ℤ) : mk |m| s = |mk m s| := by
  simp_rw [abs, mk_max, mk_neg]

noncomputable
def archimedeanClassOrderHom :
    ArchimedeanClass M →o ArchimedeanClass (DivisibleCompletion M) :=
  ArchimedeanClass.orderHom (orderAddMonoidHom M)

theorem archimedeanClassOrderHom_injective : Function.Injective (archimedeanClassOrderHom M) :=
  ArchimedeanClass.orderHom_injective (orderAddMonoidHom_injective M)

theorem archimedeanClassOrderHom_surjective : Function.Surjective (archimedeanClassOrderHom M) := by
  intro A
  induction A using ArchimedeanClass.ind with | mk a
  induction a using ind with | mk m s
  use ArchimedeanClass.mk m
  suffices ArchimedeanClass.mk (mk m 1) = ArchimedeanClass.mk (mk m s) by
    simpa using this
  rw [ArchimedeanClass.mk_eq_mk]
  have hsmul (m : M) : s • m = s.val.toNat • m := by
    suffices (s.val : ℤ) • m = (s.val.toNat : ℤ) • m by
      rw [natCast_zsmul] at this
      simpa using this
    congr
    simpa using le_of_lt s.prop
  simp_rw [← mk_abs, nsmul_mk, mk_le_mk, hsmul]
  refine ⟨⟨1, ?_⟩, ⟨s.val.toNat, by simp⟩⟩
  simpa using le_self_nsmul (by simp) (Int.toNat_eq_zero.not.mpr <| not_le.mpr s.prop)

end DivisibleCompletion
