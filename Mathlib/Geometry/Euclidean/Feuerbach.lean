module

public import Mathlib.Geometry.Euclidean.NinePointCircle
public import Mathlib.Geometry.Euclidean.Incenter

import Mathlib.Geometry.Euclidean.Volume.Triangle

/-!

-/
public section

namespace Affine.Triangle

open Simplex EuclideanGeometry Real

variable {V P : Type*}
variable [NormedAddCommGroup V] [InnerProductSpace ℝ V] [MetricSpace P] [NormedAddTorsor V P]
variable (t : Triangle ℝ P) {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)

local notation "w" => excenterWeightsFace

private theorem dist_excenter_ninePointCircle_center_sq {signs : Finset (Fin 3)}
    (hsigns : signs = ∅ ∨ signs = {0} ∨ signs = {1} ∨ signs = {2}) :
    dist (t.excenter signs) t.ninePointCircle.center ^ 2 =
    (t.ninePointCircle.radius - (if signs = ∅ then 1 else -1) * t.exradius signs) ^ 2 := by

  calc
    _ = sorry := by
      simp_rw [t.excenter_eq_affineCombination, dist_affineCombination_const_sq _ _
        (t.sum_excenterWeights_eq_one_iff.mpr (t.excenterExists _)),
        t.excenterWeights_eq_excenterWeightsFace_div]
      sorry
    _ = _ := sorry

end Affine.Triangle
