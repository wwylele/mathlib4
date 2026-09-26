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
    (t.ninePointCircle.radius + (if signs = ∅ then -1 else 1) * t.exradius signs) ^ 2 := by

  calc
    _ = (∑ i, w t signs i * dist (t.points i) (ninePointCircle t).center ^ 2) /
        ∑ i, w t signs i +
        (if signs = ∅ then -1 else 1) * 2 * t.circumradius * t.exradius signs := by
      simp_rw [t.dist_excenter_sq _ hsigns, t.excenterWeights_eq_excenterWeightsFace_div,
        ← mul_div_right_comm, ← Finset.sum_div]
    _ = (w t signs 0 * dist (t.points 0) (ninePointCircle t).center ^ 2 +
        w t signs 1 * dist (t.points 1) (ninePointCircle t).center ^ 2 +
        w t signs 2 * dist (t.points 2) (ninePointCircle t).center ^ 2) /
        ∑ i, w t signs i +
        (if signs = ∅ then -1 else 1) * 2 * t.circumradius * t.exradius signs := by
      congrm ?_ / _ + _
      have : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by grind
      simp [this]
      ring
    _ = (w t signs 0 * (t.circumradius ^ 2 + dist (t.points 0) (t.points 1) ^ 2 +
          dist (t.points 0) (t.points 2) ^ 2 - dist (t.points 1) (t.points 2) ^ 2) / 4 +
        w t signs 1 * (t.circumradius ^ 2 + dist (t.points 0) (t.points 1) ^ 2 +
          dist (t.points 1) (t.points 2) ^ 2 - dist (t.points 0) (t.points 2) ^ 2) / 4 +
        w t signs 2 * (t.circumradius ^ 2 + dist (t.points 1) (t.points 2) ^ 2 +
          dist (t.points 0) (t.points 1) ^ 2 - dist (t.points 0) (t.points 2) ^ 2) / 4) /
        ∑ i, w t signs i +
        (if signs = ∅ then -1 else 1) * 2 * t.circumradius * t.exradius signs := by
      rw [t.dist_ninePointCircle_center_sq (i₁ := 0) (i₂ := 1) (i₃ := 2)]
      sorry
    _ = _ := sorry

end Affine.Triangle
