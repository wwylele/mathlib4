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

/-!

-/

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

abbrev V : Set D := (fun v ↦ v * v) ⁻¹' (algebraMap ℝ D '' (Set.Iic 0))

theorem sqr (x : D) (h : x * x ∈ (algebraMap ℝ D).range) :
    x ∈ (algebraMap ℝ D).range ∨ x ∈ V D := by
  obtain ⟨y, hy⟩ := h
  obtain hneg | hpos := le_total y 0
  · right
    use y
    aesop
  · left
    --use Real.sqrt y

    sorry

theorem symm_in {x y : D} (hx : x ∈ V D) (hy : y ∈ V D) :
    x * y + y * x ∈ (algebraMap ℝ D).range := by

  sorry

theorem frobenius_theorem :
    Nonempty (D ≃ₐ[ℝ] ℝ) ∨ Nonempty (D ≃ₐ[ℝ] ℂ) ∨ Nonempty (D ≃ₐ[ℝ] ℍ[ℝ]) := by


  sorry
