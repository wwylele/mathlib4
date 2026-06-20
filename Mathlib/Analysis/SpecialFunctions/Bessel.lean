module

public import Mathlib

public section

theorem FormalMultilinearSeries.deriv_sum
    {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    [CompleteSpace F]
    {f : FormalMultilinearSeries 𝕜 𝕜 F} {x : 𝕜} (h : ‖x‖ₑ < f.radius) :
    deriv f.sum x = f.derivSeries.sum x 1 := by
  rw [deriv, FormalMultilinearSeries.fderiv_sum h]


namespace Complex

open scoped Nat Real
open Topology Filter

noncomputable def besselJSeries (a : ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  .ofScalars ℂ fun n ↦ (-1) ^ n / (n ! * Gamma (a + 1 + n))

@[simp]
theorem radius_besselJSeries (a : ℂ) : (besselJSeries a).radius = ⊤ := by
  apply FormalMultilinearSeries.ofScalars_radius_eq_top_of_tendsto
  · rw [Filter.eventually_atTop]
    use ⌈-a.re⌉₊
    intro n hn
    suffices Gamma (a + 1 + n) ≠ 0 by simpa [Nat.factorial_ne_zero]
    apply Gamma_ne_zero_of_re_pos
    simp only [add_re, one_re, natCast_re]
    rify at hn
    linarith [Nat.le_ceil (-a.re)]
  · simp_rw [Nat.succ_eq_add_one, norm_div, norm_pow, norm_neg, norm_one, one_pow]
    simp_rw [div_div_div_cancel_left' _ _ (show (1 : ℝ) ≠ 0 by simp)]
    simp_rw [← norm_div, mul_div_mul_comm, Nat.factorial_succ,  Nat.cast_mul,
      Nat.cast_add, ← add_assoc,
      fun (n : ℕ) ↦ div_mul_cancel_right₀ (show n ! ≠ (0 : ℂ) by simpa using n.factorial_ne_zero)]
    simp_rw [norm_mul, norm_inv]
    rw [show 𝓝 (0 : ℝ) = 𝓝 (0 * 0) by simp]
    apply Filter.Tendsto.mul
    · apply Filter.Tendsto.inv_tendsto_atTop
      rw [Filter.tendsto_atTop_atTop]
      intro x
      use ⌈x⌉₊
      intro n hn
      norm_cast
      rw [Nat.ceil_le] at hn
      exact hn.trans (by simp)
    · norm_cast
      have : (fun (n : ℕ) ↦ ‖Gamma (a + 1 + n) / Gamma (a + 1 + n + 1)‖) =ᶠ[atTop]
          (fun (n : ℕ) ↦ ‖(a + 1 + n : ℂ)‖⁻¹) := by
        filter_upwards [eventually_ge_atTop ⌈-a.re⌉₊]
        intro n hn
        have h : 0 < a.re + 1 + n := by
          rw [Nat.ceil_le] at hn
          linarith
        rw [Gamma_add_one _ (Complex.ne_zero_of_re_pos (by simpa using h))]
        rw [div_mul_cancel_right₀ (Gamma_ne_zero_of_re_pos (by simpa using h)), norm_inv]
      apply Filter.Tendsto.congr' this.symm
      apply Filter.Tendsto.inv_tendsto_atTop
      rw [Filter.tendsto_atTop_atTop]
      intro x
      use ⌈x - a.re - 1⌉₊
      intro n hn
      refine le_trans ?_ (Complex.re_le_norm _)
      simp only [add_re, one_re, natCast_re]
      rw [Nat.ceil_le] at hn
      linarith

noncomputable def besselJ (a x : ℂ) := (x / 2) ^ a * (besselJSeries a).sum ((x / 2) ^ 2)

local notation "J" => besselJ

theorem besselJ_int_neg (a : ℤ) (x : ℂ) :
    J a (-x) = (-1) ^ a * J a x := by
  unfold besselJ
  simp_rw [cpow_intCast, neg_div, neg_sq, ← mul_assoc, ← mul_zpow, neg_one_mul]

@[fun_prop]
theorem analyticAt_besselJ_right (a x : ℂ) :
    AnalyticAt ℂ (fun x ↦ (besselJSeries a).sum ((x / 2) ^ 2)) x := by
  let f := fun (x : ℂ) ↦ (x / 2) ^ 2
  have h1 := ((besselJSeries a).hasFPowerSeriesOnBall (by simp)).analyticAt_of_mem
    (by simp : f x ∈ _)
  exact AnalyticAt.comp h1 (by fun_prop)

@[fun_prop]
theorem analyticAt_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    AnalyticAt ℂ (J a) x := by
  refine AnalyticAt.mul ?_ (analyticAt_besselJ_right a x)
  apply AnalyticAt.cpow
  · fun_prop
  · fun_prop
  · simpa [slitPlane] using h

theorem besselJ_neg_int (a : ℤ) (x : ℂ) : J (-a) x = (-1) ^ a * J a x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    simp only [Int.cast_neg, neg_neg, zpow_neg] at this
    rw [this, ← mul_assoc, mul_inv_cancel₀ (zpow_ne_zero _ (by simp)), one_mul]
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  push_cast
  unfold besselJ FormalMultilinearSeries.sum
  conv_lhs =>
    rw [← Summable.sum_add_tsum_nat_add a ((besselJSeries (-a)).summable (by simp))]
  simp_rw [mul_add, ← tsum_mul_left]
  have : ∑ n ∈ Finset.range a, besselJSeries (-a) n (fun _ ↦ (x / 2) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun n hn ↦ ?_
    suffices Gamma (-a + 1 + n) = 0 by simp [besselJSeries, this]
    rw [Gamma_eq_zero_iff]
    use a - (n + 1)
    rw [Finset.mem_range, ← Nat.add_one_le_iff] at hn
    push_cast [hn]
    ring
  rw [this, mul_zero, zero_add]
  refine tsum_congr fun n ↦ ?_
  have h1 : (x / 2) ^ (-a : ℂ) = (x / 2) ^ (-a : ℤ) := by
    norm_cast
  have h2 : Gamma (a + 1 + n) = (n + a)! := by
    rw [← Gamma_nat_eq_factorial]
    congrm Gamma ?_
    push_cast
    ring
  have h3 : Gamma (-a + 1 + (n + a)) = n ! := by
    rw [← Gamma_nat_eq_factorial]
    congrm Gamma ?_
    ring
  simp [h1, h2, h3, besselJSeries, pow_add, pow_right_comm _ 2, field]

theorem besselJ_neg_one (x : ℂ) : J (-1) x = -J 1 x := by
  simpa using besselJ_neg_int 1 x

theorem besselJ_neg_comm (a : ℤ) (x : ℂ) : J (-a) x = J a (-x) := by
  rw [besselJ_neg_int, ← besselJ_int_neg]

@[fun_prop]
theorem analyticAt_besselJ_int (a : ℤ) (x : ℂ) : AnalyticAt ℂ (J a) x := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) x (by simpa using ha.le)
    convert! AnalyticAt.mul (analyticAt_const (v := ((-1) ^ a)⁻¹)) this
    ext x
    simp [besselJ_neg_int, ← mul_assoc,
      inv_mul_cancel₀ (zpow_ne_zero a (show (-1 ≠ (0 : ℂ)) by simp))]
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  refine AnalyticAt.mul ?_ (analyticAt_besselJ_right a x)
  norm_cast
  fun_prop

@[simp]
theorem besselJ_zero (a : ℂ) : J a 0 = if a = 0 then 1 else 0 := by
  unfold besselJ
  split_ifs with ha
  · convert_to 1 * 1 = (1 : ℂ) using 2
    · simp [ha]
    · rw [besselJSeries, ← FormalMultilinearSeries.ofScalarsSum]
      simp [ha]
    · simp
  · convert_to 0 * _ = (0 : ℂ) using 2
    · simp [ha]
    · simp

-- By aristotle
theorem ContinuousLinearMap.tsum_apply {f : ℕ → ℂ →L[ℂ] ℂ} (hf : Summable f) (x : ℂ) :
    (∑' n, f n) x = ∑' n, f n x :=
  (ContinuousLinearMap.apply ℂ ℂ x).map_tsum hf

theorem mul_deriv_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    x * deriv (J a) x = a * J a x - x * J (a + 1) x := by
  have hx0 : x ≠ 0 := fun h ↦ by simp_all
  have hx2 : x / 2 ≠ 0 := fun h ↦ by simp_all
  unfold besselJ
  have hdiff : DifferentiableAt ℂ (fun x ↦ (x / 2) ^ a) x := by
    apply DifferentiableAt.cpow
    · fun_prop
    · fun_prop
    · simpa [slitPlane] using h
  rw [deriv_fun_mul hdiff (analyticAt_besselJ_right a x).differentiableAt]
  rw [sub_eq_add_neg, ← mul_assoc, mul_add, ← mul_neg]
  congrm ?_ + _ * ?_
  · rw [_root_.deriv_cpow_const (by fun_prop) (by simpa [slitPlane] using h)]
    rw [deriv_div_const, deriv_id'', cpow_sub _ _ hx2, cpow_one]
    field
  · rw [cpow_add _ _ hx2, cpow_one, mul_assoc, ← mul_neg]
    congr
    change deriv (a.besselJSeries.sum ∘ fun x ↦ ((x / 2) ^ 2)) x =
      -(x / 2 * (a + 1).besselJSeries.sum ((x / 2) ^ 2))
    rw [deriv_comp _ ((((besselJSeries a).hasFPowerSeriesOnBall (by simp)).analyticAt_of_mem
      (by simp)).differentiableAt) (by fun_prop)]
    rw [FormalMultilinearSeries.deriv_sum (by simp)]
    rw [deriv_fun_pow (by fun_prop), deriv_div_const, deriv_id'']
    rw [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, one_div]
    suffices (a.besselJSeries.derivSeries.sum ((x / 2) ^ 2)) 1 =
        -(a + 1).besselJSeries.sum ((x / 2) ^ 2) by
      rw [this]
      field
    unfold FormalMultilinearSeries.sum
    rw [ContinuousLinearMap.tsum_apply (FormalMultilinearSeries.summable _ (by
      rw [Metric.mem_eball, edist_zero_right]
      apply lt_of_lt_of_le (by simp) (FormalMultilinearSeries.radius_le_radius_derivSeries _)
    ))]
    rw [← tsum_neg]
    refine tsum_congr fun n ↦ ?_
    have h : a + 1 + (n + 1) = a + 1 + 1 + n := by ring
    simp [besselJSeries, pow_add, Nat.factorial_succ, h, field]

theorem mul_deriv_besselJ_int (a : ℤ) (x : ℂ) :
    x * deriv (J a) x = a * J a x - x * J (a + 1) x := by
  by_cases h : x ∈ slitPlane
  · exact mul_deriv_besselJ a h
  by_cases h0 : x = 0
  · simp [h0]
    norm_cast
    grind
  have h : -x ∈ slitPlane := by
    rw [Complex.ext_iff] at h0
    simp_all [slitPlane]
    grind
  have hderiv := mul_deriv_besselJ a h
  norm_cast at hderiv
  rw [neg_mul, ← mul_neg, ← deriv_comp_neg] at hderiv
  simp_rw [besselJ_int_neg] at hderiv
  rw [deriv_const_mul _ (analyticAt_besselJ_int a x).differentiableAt] at hderiv
  rw [zpow_add₀ (by simp), zpow_one] at hderiv
  rw [← mul_left_inj' (show (-1) ^ a ≠ (0 : ℂ) from zpow_ne_zero a (by simp))]
  push_cast at hderiv
  linear_combination hderiv

theorem besselJ_recurrence (a : ℂ) (x : ℂ) :
    2 * a * J a x = x * J (a - 1) x + x * J (a + 1) x := by
  by_cases h : x = 0
  · simp [h]
  have hx2 : x / 2 ≠ 0 := by simpa using h
  by_cases ha : a = 0
  · simp [ha, besselJ_neg_one]
  unfold besselJ FormalMultilinearSeries.sum
  simp_rw [← mul_assoc]
  conv_lhs =>
    rw [Summable.tsum_eq_zero_add ((besselJSeries a).summable (by simp))]
    rw [mul_add, ← tsum_mul_left]
  conv_rhs =>
    rw [Summable.tsum_eq_zero_add ((besselJSeries (a - 1)).summable (by simp))]
    rw [mul_add, ← tsum_mul_left, ← tsum_mul_left, add_assoc]
    rw [← Summable.tsum_add (by
      apply Summable.mul_left
      exact ((besselJSeries (a - 1)).summable (by simp)).comp_injective (add_left_injective _)
    ) (((besselJSeries (a + 1)).summable (by simp)).mul_left _)]
  congrm ?_ + ∑' n, ?_
  · simp [besselJSeries, Gamma_add_one _ ha, cpow_sub _ _ hx2, field]
  have h1 : Gamma (a + 1 + 1 + n) = Gamma (a + (n + 1) + 1) := by
    ring_nf
  have h2 : Gamma (a + 1 + (n + 1)) = Gamma (a + (n + 1) + 1) := by
    ring_nf
  by_cases han : a + (n + 1) = 0
  · have ha : n + 1 = -a := by linear_combination han
    simp [h1, besselJSeries,Nat.factorial_succ, pow_add, pow_right_comm _ 2, cpow_sub _ _ hx2,
      cpow_add _ _ hx2, ha, field]
  simp [h1, h2, besselJSeries, Nat.factorial_succ, pow_add, pow_right_comm _ 2, cpow_sub _ _ hx2,
    cpow_add _ _ hx2, Gamma_add_one _ han, field]
  ring -- why?

theorem two_mul_deriv_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    2 * deriv (J a) x = J (a - 1) x - J (a + 1) x := by
  have hx0 : x ≠ 0 := fun hx0 ↦ by simp [hx0] at h
  rw [← mul_right_inj' hx0, mul_left_comm x 2, mul_deriv_besselJ a h, mul_sub, ← mul_assoc 2,
    besselJ_recurrence]
  ring

theorem deriv_besselJ (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    deriv (J a) x = 2⁻¹ * J (a - 1) x - 2⁻¹ * J (a + 1) x := by
  rw [← mul_right_inj' (show 2 ≠ (0 : ℂ) by simp), two_mul_deriv_besselJ a h]
  ring

theorem two_mul_deriv_besselJ_int (a : ℤ) (x : ℂ) :
    2 * deriv (J a) x = J (a - 1) x - J (a + 1) x := by
  wlog! hx0 : x ≠ 0
  · suffices (fun _ ↦ 2) * deriv (J a) =ᶠ[𝓝 0] J (a - 1 : ℤ) - J (a + 1 : ℤ) by
      simpa [hx0] using this.eq_of_nhds
    rw [← ContinuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      (AnalyticAt.continuousAt (𝕜 := ℂ) (by fun_prop))
      (AnalyticAt.continuousAt (𝕜 := ℂ) (by fun_prop))]
    apply eventuallyEq_nhdsWithin_of_eqOn fun x hx ↦ ?_
    specialize this a x (by simpa using hx)
    simpa using this
  rw [← mul_right_inj' hx0, mul_left_comm x 2, mul_deriv_besselJ_int a x, mul_sub, ← mul_assoc 2,
    besselJ_recurrence]
  ring

theorem deriv_besselJ_int (a : ℤ) (x : ℂ) :
    deriv (J a) x = 2⁻¹ * J (a - 1) x - 2⁻¹ * J (a + 1) x := by
  rw [← mul_right_inj' (show 2 ≠ (0 : ℂ) by simp), two_mul_deriv_besselJ_int a x]
  ring

theorem besselJ_equation (a : ℂ) {x : ℂ} (h : x ∈ slitPlane) :
    x ^ 2 * deriv (deriv (J a)) x + x * deriv (J a) x + (x ^ 2 - a ^ 2) * J a x = 0 := by
  have : deriv (deriv (J a)) x =
      deriv (fun x ↦ 2⁻¹ * J (a - 1) x - 2⁻¹ * J (a + 1) x) x := by
    refine Set.EqOn.eq_of_mem ?_ h
    refine Set.EqOn.deriv ?_ isOpen_slitPlane
    intro x hx
    apply deriv_besselJ a hx
  rw [this, deriv_fun_sub (by fun_prop [h]) (by fun_prop [h]),
    deriv_const_mul _ (by fun_prop [h]), deriv_const_mul _ (by fun_prop [h]),
    deriv_besselJ _ h, deriv_besselJ _ h, deriv_besselJ _ h]
  convert_to x / 2 * J (a - 1) x - x / 2 * J (a + 1) x
    + x / 4 * (x * J (a - 1 - 1) x + x * J (a - 1 + 1) x)
    + x / 4 * (x * J (a + 1 - 1) x + x * J (a + 1 + 1) x)
    - a / 2 * (2 * a * J a x) = 0
  · ring_nf
  rw [besselJ_recurrence a, ← besselJ_recurrence (a - 1), ← besselJ_recurrence (a + 1)]
  ring

theorem besselJ_int_equation (a : ℤ) (x : ℂ) :
    x ^ 2 * deriv (deriv (J a)) x + x * deriv (J a) x + (x ^ 2 - a ^ 2) * J a x = 0 := by
  have : deriv (deriv (J a)) x =
      deriv (fun x ↦ 2⁻¹ * J (a - 1 : ℤ) x - 2⁻¹ * J (a + 1 : ℤ) x) x := by
    congr with x
    simpa using deriv_besselJ_int a x
  rw [this, deriv_fun_sub (by fun_prop) (by fun_prop),
    deriv_const_mul _ (by fun_prop), deriv_const_mul _ (by fun_prop),
    deriv_besselJ_int, deriv_besselJ_int, deriv_besselJ_int]
  push_cast
  convert_to x / 2 * J (a - 1) x - x / 2 * J (a + 1) x
    + x / 4 * (x * J (a - 1 - 1) x + x * J (a - 1 + 1) x)
    + x / 4 * (x * J (a + 1 - 1) x + x * J (a + 1 + 1) x)
    - a / 2 * (2 * a * J a x) = 0
  · ring_nf
  rw [besselJ_recurrence a, ← besselJ_recurrence (a - 1), ← besselJ_recurrence (a + 1)]
  ring

theorem besselJ_bound (a : ℤ) (x : ℂ) :
    ‖J a x‖ ≤ ‖x / 2‖ ^ a.natAbs * ((a.natAbs ! : ℝ)⁻¹ * Real.exp (‖x / 2‖ ^ 2)) := by
  wlog! ha : 0 ≤ a
  · specialize this (-a) (-x) (by simpa using ha.le)
    simpa [besselJ_neg_comm] using this
  obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le ha
  simp only [Int.cast_natCast, Int.natAbs_natCast]
  unfold besselJ
  rw [norm_mul, cpow_natCast, norm_pow]
  refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (norm_nonneg _) _)
  simp only [FormalMultilinearSeries.sum, besselJSeries,
    FormalMultilinearSeries.apply_eq_prod_smul_coeff, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul]
  have hexp := NormedSpace.exp_hasFPowerSeriesOnBall.hasSum (𝕜 := ℝ)
      (show ‖x / 2‖ ^ 2 ∈ Metric.eball 0 ⊤ by simp)
  rw [zero_add] at hexp
  have hsummable := hexp.summable.mul_left (a ! : ℝ)⁻¹
  rw [Real.exp_eq_exp_ℝ, ← hexp.tsum_eq, ← tsum_mul_left]
  have hle (i : ℕ) :
      ‖((x / 2) ^ 2) ^ i * ((-1) ^ i / (i ! * Gamma (a + 1 + i)))‖ ≤
      (a ! : ℝ)⁻¹ * (NormedSpace.expSeries ℝ ℝ i) fun _ ↦ ‖x / 2‖ ^ 2 := by
    have : Gamma (a + 1 + i) = (a + i) ! := by
      rw [← Gamma_nat_eq_factorial]
      congrm Gamma ?_
      push_cast
      ring
    rw [this]
    simp only [norm_mul, div_eq_mul_inv, mul_inv, norm_inv]
    have hgr : ‖((a + i) ! : ℂ)‖⁻¹ ≤ ‖(a ! : ℂ)‖⁻¹ := by
      rw [inv_le_inv₀ (by simpa using Nat.factorial_pos (a + i))
        (by simpa using Nat.factorial_pos a)]
      simp only [RCLike.norm_natCast, Nat.cast_le]
      apply Nat.factorial_le
      simp
    grw [hgr]
    apply le_of_eq
    simp [NormedSpace.expSeries_eq_ofScalars, field]
  refine (norm_tsum_le_tsum_norm ?summable).trans (Summable.tsum_le_tsum hle ?summable hsummable)
  exact Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) hle hsummable

noncomputable
def besselJGF (x t : ℂ) := ∑' a : ℤ, J a x * t ^ a

local notation "g" => besselJGF

noncomputable
def boundU (x t0 t1 : ℂ) (a : ℤ) :=
  ‖x / 2‖ ^ a.natAbs * ((a.natAbs ! : ℝ)⁻¹ * Real.exp (‖x / 2‖ ^ 2)) *
  if 0 ≤ a then ‖t1‖ ^ a else ‖t0‖ ^ a

theorem summable_boundU (x t0 t1 : ℂ) :
    Summable (boundU x t0 t1) := by
  apply Summable.of_nat_of_neg
  · suffices Summable fun a ↦
        (‖x‖ / 2) ^ a * ((a ! : ℝ)⁻¹ * Real.exp ((‖x‖ / 2) ^ 2)) * ‖t1‖ ^ a by
      simpa [boundU]
    convert_to Summable fun a ↦ Real.exp ((‖x‖ / 2) ^ 2) * (‖x / 2 * t1‖ ^ a * (a ! : ℝ)⁻¹)
    · ext
      simp
      ring
    apply Summable.mul_left
    set q := ‖x / 2 * t1‖
    simpa [NormedSpace.expSeries_eq_ofScalars] using
      (NormedSpace.exp_hasFPowerSeriesOnBall.hasSum (𝕜 := ℝ)
      (show q ∈ Metric.eball 0 ⊤ by simp)).summable
  · convert_to! Summable fun a ↦
        (‖x‖ / 2) ^ a * ((a ! : ℝ)⁻¹ * Real.exp ((‖x‖ / 2) ^ 2)) * ‖t0‖ ^ (-a : ℤ)
    · ext a
      by_cases ha0 : a = 0 <;> simp [ha0, boundU]
    convert_to Summable fun a ↦ Real.exp ((‖x‖ / 2) ^ 2) * (‖x / 2 / t0‖ ^ a * (a ! : ℝ)⁻¹)
    · ext
      simp
      ring
    apply Summable.mul_left
    set q := ‖x / 2 / t0‖
    simpa [NormedSpace.expSeries_eq_ofScalars, ] using
      (NormedSpace.exp_hasFPowerSeriesOnBall.hasSum (𝕜 := ℝ)
      (show q ∈ Metric.eball 0 ⊤ by simp)).summable

theorem hasDerivAt_besselJGF (x : ℂ) {t : ℂ} (ht : t ≠ 0) :
    HasDerivAt (g x) (x / 2 * (1 + t ^ (-2 : ℤ)) * g x t) t := by
  obtain ⟨t0, ht0m, ht0⟩ := IsCompact.exists_isMinOn (isCompact_closedBall t ‖t / 2‖)
    (Metric.nonempty_closedBall.mpr (by grind)) continuous_norm.continuousOn
  have ht00 : t0 ≠ 0 := by
    intro h
    have h : ‖t‖ ≤ ‖t‖ / 2 := by simpa [h] using ht0m
    rw [le_div_iff₀ (by simp), mul_two] at h
    simp [ht] at h
  obtain ⟨t1, ht1m, ht1⟩ := IsCompact.exists_isMaxOn (isCompact_closedBall t ‖t / 2‖)
    (Metric.nonempty_closedBall.mpr (by grind)) continuous_norm.continuousOn
  have ht0 {s : ℂ} (hs : s ∈ Metric.ball t ‖t / 2‖) : ‖t0‖ ≤ ‖s‖ := by
    rw [isMinOn_iff] at ht0
    apply ht0 s (Set.mem_of_mem_of_subset hs Metric.ball_subset_closedBall)
  have ht1 {s : ℂ} (hs : s ∈ Metric.ball t ‖t / 2‖) : ‖s‖ ≤ ‖t1‖ := by
    rw [isMaxOn_iff] at ht1
    apply ht1 s (Set.mem_of_mem_of_subset hs Metric.ball_subset_closedBall)
  have hs0 {s : ℂ} (hs : s ∈ Metric.ball t ‖t / 2‖) : s ≠ 0 := by
    intro h
    have hs : ‖t‖ < ‖t‖ / 2 := by simpa [h] using hs
    rw [lt_div_iff₀ (by simp), mul_two] at hs
    simp [(norm_nonneg t).not_gt] at hs
  have hdiff (a : ℤ) : DifferentiableOn ℂ (fun w ↦ J a x * w ^ a) (Metric.ball t ‖t / 2‖) := by
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    apply DifferentiableAt.const_mul
    simp [differentiableAt_zpow, hs0 hs]
  have hbound (a : ℤ) (s : ℂ) (hs : s ∈ Metric.ball t ‖t / 2‖) :
      ‖J a x * s ^ a‖ ≤ x.boundU t0 t1 a := by
    simp_rw [boundU]
    rw [norm_mul]
    grw [besselJ_bound]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    split_ifs with ha
    · rw [norm_zpow]
      apply zpow_le_zpow_left₀ ha (by simp) (ht1 hs)
    · rw [not_le] at ha
      rw [norm_zpow, ← inv_le_inv₀ (by positivity) (by positivity [hs0 hs]),
        ← zpow_neg, ← zpow_neg]
      apply zpow_le_zpow_left₀ (by simpa using ha.le) (by simp) (ht0 hs)
  convert! DifferentiableAt.hasDerivAt ?_ using 1
  · rw [← mul_div_right_comm _ _ 2, ← mul_div_right_comm _ _ 2,
    div_eq_iff (by simp), mul_comm _ 2]
    unfold besselJGF
    rw [mul_assoc, one_add_mul, ← tsum_mul_left]
    simp_rw [mul_left_comm (t ^ (-2 : ℤ)), ← zpow_add₀ ht]
    conv_lhs =>
      right
      conv =>
        right
        rw [← (Equiv.addRight 1).tsum_eq]
        simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one, Int.reduceNeg,
          (show ∀ c : ℤ, -2 + (c + 1) = c - 1 by intro; ring)]
      conv =>
        left
        rw [← (Equiv.addRight (-1)).tsum_eq]
        simp only [Int.reduceNeg, Equiv.coe_addRight, ← sub_eq_add_neg, Int.cast_sub, Int.cast_one]
    have hJsummable : Summable fun (a : ℤ) ↦ J a x * t ^ a :=
      (summable_boundU x t0 t1).of_norm_bounded (hbound · t (by simpa using ht))
    rw [← Summable.tsum_add
      (by exact_mod_cast (Equiv.subRight 1).summable_iff.mpr hJsummable)
      (by
        rw [← summable_mul_left_iff (zpow_ne_zero 2 ht)]
        simp_rw [mul_left_comm (t ^ (2 : ℤ)), ← zpow_add₀ ht,
          show ∀ a : ℤ, 2 + (a - 1) = a + 1 by intro; ring]
        exact_mod_cast (Equiv.addRight 1).summable_iff.mpr hJsummable)]
    simp_rw [← add_mul]
    rw [← tsum_mul_left]
    simp_rw [← mul_assoc, mul_add]
    simp_rw [← besselJ_recurrence]
    simp_rw [mul_assoc]
    rw [tsum_mul_left]
    simp_rw [mul_left_comm _ (J _ _)]
    rw [← (hasSum_deriv_of_summable_norm (summable_boundU x t0 t1) hdiff Metric.isOpen_ball hbound
      (by simpa using ht)).tsum_eq]
    simp
  apply (Complex.differentiableOn_tsum_of_summable_norm (summable_boundU x t0 t1) hdiff
    Metric.isOpen_ball hbound).differentiableAt
  apply Metric.ball_mem_nhds
  simpa using ht

theorem deriv_tsum_besselJ (x : ℂ) : HasDerivAt (fun x ↦ ∑' a : ℤ, J a x) 0 x := by
  obtain ⟨xmax, hxmm, hxm⟩ := IsCompact.exists_isMaxOn (isCompact_closedBall x 1)
    (Metric.nonempty_closedBall.mpr (by grind)) continuous_norm.continuousOn
  have hdiff (a : ℤ) : DifferentiableOn ℂ (J a) (Metric.ball x 1) := by
    intro x hx
    apply AnalyticAt.differentiableWithinAt
    fun_prop
  have hbound (a : ℤ) (x' : ℂ) (hx' : x' ∈ Metric.ball x 1): ‖J a x'‖ ≤ xmax.boundU 1 1 a := by
    simp_rw [boundU]
    grw [besselJ_bound]
    simp only [Complex.norm_div, norm_ofNat, norm_one, one_zpow, ite_self, mul_one]
    have hx' : ‖x'‖ ≤ ‖xmax‖ := by
      rw [isMaxOn_iff] at hxm
      exact hxm x' (Set.mem_of_mem_of_subset hx' Metric.ball_subset_closedBall)
    grw [hx', hx']
  have h : DifferentiableAt ℂ (fun x ↦ ∑' a : ℤ, J a x) x :=
    (Complex.differentiableOn_tsum_of_summable_norm (summable_boundU xmax 1 1) hdiff
      Metric.isOpen_ball hbound).differentiableAt (Metric.ball_mem_nhds _ (by simp))
  convert! ← h.hasDerivAt using 1
  rw [← (hasSum_deriv_of_summable_norm (summable_boundU xmax 1 1) hdiff Metric.isOpen_ball
    hbound (by simp)).tsum_eq]
  simp_rw [deriv_besselJ_int]
  have hJsummable : Summable fun (a : ℤ) ↦ 2⁻¹ * J a x := by
    apply Summable.mul_left
    exact (summable_boundU xmax 1 1).of_norm_bounded fun a ↦ hbound _ _ (by simp)
  rw [Summable.tsum_sub (by exact_mod_cast (Equiv.subRight 1).summable_iff.mpr hJsummable)
    (by exact_mod_cast (Equiv.addRight 1).summable_iff.mpr hJsummable)]
  conv_lhs =>
    conv =>
      left
      rw [← (Equiv.addRight 1).tsum_eq]
      simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one, add_sub_cancel_right]
    conv =>
      right
      rw [← (Equiv.addRight (-1)).tsum_eq]
      simp only [Int.reduceNeg, Equiv.coe_addRight, Int.cast_add, Int.cast_neg, Int.cast_one,
        neg_add_cancel_right]
  simp

@[simp]
theorem tsum_besselJ (x : ℂ) : ∑' a : ℤ, J a x = 1 := by
  simp [is_const_of_deriv_eq_zero (fun x ↦ (deriv_tsum_besselJ x).differentiableAt)
    (fun x ↦ (deriv_tsum_besselJ x).deriv) x 0]

theorem hasSum_besselJ (x : ℂ) : HasSum (fun (a : ℤ) ↦ J a x) 1 := by
  convert Summable.hasSum ?_
  · simp
  by_contra h
  simpa using tsum_eq_zero_of_not_summable h

@[simp]
theorem besselJGF_one (x : ℂ) : g x 1 = 1 := by
  simp [besselJGF]

theorem HasDerivAt.comp_ofReal' {e : ℂ → ℂ} {e' : ℂ} {z : ℝ} (hf : HasDerivAt e e' (ofReal z)) :
    HasDerivAt (e ∘ ofReal) e' z :=
  HasDerivAt.comp_ofReal hf

theorem besselJGF_eq (x : ℂ) {t : ℂ} (ht : t ≠ 0) :
    g x t = exp (x / 2 * (t - t⁻¹)) := by
  have hderiv {t : ℂ} (ht : t ≠ 0) :
      HasDerivAt (fun t ↦ cexp (x / 2 * (t - t⁻¹)))
      (x / 2 * (1 + (t ^ 2)⁻¹) * cexp (x / 2 * (t - (t)⁻¹))) t := by
    rw [mul_comm (x / 2 * (1 + (t ^ 2)⁻¹))]
    apply HasDerivAt.cexp
    apply HasDerivAt.const_mul
    simp_rw [sub_eq_add_neg]
    apply HasDerivAt.add
    · apply hasDerivAt_id
    · simpa using! (hasDerivAt_inv ht).neg
  suffices ({0}ᶜ : Set ℂ).EqOn (g x) (fun t ↦ exp (x / 2 * (t - t⁻¹))) by
    exact this (by simpa using ht)
  suffices (Complex.ofReal '' Set.Icc 1 2).EqOn (g x) (fun t ↦ exp (x / 2 * (t - t⁻¹))) by
    refine AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq ?_ ?_ ?_
      (show 1 ∈ ({0}ᶜ : Set ℂ) by simp) ?_
    · refine DifferentiableOn.analyticOnNhd ?_ (by simp)
      intro t ht
      exact (hasDerivAt_besselJGF _ (by simpa using ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      apply AnalyticAt.cexp
      apply AnalyticAt.mul (by fun_prop)
      apply AnalyticAt.sub (by fun_prop)
      apply analyticAt_inv (by simpa using ht)
    · exact (isConnected_compl_singleton_of_one_lt_rank (by simp) _).isPreconnected
    · rw [Filter.Frequently, Filter.Eventually, Metric.mem_nhdsWithin_iff]
      simp only [gt_iff_lt, not_exists, not_and]
      intro r hr
      rw [Set.not_subset]
      refine ⟨(min (1 + r / 2) 2 : ℝ), ⟨?_, ?_⟩ , ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm]
        norm_cast
        rw [Real.norm_eq_abs]
        grind
      · rw [Set.mem_compl_iff, Set.mem_singleton_iff, ofReal_eq_one]
        grind
      · rw [Set.mem_setOf_eq, not_not]
        apply this
        suffices 0 ≤ r / 2 by simpa
        grind
  rw [← Set.eqOn_comp_right_iff]
  let v : ℝ → ℂ → ℂ := (fun (t gt : ℂ) ↦ x / 2 * (1 + t ^ (-2 : ℤ)) * gt) ∘ ofReal
  let s : ℝ → Set ℂ := fun _ ↦ Set.univ
  have hv (t : ℝ) (ht : t ∈ Set.Ico 1 2) : LipschitzOnWith ‖x‖₊ (v t) (s t) := by
    intro a ha b hb
    suffices (‖x‖₊ / 2 * ‖1 + ((t : ℂ) ^ 2)⁻¹‖₊ : ENNReal) * ‖a - b‖₊ ≤ ‖x‖₊ * ‖a - b‖₊ by
      simpa [v, edist_eq_enorm_sub, ← mul_sub, enorm_eq_nnnorm] using! this
    suffices ‖1 + ((t : ℂ) ^ 2)⁻¹‖₊ ≤ 2 by
      grw [this]
      simp [ENNReal.div_mul_cancel]
    rw [← NNReal.coe_le_coe, coe_nnnorm]
    norm_cast
    rw [Real.norm_eq_abs]
    rw [abs_of_nonneg (add_nonneg (by simp) (by simpa using sq_nonneg t))]
    grind [one_le_sq_iff₀, sq_pos_iff, inv_le_one₀]
  refine ODE_solution_unique_of_mem_Icc_right hv (fun t ht ↦ ?_)  (fun t ht ↦ ?_)
      (fun t ht ↦ by simp [s]) (fun t ht ↦ ?_) (fun t ht ↦ ?_) (fun t ht ↦ by simp [s]) (by simp)
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp ?_ continuous_ofReal.continuousAt
    refine HasDerivAt.continuousAt (hasDerivAt_besselJGF _ ?_)
    rw [ofReal_eq_zero.ne]
    grind
  · apply HasDerivAt.hasDerivWithinAt
    apply HasDerivAt.comp_ofReal'
    apply hasDerivAt_besselJGF
    rw [ofReal_eq_zero.ne]
    grind
  · apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.comp ?_ continuous_ofReal.continuousAt
    refine HasDerivAt.continuousAt (hderiv ?_)
    rw [ofReal_eq_zero.ne]
    grind
  · apply HasDerivAt.hasDerivWithinAt
    apply HasDerivAt.comp_ofReal'
    apply hderiv
    rw [ofReal_eq_zero.ne]
    grind

theorem hasSum_besselJ_mul_pow (x : ℂ) {t : ℂ} (ht : t ≠ 0) :
    HasSum (fun (a : ℤ) ↦ J a x * t ^ a) (exp (x / 2 * (t - t⁻¹))) := by
  convert Summable.hasSum ?_
  · exact (besselJGF_eq x ht).symm
  by_contra h
  have h := tsum_eq_zero_of_not_summable h
  rw [← besselJGF, besselJGF_eq x ht] at h
  simp at h

theorem hasSum_besselJ_mul_exp (x t : ℂ) :
    HasSum (fun (a : ℤ) ↦ J a x * exp (a * t * I)) (exp (x * sin t * I)) := by
  convert hasSum_besselJ_mul_pow x (exp_ne_zero (t * I)) using 2 with a
  · rw [← exp_int_mul]
    ring_nf
  · rw [show sin t = 2 * sin t / 2 by simp, two_sin, ← exp_neg]
    trans x * ((cexp (-t * I) - cexp (t * I)) / 2) * I ^ 2
    · ring
    rw [I_sq]
    ring_nf

theorem besselJ_eq_integral (a : ℤ) (x : ℂ) :
    J a x = (2 * π)⁻¹ * ∫ t in 0..2 * π, exp ((x * sin t - a * t) * I) := by
  set τ := 2 * π
  have hτ : τ ≠ 0 := by simp [τ]
  have hleτ : 0 ≤ τ := by simpa [τ] using Real.pi_nonneg
  calc
  J a x = τ⁻¹ * (∫ t in 0..τ, J a x * exp (a * t * I) * exp (-(a * t) * I)) := by
    simp_rw [mul_assoc (J _ _), ← exp_add, ← add_mul]
    simp [hτ]
  _ = τ⁻¹ * (∑' b : ℤ, ∫ t in 0..τ, J b x * exp (b * t * I) * exp (-(a * t) * I)) := by
    congrm _ * ?_
    symm
    refine tsum_eq_single a (fun b hb ↦ ?_)
    have hab : b - a ≠ (0 : ℂ) := by simpa [sub_ne_zero] using hb
    simp_rw [mul_assoc (J _ _), ← exp_add, ← add_mul, ← sub_eq_add_neg, ← sub_mul]
    rw [intervalIntegral.integral_const_mul]
    apply mul_eq_zero_of_right
    have hderiv : ∀ t ∈ Set.uIcc 0 τ,
        HasDerivAt (fun (t : ℝ) ↦ ((b - a) * I)⁻¹ * exp ((b - a) * t * I))
        (exp ((b - a) * ↑t * I)) t := by
      intro t _
      convert_to HasDerivAt (fun (t : ℝ) ↦ ((b - a) * I)⁻¹ * exp ((b - a) * I * t))
        (((b - a) * I)⁻¹ * (exp ((b - a) * I * ↑t) * ((b - a) * I))) t
      · ring_nf
      · field_simp
      apply HasDerivAt.const_mul
      apply HasDerivAt.cexp
      apply HasDerivAt.comp_ofReal
      apply hasDerivAt_const_mul
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (Continuous.intervalIntegrable (by fun_prop) _ _)]
    rw [show cexp ((b - a) * τ * I) = exp ((b - a : ℤ) * (2 * π * I)) by
      simp [τ]
      ring_nf, exp_int_mul_two_pi_mul_I]
    simp
  _ = τ⁻¹ * (∫ t in 0..τ, ∑' b : ℤ, J b x * exp (b * t * I) * exp (-(a * t) * I)) := by
    simp_rw [intervalIntegral.integral_of_le hleτ]
    rw [MeasureTheory.integral_tsum_of_summable_integral_norm ?_ ?_]
    · intro a
      apply Continuous.integrableOn_Ioc
      fun_prop
    · norm_cast
      simp_rw [norm_mul, norm_exp_ofReal_mul_I, mul_one]
      simpa using (hasSum_besselJ x).summable.norm.mul_left (max τ 0)
  _ = _ := by
    simp_rw [tsum_mul_right, (hasSum_besselJ_mul_exp _ _).tsum_eq, ← exp_add, ← add_mul,
      ← sub_eq_add_neg]

theorem besselJ_eq_integral' (a : ℤ) (x : ℂ) :
    J a x = (2 * π)⁻¹ * ∫ t in 0..2 * π, exp ((a * t - x * sin t) * I) := by
  convert besselJ_eq_integral (-a) (-x) using 1
  · simp [besselJ_neg_comm]
  congrm _ * ∫ t in 0..2 * π, exp (?_ * I)
  push_cast
  ring

end Complex
