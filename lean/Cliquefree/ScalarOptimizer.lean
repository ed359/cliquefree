module

public import Cliquefree.ScalarCalculus

/-!
# Optimizers of the scalar potential

Second derivatives of Shearer's function and the unique scalar optimizer.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace Cliquefree

/-- The second degree derivative of the unit-interval kernel. -/
def shearerSecondKernel (d t : ℝ) : ℝ :=
  2 * t ^ 2 * (1 - t) / (1 + (d - 1) * t) ^ 3

theorem shearerSecondKernel_continuousOn {d : ℝ} (hd : 0 < d) :
    ContinuousOn (shearerSecondKernel d) (Icc 0 1) := by
  unfold shearerSecondKernel
  exact ((continuousOn_const.mul (continuousOn_id.pow 2)).mul
    (continuousOn_const.sub continuousOn_id)).div
    ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 3)
    (fun t ht ↦ pow_ne_zero 3 (shearerKernel_den_pos hd ht).ne')

theorem shearerSecondKernel_norm_le {d t δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hδd : δ ≤ d) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖shearerSecondKernel d t‖ ≤ 2 / δ ^ 3 := by
  have hn : 0 ≤ 2 * t ^ 2 * (1 - t) :=
    mul_nonneg (mul_nonneg zero_le_two (sq_nonneg t)) (sub_nonneg.mpr ht.2)
  have ht₂ : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  have hn₂ : 2 * t ^ 2 * (1 - t) ≤ 2 := by
    nlinarith [mul_nonneg (sq_nonneg t) ht.1]
  have hden := shearerKernel_den_lower hδ₁ hδd ht
  rw [shearerSecondKernel, norm_div, Real.norm_eq_abs, abs_of_nonneg hn,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (hδ.le.trans hden) 3)]
  exact div_le_div₀ zero_le_two hn₂ (pow_pos hδ 3) (pow_le_pow_left₀ hδ.le hden 3)

theorem shearerFirstKernel_hasDerivAt {d t : ℝ} (hd : 0 < d) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ shearerFirstKernel y t) (shearerSecondKernel d t) d := by
  have hden : HasDerivAt (fun y : ℝ ↦ 1 + (y - 1) * t) t d := by
    simpa using (((hasDerivAt_id' d).sub_const 1).mul_const t).const_add 1
  have hn := (shearerKernel_den_pos hd ht).ne'
  have hinv := (hden.inv hn).pow 2
  have hraw := (hasDerivAt_const d (-(t * (1 - t)))).mul hinv
  apply (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.inv_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one,
      zero_mul, zero_add]
    unfold shearerSecondKernel
    field_simp [hn]
  · filter_upwards [] with y
    simp only [shearerFirstKernel, Pi.mul_apply, Pi.inv_apply, Pi.pow_apply,
      div_eq_mul_inv, inv_pow]

/-- The second derivative is the integral of the positive second kernel. -/
theorem shearerF_deriv_hasDerivAt_integral {d : ℝ} (hd : 0 < d) :
    HasDerivAt (deriv shearerF) (∫ t in (0 : ℝ)..1, shearerSecondKernel d t) d := by
  let δ : ℝ := min 1 (d / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (half_pos hd)
  have hraw : IntervalIntegrable (shearerSecondKernel d) volume 0 1 ∧
      HasDerivAt (fun y ↦ ∫ t in (0 : ℝ)..1, shearerFirstKernel y t)
        (∫ t in (0 : ℝ)..1, shearerSecondKernel d t) d := by
    apply intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := shearerFirstKernel) (F' := shearerSecondKernel) (bound := fun _ ↦ 2 / δ ^ 3)
      (s := Ioi (d / 2)) (Ioi_mem_nhds (half_lt_self hd))
    · filter_upwards [Ioi_mem_nhds (half_lt_self hd)] with y hy
      rw [uIoc_of_le zero_le_one]
      exact ((shearerFirstKernel_continuousOn ((half_pos hd).trans hy)).mono
        Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · exact (shearerFirstKernel_continuousOn hd).intervalIntegrable_of_Icc zero_le_one
    · rw [uIoc_of_le zero_le_one]
      exact ((shearerSecondKernel_continuousOn hd).mono
        Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · apply ae_of_all volume
      intro t ht y hy
      rw [uIoc_of_le zero_le_one] at ht
      exact shearerSecondKernel_norm_le hδ (min_le_left _ _)
        ((min_le_right _ _).trans hy.le) ⟨ht.1.le, ht.2⟩
    · exact intervalIntegrable_const
    · apply ae_of_all volume
      intro t ht y hy
      rw [uIoc_of_le zero_le_one] at ht
      exact shearerFirstKernel_hasDerivAt ((half_pos hd).trans hy) ⟨ht.1.le, ht.2⟩
  apply hraw.2.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hd] with y hy
  exact (shearerF_hasDerivAt_integral hy).deriv

theorem shearerF_deriv2_pos {d : ℝ} (hd : 0 < d) : 0 < deriv (deriv shearerF) d := by
  rw [(shearerF_deriv_hasDerivAt_integral hd).deriv]
  apply intervalIntegral.integral_pos zero_lt_one (shearerSecondKernel_continuousOn hd)
  · intro t ht
    unfold shearerSecondKernel
    exact div_nonneg (mul_nonneg (mul_nonneg zero_le_two (sq_nonneg t))
      (sub_nonneg.mpr ht.2)) (pow_nonneg (shearerKernel_den_pos hd ⟨ht.1.le, ht.2⟩).le 3)
  · refine ⟨1 / 2, by norm_num, ?_⟩
    unfold shearerSecondKernel
    apply div_pos (by norm_num)
    exact pow_pos (shearerKernel_den_pos hd (by norm_num)) 3

theorem shearerF_strictConvexOn : StrictConvexOn ℝ (Ici 0) shearerF := by
  apply strictConvexOn_of_deriv2_pos (convex_Ici 0) shearerF_continuous.continuousOn
  intro d hd
  rw [interior_Ici] at hd
  exact shearerF_deriv2_pos hd

theorem shearerF_deriv_strictMonoOn : StrictMonoOn (deriv shearerF) (Ioi 0) :=
  (shearerF_strictConvexOn.subset Ioi_subset_Ici_self (convex_Ioi 0)).strictMonoOn_deriv
    (fun _ hd ↦ (shearerF_hasDerivAt_integral hd).differentiableAt)

theorem shearerF_deriv_continuousOn : ContinuousOn (deriv shearerF) (Ioi 0) :=
  fun _ hd ↦ (shearerF_deriv_hasDerivAt_integral hd).continuousAt.continuousWithinAt

theorem neg_shearerF_deriv_le {d : ℝ} (hd : 0 < d) : -deriv shearerF d ≤ 2 / d := by
  have ht := shearerF_tangent_le hd (half_pos hd)
  have hf := shearerF_pos hd.le
  have hf₁ := shearerF_le_one (half_pos hd).le
  apply (le_div_iff₀ hd).mpr
  nlinarith

theorem shearerF_deriv_tendsto_atTop : Tendsto (deriv shearerF) atTop (𝓝 0) := by
  have hbound : Tendsto (fun d : ℝ ↦ 2 / d) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hn : Tendsto (fun d : ℝ ↦ -deriv shearerF d) atTop (𝓝 0) := by
    apply squeeze_zero' ?_ ?_ hbound
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
      exact neg_nonneg.mpr (shearerF_deriv_neg hd).le
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with d hd
      exact neg_shearerF_deriv_le hd
  simpa only [neg_zero, neg_neg] using hn.neg

theorem shearerF_deriv_tendsto_zero_right :
    Tendsto (deriv shearerF) (𝓝[>] 0) atBot := by
  have hc : Tendsto (fun d : ℝ ↦ -(d + 1) / (d - 1) ^ 3) (𝓝[>] 0) (𝓝 1) := by
    have h : ContinuousAt (fun d : ℝ ↦ -(d + 1) / (d - 1) ^ 3) 0 :=
      (continuousAt_id.add continuousAt_const).neg.div
        ((continuousAt_id.sub continuousAt_const).pow 3) (by norm_num)
    convert h.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0) using 1
    norm_num
  have hb : Tendsto (fun d : ℝ ↦ 2 / (d - 1) ^ 2) (𝓝[>] 0) (𝓝 2) := by
    have h : ContinuousAt (fun d : ℝ ↦ 2 / (d - 1) ^ 2) 0 :=
      continuousAt_const.div ((continuousAt_id.sub continuousAt_const).pow 2) (by norm_num)
    convert h.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0) using 1
    norm_num
  have hlim := (Real.tendsto_log_nhdsGT_zero.atBot_mul_pos zero_lt_one hc).atBot_add hb
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds] with d hd h₁
  rw [(shearerF_hasDerivAt (show d ≠ 0 from ne_of_gt hd)
    (show d ≠ 1 from ne_of_lt h₁)).deriv]
  field_simp [sub_ne_zero.mpr (show d ≠ 1 from ne_of_lt h₁)]
  ring

theorem shearerF_deriv_existsUnique {z : ℝ} (hz : z < 0) :
    ∃! d : ℝ, 0 < d ∧ deriv shearerF d = z := by
  have hr : Iio (0 : ℝ) ⊆ (deriv shearerF) '' Ioi 0 :=
    isPreconnected_Ioi.intermediate_value_Iio
      (l₁ := 𝓝[>] (0 : ℝ)) (l₂ := atTop) inf_le_right
      (le_principal_iff.mpr (eventually_gt_atTop (0 : ℝ)))
      shearerF_deriv_continuousOn shearerF_deriv_tendsto_zero_right
      shearerF_deriv_tendsto_atTop
  obtain ⟨d, hd, hdz⟩ := hr hz
  refine ⟨d, ⟨hd, hdz⟩, ?_⟩
  intro e he
  exact shearerF_deriv_strictMonoOn.injOn he.1 hd (he.2.trans hdz.symm)

/-- The unique positive stationary degree for positive weight and coordinate. -/
def scalarOptimizer (a x : ℝ) : ℝ :=
  if h : 0 < a ∧ 0 < x then
    (shearerF_deriv_existsUnique
      (neg_neg_of_pos (div_pos (sq_pos_of_pos h.2) h.1))).choose
  else 0

theorem scalarOptimizer_spec {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < scalarOptimizer a x ∧ deriv shearerF (scalarOptimizer a x) = -(x ^ 2 / a) := by
  rw [scalarOptimizer, dite_eq_left ⟨ha, hx⟩]
  exact (shearerF_deriv_existsUnique
    (neg_neg_of_pos (div_pos (sq_pos_of_pos hx) ha))).choose_spec.1

theorem scalarOptimizer_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    0 < scalarOptimizer a x := (scalarOptimizer_spec ha hx).1

theorem scalarOptimizer_stationary {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    x ^ 2 = -a * deriv shearerF (scalarOptimizer a x) := by
  rw [(scalarOptimizer_spec ha hx).2]
  field_simp

theorem scalarPotential_eq_optimizer {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    scalarPotential a x = a * shearerF (scalarOptimizer a x) + scalarOptimizer a x * x ^ 2 :=
  scalarPotential_eq_of_sq_eq_neg_deriv ha (scalarOptimizer_pos ha hx)
    (scalarOptimizer_stationary ha hx)

theorem scalarOptimizer_continuousAt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ContinuousAt (scalarOptimizer a) x := by
  have ht : ContinuousAt (fun y : ℝ ↦ -(y ^ 2 / a)) x :=
    ((continuousAt_id.pow 2).div_const a).neg
  apply tendsto_order.mpr
  constructor
  · intro l hl
    by_cases hl₀ : 0 < l
    · have hb := shearerF_deriv_strictMonoOn hl₀ (scalarOptimizer_pos ha hx) hl
      rw [(scalarOptimizer_spec ha hx).2] at hb
      filter_upwards [ht.tendsto.eventually_const_lt hb, Ioi_mem_nhds hx] with y hy hy₀
      apply (shearerF_deriv_strictMonoOn.lt_iff_lt hl₀ (scalarOptimizer_pos ha hy₀)).mp
      rwa [(scalarOptimizer_spec ha hy₀).2]
    · filter_upwards [Ioi_mem_nhds hx] with y hy
      exact (le_of_not_gt hl₀).trans_lt (scalarOptimizer_pos ha hy)
  · intro u hu
    have hu₀ := (scalarOptimizer_pos ha hx).trans hu
    have hb := shearerF_deriv_strictMonoOn (scalarOptimizer_pos ha hx) hu₀ hu
    rw [(scalarOptimizer_spec ha hx).2] at hb
    filter_upwards [ht.tendsto.eventually_lt_const hb, Ioi_mem_nhds hx] with y hy hy₀
    apply (shearerF_deriv_strictMonoOn.lt_iff_lt (scalarOptimizer_pos ha hy₀) hu₀).mp
    rwa [(scalarOptimizer_spec ha hy₀).2]

theorem scalarPotential_continuousAt_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    ContinuousAt (scalarPotential a) x := by
  have ho := scalarOptimizer_continuousAt ha hx
  have hc : ContinuousAt (fun y : ℝ ↦ a * shearerF (scalarOptimizer a y) +
      scalarOptimizer a y * y ^ 2) x :=
    (continuousAt_const.mul (shearerF_continuous.continuousAt.comp ho)).add
      (ho.mul (continuousAt_id.pow 2))
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hx] with y hy
  exact scalarPotential_eq_optimizer ha hy

/-- The scalar potential is continuous, including its assigned endpoint value. -/
theorem scalarPotential_continuous {a : ℝ} (ha : 0 < a) : Continuous (scalarPotential a) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact scalarPotential_continuousAt_zero ha.le
  have hc := (scalarPotential_continuousAt_pos ha (abs_pos.mpr hx)).comp
    (continuous_abs.continuousAt : ContinuousAt (fun y : ℝ ↦ |y|) x)
  simpa [Function.comp_def] using hc

/-- Testing at the optimizer bounds increments by the corresponding quadratic. -/
theorem scalarPotential_sub_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (y : ℝ) :
    scalarPotential a y - scalarPotential a x ≤ scalarOptimizer a x * (y ^ 2 - x ^ 2) := by
  have ht := scalarPotential_le_test (x := y) ha.le (scalarOptimizer_pos ha hx)
  rw [scalarPotential_eq_optimizer ha hx]
  nlinarith

theorem scalarPotential_slope_bounds {a x y : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hy : 0 < y) (hne : y ≠ x) :
    min (scalarOptimizer a x * (y + x)) (scalarOptimizer a y * (y + x)) ≤
        slope (scalarPotential a) x y ∧
      slope (scalarPotential a) x y ≤
        max (scalarOptimizer a x * (y + x)) (scalarOptimizer a y * (y + x)) := by
  have hu := scalarPotential_sub_le ha hx y
  have hl := scalarPotential_sub_le ha hy x
  rw [slope_def_field]
  rcases lt_or_gt_of_ne hne with h | h
  · constructor
    · apply (min_le_left _ _).trans
      apply (le_div_iff_of_neg (sub_neg.mpr h)).mpr
      nlinarith
    · apply le_trans _ (le_max_right _ _)
      apply (div_le_iff_of_neg (sub_neg.mpr h)).mpr
      nlinarith
  · constructor
    · apply (min_le_right _ _).trans
      apply (le_div_iff₀ (sub_pos.mpr h)).mpr
      nlinarith
    · apply le_trans _ (le_max_left _ _)
      apply (div_le_iff₀ (sub_pos.mpr h)).mpr
      nlinarith

/-- The envelope derivative: `U'_a(x) = 2 d_*(a,x) x`. -/
theorem scalarPotential_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (scalarPotential a) (2 * scalarOptimizer a x * x) x := by
  have hc₁ : ContinuousAt (fun y : ℝ ↦ scalarOptimizer a x * (y + x)) x :=
    continuousAt_const.mul (continuousAt_id.add_const x)
  have hc₂ : ContinuousAt (fun y : ℝ ↦ scalarOptimizer a y * (y + x)) x :=
    (scalarOptimizer_continuousAt ha hx).mul (continuousAt_id.add_const x)
  have ht₁ : Tendsto (fun y : ℝ ↦ scalarOptimizer a x * (y + x)) (𝓝[≠] x)
      (𝓝 (2 * scalarOptimizer a x * x)) := by
    convert hc₁.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] x ≤ 𝓝 x) using 1
    congr 1
    ring
  have ht₂ : Tendsto (fun y : ℝ ↦ scalarOptimizer a y * (y + x)) (𝓝[≠] x)
      (𝓝 (2 * scalarOptimizer a x * x)) := by
    convert hc₂.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] x ≤ 𝓝 x) using 1
    congr 1
    ring
  have hmin := ht₁.min ht₂
  have hmax := ht₁.max ht₂
  simp only [min_self] at hmin
  simp only [max_self] at hmax
  have hb : ∀ᶠ y in 𝓝[≠] x,
      min (scalarOptimizer a x * (y + x)) (scalarOptimizer a y * (y + x)) ≤
          slope (scalarPotential a) x y ∧
        slope (scalarPotential a) x y ≤
          max (scalarOptimizer a x * (y + x)) (scalarOptimizer a y * (y + x)) := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hx).filter_mono nhdsWithin_le_nhds] with y hne hy
    exact scalarPotential_slope_bounds ha hx hy hne
  apply hasDerivAt_iff_tendsto_slope.mpr
  exact hmin.squeeze' hmax (hb.mono fun _ h ↦ h.1) (hb.mono fun _ h ↦ h.2)

theorem scalarXi_eq_optimizer {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    scalarXi a x = a * shearerF (scalarOptimizer a x) - scalarOptimizer a x * x ^ 2 := by
  rw [scalarXi, scalarPotential_eq_optimizer ha hx, (scalarPotential_hasDerivAt ha hx).deriv]
  ring

/-- The Shearer ODE expressed at the scalar optimizer. -/
theorem scalarOptimizer_ode {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    (1 + scalarOptimizer a x) * scalarXi a x +
      2 * scalarOptimizer a x * x ^ 2 = a := by
  rw [scalarXi_eq_optimizer ha hx, scalarOptimizer_stationary ha hx]
  have ho := congrArg (fun z : ℝ ↦ a * z) (shearerF_ode_all (scalarOptimizer a x))
  nlinarith

theorem shearerF_add_mul_deriv_pos {d : ℝ} (hd : 0 < d) :
    0 < shearerF d + d * deriv shearerF d := by
  have hi : IntervalIntegrable (shearerFirstKernel d) volume 0 1 :=
    (shearerFirstKernel_continuousOn hd).intervalIntegrable_of_Icc zero_le_one
  have heq : shearerF d + d * deriv shearerF d =
      ∫ t in (0 : ℝ)..1, (1 - t) ^ 2 / (1 + (d - 1) * t) ^ 2 := by
    rw [shearerF_eq_integral hd, (shearerF_hasDerivAt_integral hd).deriv,
      ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add (shearerKernel_intervalIntegrable hd) (hi.const_mul d)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    unfold shearerKernel shearerFirstKernel
    field_simp [(shearerKernel_den_pos hd ht).ne']
    ring
  rw [heq]
  apply intervalIntegral.integral_pos zero_lt_one
  · exact ((continuousOn_const.sub continuousOn_id).pow 2).div
      ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2)
      (fun t ht ↦ pow_ne_zero 2 (shearerKernel_den_pos hd ht).ne')
  · intro t ht
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact ⟨0, by norm_num, by norm_num⟩

theorem scalarXi_pos {a x : ℝ} (ha : 0 < a) (hx : 0 < x) : 0 < scalarXi a x := by
  rw [scalarXi_eq_optimizer ha hx, scalarOptimizer_stationary ha hx]
  have hp := mul_pos ha (shearerF_add_mul_deriv_pos (scalarOptimizer_pos ha hx))
  nlinarith

theorem scalarOptimizer_mul_scalarXi_le {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    scalarOptimizer a x * scalarXi a x ≤ a := by
  have ho := scalarOptimizer_ode ha hx
  have hp := scalarXi_pos ha hx
  nlinarith [mul_nonneg (scalarOptimizer_pos ha hx).le (sq_nonneg x)]

end Cliquefree
