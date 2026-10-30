module

public import Cliquefree.Scalar

/-!
# Integral and differential properties of the scalar potential

This module establishes the analytic facts used in the weight lift from the
explicit Shearer function and scalar potential defined in `Cliquefree.Scalar`.
-/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace Cliquefree

/-- The unit-interval integral kernel for Shearer's function. -/
def shearerKernel (d t : ℝ) : ℝ := (1 - t) / (1 + (d - 1) * t)

theorem shearerKernel_den_lower {d t δ : ℝ} (hδ₁ : δ ≤ 1) (hδd : δ ≤ d)
    (ht : t ∈ Icc (0 : ℝ) 1) : δ ≤ 1 + (d - 1) * t := by
  nlinarith [mul_nonneg (sub_nonneg.mpr hδd) ht.1,
    mul_nonneg (sub_nonneg.mpr hδ₁) (sub_nonneg.mpr ht.2)]

theorem shearerKernel_den_pos {d t : ℝ} (hd : 0 < d) (ht : t ∈ Icc (0 : ℝ) 1) :
    0 < 1 + (d - 1) * t :=
  (lt_min zero_lt_one hd).trans_le
    (shearerKernel_den_lower (min_le_left 1 d) (min_le_right 1 d) ht)

theorem shearerKernel_continuousOn {d : ℝ} (hd : 0 < d) :
    ContinuousOn (shearerKernel d) (Icc 0 1) := by
  unfold shearerKernel
  exact (continuousOn_const.sub continuousOn_id).div
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    (fun t ht ↦ (shearerKernel_den_pos hd ht).ne')

theorem shearerKernel_intervalIntegrable {d : ℝ} (hd : 0 < d) :
    IntervalIntegrable (shearerKernel d) volume 0 1 :=
  (shearerKernel_continuousOn hd).intervalIntegrable_of_Icc zero_le_one

/-- The unit-interval integral representation of Shearer's function at positive degree. -/
theorem shearerF_eq_integral {d : ℝ} (hd : 0 < d) :
    shearerF d = ∫ t in (0 : ℝ)..1, shearerKernel d t := by
  by_cases h₁ : d = 1
  · subst d
    simp only [shearerF_one, shearerKernel, sub_self, zero_mul, add_zero, div_one]
    rw [intervalIntegral.integral_sub intervalIntegrable_const
      intervalIntegral.intervalIntegrable_id]
    norm_num [integral_id]
  let P : ℝ → ℝ := fun t ↦
    (d * Real.log (1 + (d - 1) * t) - (d - 1) * t) / (d - 1) ^ 2
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt P (shearerKernel d t) t := by
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    have hden := (((hasDerivAt_id t).const_mul (d - 1)).const_add 1)
    have hlog := (Real.hasDerivAt_log (shearerKernel_den_pos hd ht).ne').comp t hden
    have hraw := ((hlog.const_mul d).sub ((hasDerivAt_id t).const_mul (d - 1))).div_const
      ((d - 1) ^ 2)
    apply (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
    · simp only [mul_one]
      unfold shearerKernel
      field_simp [(shearerKernel_den_pos hd ht).ne', sub_ne_zero.mpr h₁]
      ring
    · filter_upwards [] with z
      rfl
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (shearerKernel_intervalIntegrable hd)
  rw [hint, shearerF_of_ne hd.ne' h₁]
  dsimp [P]
  simp only [mul_one, add_sub_cancel, mul_zero, add_zero, Real.log_one, mul_zero, sub_zero,
    zero_div, sub_zero]
  congr 1
  ring

/-- Convexity follows by integrating the convex reciprocal-affine kernels. -/
theorem shearerF_convexOn_pos : ConvexOn ℝ (Ioi 0) shearerF := by
  have hc : ConvexOn ℝ (Ioi 0)
      (fun d : ℝ ↦ ∫ t in (0 : ℝ)..1, shearerKernel d t) := by
    simp only [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    apply integral_convexOn_of_integrand_ae (convex_Ioi 0)
    · filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      let g : ℝ →ᵃ[ℝ] ℝ := (DistribSMul.toLinearMap ℝ ℝ t).toAffineMap +
        AffineMap.const ℝ ℝ (1 - t)
      have hg (d : ℝ) : g d = 1 + (d - 1) * t := by
        simp [g]
        ring
      have hpos : ∀ d ∈ Ioi (0 : ℝ), g d ∈ Ioi (0 : ℝ) := by
        intro d hd
        rw [hg]
        exact shearerKernel_den_pos hd ⟨ht.1.le, ht.2⟩
      have hrecip : ConvexOn ℝ (Ioi (0 : ℝ)) (fun d ↦ (g d) ^ (-1 : ℤ)) :=
        ((convexOn_zpow (-1)).comp_affineMap g).subset hpos (convex_Ioi 0)
      refine (hrecip.smul (sub_nonneg.mpr ht.2)).congr ?_
      intro d hd
      change (1 - t) * (g d) ^ (-1 : ℤ) = shearerKernel d t
      rw [hg]
      simp [shearerKernel, div_eq_mul_inv]
    · intro d hd
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
        (shearerKernel_intervalIntegrable hd)
  exact hc.congr (fun d hd ↦ (shearerF_eq_integral hd).symm)

/-- The derivative of the unit-interval kernel with respect to the degree parameter. -/
def shearerFirstKernel (d t : ℝ) : ℝ :=
  -(t * (1 - t)) / (1 + (d - 1) * t) ^ 2

theorem shearerFirstKernel_continuousOn {d : ℝ} (hd : 0 < d) :
    ContinuousOn (shearerFirstKernel d) (Icc 0 1) := by
  unfold shearerFirstKernel
  exact (continuousOn_id.mul (continuousOn_const.sub continuousOn_id)).neg.div
    ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 2)
    (fun t ht ↦ pow_ne_zero 2 (shearerKernel_den_pos hd ht).ne')

theorem shearerFirstKernel_norm_le {d t δ : ℝ} (hδ : 0 < δ) (hδ₁ : δ ≤ 1)
    (hδd : δ ≤ d) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖shearerFirstKernel d t‖ ≤ 1 / δ ^ 2 := by
  have hn : 0 ≤ t * (1 - t) := mul_nonneg ht.1 (sub_nonneg.mpr ht.2)
  have hn₁ : t * (1 - t) ≤ 1 := by nlinarith [sq_nonneg t, ht.2]
  have hden := shearerKernel_den_lower hδ₁ hδd ht
  rw [shearerFirstKernel, norm_div, norm_neg, Real.norm_eq_abs, abs_of_nonneg hn,
    Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact div_le_div₀ zero_le_one hn₁ (sq_pos_of_pos hδ) (pow_le_pow_left₀ hδ.le hden 2)

theorem shearerKernel_hasDerivAt {d t : ℝ} (hd : 0 < d) (ht : t ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ shearerKernel y t) (shearerFirstKernel d t) d := by
  have hden : HasDerivAt (fun y : ℝ ↦ 1 + (y - 1) * t) t d := by
    simpa using (((hasDerivAt_id' d).sub_const 1).mul_const t).const_add 1
  have hraw := (hasDerivAt_const d (1 - t)).div hden (shearerKernel_den_pos hd ht).ne'
  apply (hraw.congr_deriv ?_).congr_of_eventuallyEq ?_
  · unfold shearerFirstKernel
    ring
  · filter_upwards [] with y
    rfl

/-- Differentiation of the kernel integral, valid also at the removable singularity. -/
theorem shearerF_hasDerivAt_integral {d : ℝ} (hd : 0 < d) :
    HasDerivAt shearerF (∫ t in (0 : ℝ)..1, shearerFirstKernel d t) d := by
  let δ : ℝ := min 1 (d / 2)
  have hδ : 0 < δ := lt_min zero_lt_one (half_pos hd)
  have hraw : IntervalIntegrable (shearerFirstKernel d) volume 0 1 ∧
      HasDerivAt (fun y ↦ ∫ t in (0 : ℝ)..1, shearerKernel y t)
        (∫ t in (0 : ℝ)..1, shearerFirstKernel d t) d := by
    apply intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (F := shearerKernel) (F' := shearerFirstKernel) (bound := fun _ ↦ 1 / δ ^ 2)
      (s := Ioi (d / 2)) (Ioi_mem_nhds (half_lt_self hd))
    · filter_upwards [Ioi_mem_nhds (half_lt_self hd)] with y hy
      rw [uIoc_of_le zero_le_one]
      exact ((shearerKernel_continuousOn ((half_pos hd).trans hy)).mono
        Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · exact shearerKernel_intervalIntegrable hd
    · rw [uIoc_of_le zero_le_one]
      exact ((shearerFirstKernel_continuousOn hd).mono
        Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
    · apply ae_of_all volume
      intro t ht y hy
      rw [uIoc_of_le zero_le_one] at ht
      exact shearerFirstKernel_norm_le hδ (min_le_left _ _)
        ((min_le_right _ _).trans hy.le) ⟨ht.1.le, ht.2⟩
    · exact intervalIntegrable_const
    · apply ae_of_all volume
      intro t ht y hy
      rw [uIoc_of_le zero_le_one] at ht
      exact shearerKernel_hasDerivAt ((half_pos hd).trans hy) ⟨ht.1.le, ht.2⟩
  apply hraw.2.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hd] with y hy
  exact shearerF_eq_integral hy

@[simp] theorem shearerF_deriv_one : deriv shearerF 1 = -(1 / 6) := by
  rw [(shearerF_hasDerivAt_integral zero_lt_one).deriv]
  calc
    (∫ t in (0 : ℝ)..1, shearerFirstKernel 1 t) = ∫ t in (0 : ℝ)..1, t ^ 2 - t := by
      apply intervalIntegral.integral_congr
      intro t ht
      simp only [shearerFirstKernel, sub_self, zero_mul, add_zero, one_pow, div_one]
      ring
    _ = -(1 / 6) := by
      rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_pow 2)
        intervalIntegral.intervalIntegrable_id]
      norm_num [integral_pow, integral_id]

theorem shearerF_deriv_neg {d : ℝ} (hd : 0 < d) : deriv shearerF d < 0 := by
  rcases lt_trichotomy d 1 with h | rfl | h
  · exact shearerF_deriv_neg_of_lt_one hd h
  · norm_num
  · exact shearerF_deriv_neg_of_one_lt h

/-- The tangent line to the convex Shearer function is a global lower bound. -/
theorem shearerF_tangent_le {d e : ℝ} (hd : 0 < d) (he : 0 < e) :
    shearerF d + deriv shearerF d * (e - d) ≤ shearerF e := by
  have hf := (shearerF_hasDerivAt_integral hd).differentiableAt
  rcases lt_trichotomy d e with h | rfl | h
  · have hs := shearerF_convexOn_pos.deriv_le_slope hd he h hf
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    linarith
  · simp
  · have hs := shearerF_convexOn_pos.slope_le_deriv he hd h hf
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

/-- The stationary degree attains the scalar infimum. -/
theorem scalarPotential_eq_of_sq_eq_neg_deriv {a x d : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hx : x ^ 2 = -a * deriv shearerF d) :
    scalarPotential a x = a * shearerF d + d * x ^ 2 := by
  have hp : 0 < -a * deriv shearerF d := mul_pos_of_neg_of_neg (neg_neg_of_pos ha)
    (shearerF_deriv_neg hd)
  have hx₀ : x ≠ 0 := sq_pos_iff.mp (hx.symm ▸ hp)
  apply le_antisymm (scalarPotential_le_test ha.le hd)
  rw [scalarPotential, ite_eq_right hx₀]
  apply le_csInf (Set.Nonempty.image _ nonempty_Ioi)
  rintro y ⟨e, he, rfl⟩
  have ht := mul_le_mul_of_nonneg_left (shearerF_tangent_le hd he) ha.le
  rw [hx]
  nlinarith

theorem sqrt_neg_shearerF_deriv_pos {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    0 < Real.sqrt (-a * deriv shearerF d) :=
  Real.sqrt_pos.mpr (mul_pos_of_neg_of_neg (neg_neg_of_pos ha) (shearerF_deriv_neg hd))

/-- The exact scalar minimization identity used in the weight lift. -/
theorem scalarPotential_sqrt_neg_deriv {a d : ℝ} (ha : 0 < a) (hd : 0 < d) :
    scalarPotential a (Real.sqrt (-a * deriv shearerF d)) =
      a * shearerF d + d * (Real.sqrt (-a * deriv shearerF d)) ^ 2 := by
  apply scalarPotential_eq_of_sq_eq_neg_deriv ha hd
  exact Real.sq_sqrt (mul_pos_of_neg_of_neg (neg_neg_of_pos ha) (shearerF_deriv_neg hd)).le

end Cliquefree
