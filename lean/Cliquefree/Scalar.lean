module

public import Mathlib

/-!
# Scalar functions for the weighted local independence bound

Shearer's function has the continuous values `f(0) = 1` and `f(1) = 1 / 2`.
The scalar potential is its variational transform, with value zero at zero auxiliary weight.
-/

@[expose] public section

noncomputable section

open Set Filter
open scoped Topology

namespace Cliquefree

/-- Shearer's function, with its continuous values at zero and one. -/
def shearerF (d : ℝ) : ℝ :=
  if d = 0 then 1 else if d = 1 then 1 / 2 else
    (d * Real.log d - d + 1) / (d - 1) ^ 2

@[simp] theorem shearerF_zero : shearerF 0 = 1 := by
  norm_num [shearerF]

@[simp] theorem shearerF_one : shearerF 1 = 1 / 2 := by
  norm_num [shearerF]

theorem shearerF_of_ne {d : ℝ} (h₀ : d ≠ 0) (h₁ : d ≠ 1) :
    shearerF d = (d * Real.log d - d + 1) / (d - 1) ^ 2 := by
  simp [shearerF, h₀, h₁]

theorem shearerF_pos {d : ℝ} (hd : 0 ≤ d) : 0 < shearerF d := by
  rcases eq_or_lt_of_le hd with h₀ | h₀
  · simp [← h₀]
  by_cases h₁ : d = 1
  · simp [h₁]
  rw [shearerF_of_ne h₀.ne' h₁]
  apply div_pos ?_ (sq_pos_of_ne_zero (sub_ne_zero.mpr h₁))
  have hlog := Real.log_lt_sub_one_of_pos (inv_pos.mpr h₀) (inv_ne_one.mpr h₁)
  rw [Real.log_inv] at hlog
  have hmul := mul_lt_mul_of_pos_left hlog h₀
  simp only [mul_sub, mul_inv_cancel₀ h₀.ne', mul_one] at hmul
  nlinarith

theorem shearerF_le_one {d : ℝ} (hd : 0 ≤ d) : shearerF d ≤ 1 := by
  rcases eq_or_lt_of_le hd with h₀ | h₀
  · simp [← h₀]
  by_cases h₁ : d = 1
  · norm_num [h₁]
  rw [shearerF_of_ne h₀.ne' h₁]
  apply (div_le_one (sq_pos_of_ne_zero (sub_ne_zero.mpr h₁))).mpr
  have hmul := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos h₀) hd
  nlinarith


theorem shearerF_of_ne_one {d : ℝ} (h₁ : d ≠ 1) :
    shearerF d = (d * Real.log d - d + 1) / (d - 1) ^ 2 := by
  by_cases h₀ : d = 0
  · simp [h₀]
  · exact shearerF_of_ne h₀ h₁

theorem shearerF_hasDerivAt {d : ℝ} (h₀ : d ≠ 0) (h₁ : d ≠ 1) :
    HasDerivAt shearerF ((2 * (d - 1) - (d + 1) * Real.log d) / (d - 1) ^ 3) d := by
  have hn := (((hasDerivAt_id d).mul (Real.hasDerivAt_log h₀)).sub
    (hasDerivAt_id d)).add_const 1
  have hd := ((hasDerivAt_id d).sub_const 1).pow 2
  have hq := hn.div hd (pow_ne_zero 2 (sub_ne_zero.mpr h₁))
  apply (hq.congr_deriv ?_).congr_of_eventuallyEq ?_
  · simp only [Pi.pow_apply, Pi.mul_apply, Pi.sub_apply, id_eq, one_mul,
      mul_inv_cancel₀ h₀]
    field_simp
    ring
  · filter_upwards [eventually_ne_nhds h₁] with y hy
    exact shearerF_of_ne_one hy

/-- The differential identity for Shearer's function away from its removable singularity. -/
theorem shearerF_ode {d : ℝ} (h₀ : d ≠ 0) (h₁ : d ≠ 1) :
    d * (d - 1) * deriv shearerF d + (d + 1) * shearerF d = 1 := by
  rw [(shearerF_hasDerivAt h₀ h₁).deriv, shearerF_of_ne h₀ h₁]
  field_simp [sub_ne_zero.mpr h₁]
  ring

/-- The differential identity also holds at both specified endpoints. -/
theorem shearerF_ode_all (d : ℝ) :
    d * (d - 1) * deriv shearerF d + (d + 1) * shearerF d = 1 := by
  by_cases h₀ : d = 0
  · simp [h₀]
  by_cases h₁ : d = 1
  · norm_num [h₁]
  exact shearerF_ode h₀ h₁

theorem shearerF_continuousAt_zero : ContinuousAt shearerF 0 := by
  have hn : ContinuousAt (fun d : ℝ ↦ d * Real.log d - d + 1) 0 :=
    (Real.continuous_mul_log.continuousAt.sub continuousAt_id).add continuousAt_const
  have hd : ContinuousAt (fun d : ℝ ↦ (d - 1) ^ 2) 0 :=
    (continuousAt_id.sub continuousAt_const).pow 2
  apply (hn.div hd (by norm_num)).congr
  filter_upwards [eventually_ne_nhds (show (0 : ℝ) ≠ 1 by norm_num)] with y hy
  exact (shearerF_of_ne_one hy).symm

/-- The scalar potential `U_a(x)`, with its assigned value at zero. -/
def scalarPotential (a x : ℝ) : ℝ :=
  if x = 0 then 0 else sInf ((fun d : ℝ ↦ a * shearerF d + d * x ^ 2) '' Ioi 0)

/-- The scalar quantity `ξ_a(x) = U_a(x) - x U'_a(x)`. -/
def scalarXi (a x : ℝ) : ℝ :=
  scalarPotential a x - x * deriv (scalarPotential a) x

@[simp] theorem scalarPotential_zero (a : ℝ) : scalarPotential a 0 = 0 := by
  simp [scalarPotential]

theorem scalarPotential_nonneg {a x : ℝ} (ha : 0 ≤ a) : 0 ≤ scalarPotential a x := by
  unfold scalarPotential
  split_ifs with hx
  · exact le_rfl
  · apply le_csInf (Set.Nonempty.image _ nonempty_Ioi)
    rintro y ⟨d, hd, rfl⟩
    exact add_nonneg (mul_nonneg ha (shearerF_pos hd.le).le)
      (mul_nonneg hd.le (sq_nonneg x))

/-- Every positive degree is an admissible test value for the infimum. -/
theorem scalarPotential_le_test {a x d : ℝ} (ha : 0 ≤ a) (hd : 0 < d) :
    scalarPotential a x ≤ a * shearerF d + d * x ^ 2 := by
  unfold scalarPotential
  split_ifs with hx
  · exact add_nonneg (mul_nonneg ha (shearerF_pos hd.le).le)
      (mul_nonneg hd.le (sq_nonneg x))
  · apply csInf_le
    · refine ⟨0, ?_⟩
      rintro y ⟨t, ht, rfl⟩
      exact add_nonneg (mul_nonneg ha (shearerF_pos ht.le).le)
        (mul_nonneg ht.le (sq_nonneg x))
    · exact ⟨d, hd, rfl⟩

/-- Letting the test degree tend to zero gives the uniform bound `U_a(x) ≤ a`. -/
theorem scalarPotential_le_weight {a x : ℝ} (ha : 0 ≤ a) : scalarPotential a x ≤ a := by
  have hcont : ContinuousAt (fun d : ℝ ↦ a * shearerF d + d * x ^ 2) 0 :=
    (continuousAt_const.mul shearerF_continuousAt_zero).add
      (continuousAt_id.mul continuousAt_const)
  have ht : Tendsto (fun d : ℝ ↦ a * shearerF d + d * x ^ 2) (𝓝[>] 0) (𝓝 a) := by
    simpa using hcont.tendsto.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact scalarPotential_le_test ha hd

/-- The test inequality extends to degree zero, using `f(0) = 1`. -/
theorem scalarPotential_le_test_nonneg {a x d : ℝ} (ha : 0 ≤ a) (hd : 0 ≤ d) :
    scalarPotential a x ≤ a * shearerF d + d * x ^ 2 := by
  rcases eq_or_lt_of_le hd with hd | hd
  · simpa [← hd] using (scalarPotential_le_weight (x := x) ha)
  · exact scalarPotential_le_test ha hd

theorem scalarPotential_mono_coordinate {a x y : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hxy : x ≤ y) : scalarPotential a x ≤ scalarPotential a y := by
  by_cases hy : y = 0
  · have hx₀ : x = 0 := le_antisymm (hy ▸ hxy) hx
    simp [hy, hx₀]
  conv_rhs => rw [scalarPotential, ite_eq_right hy]
  apply le_csInf (Set.Nonempty.image _ nonempty_Ioi)
  rintro z ⟨d, hd, rfl⟩
  exact (scalarPotential_le_test ha hd).trans
    (add_le_add le_rfl (mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ hx (hx.trans hxy)).mpr hxy) hd.le))

/-- The explicit value at one removes the apparent singularity of the quotient formula. -/
theorem shearerF_continuousAt_one : ContinuousAt shearerF 1 := by
  have hff : ∀ᶠ d : ℝ in 𝓝[≠] 1,
      HasDerivAt (fun t : ℝ ↦ t * Real.log t - t + 1) (Real.log d) d := by
    filter_upwards [(eventually_ne_nhds (show (1 : ℝ) ≠ 0 by norm_num)).filter_mono
      nhdsWithin_le_nhds] with d hd
    simpa only [Pi.mul_apply, Pi.sub_apply, id_eq, one_mul, mul_inv_cancel₀ hd,
      add_sub_cancel_right] using (((hasDerivAt_id d).mul (Real.hasDerivAt_log hd)).sub
        (hasDerivAt_id d)).add_const 1
  have hgg : ∀ᶠ d : ℝ in 𝓝[≠] 1,
      HasDerivAt (fun t : ℝ ↦ (t - 1) ^ 2) (2 * (d - 1)) d := by
    filter_upwards [] with d
    simpa [Pi.pow_def] using ((hasDerivAt_id d).sub_const 1).pow 2
  have hgn : ∀ᶠ d : ℝ in 𝓝[≠] 1, 2 * (d - 1) ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hd)
  have hfn : Tendsto (fun d : ℝ ↦ d * Real.log d - d + 1) (𝓝[≠] 1) (𝓝 0) := by
    have hc : ContinuousAt (fun d : ℝ ↦ d * Real.log d - d + 1) 1 :=
      (Real.continuous_mul_log.continuousAt.sub continuousAt_id).add continuousAt_const
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hgd : Tendsto (fun d : ℝ ↦ (d - 1) ^ 2) (𝓝[≠] 1) (𝓝 0) := by
    simpa [Pi.pow_def, Pi.sub_def] using (((continuousAt_id.sub continuousAt_const).pow 2 :
      ContinuousAt (fun d : ℝ ↦ (d - 1) ^ 2) 1).tendsto.mono_left nhdsWithin_le_nhds)
  have hdiv : Tendsto (fun d : ℝ ↦ Real.log d / (2 * (d - 1))) (𝓝[≠] 1) (𝓝 (1 / 2)) := by
    simpa [slope_def_field, div_div, mul_comm] using
      (Real.hasDerivAt_log (show (1 : ℝ) ≠ 0 by norm_num)).tendsto_slope.div_const 2
  rw [continuousAt_iff_punctured_nhds, shearerF_one]
  apply (HasDerivAt.lhopital_zero_nhdsNE hff hgg hgn hfn hgd hdiv).congr'
  filter_upwards [self_mem_nhdsWithin] with d hd
  exact (shearerF_of_ne_one hd).symm

theorem shearerF_continuous : Continuous shearerF := by
  apply continuous_iff_continuousAt.mpr
  intro d
  by_cases h₀ : d = 0
  · simpa [h₀] using shearerF_continuousAt_zero
  by_cases h₁ : d = 1
  · simpa [h₁] using shearerF_continuousAt_one
  exact (shearerF_hasDerivAt h₀ h₁).continuousAt

theorem shearerF_deriv_neg_of_one_lt {d : ℝ} (hd : 1 < d) : deriv shearerF d < 0 := by
  have hd₀ : 0 < d := zero_lt_one.trans hd
  rw [(shearerF_hasDerivAt hd₀.ne' hd.ne').deriv]
  apply div_neg_of_neg_of_pos ?_ (pow_pos (sub_pos.mpr hd) 3)
  have hlog : 2 * (d - 1) / (d + 1) < Real.log d := by
    simpa only [show 1 + (d - 1) = d by ring, show d - 1 + 2 = d + 1 by ring] using
      Real.lt_log_one_add_of_pos (sub_pos.mpr hd)
  have hm := (div_lt_iff₀ (by linarith : 0 < d + 1)).mp hlog
  nlinarith

theorem shearerF_deriv_neg_of_lt_one {d : ℝ} (hd : 0 < d) (h₁ : d < 1) :
    deriv shearerF d < 0 := by
  rw [(shearerF_hasDerivAt hd.ne' h₁.ne).deriv]
  have hinv : 1 < d⁻¹ := (one_lt_inv₀ hd).mpr h₁
  have hlog : 2 * (d⁻¹ - 1) / (d⁻¹ + 1) < -Real.log d := by
    simpa only [show 1 + (d⁻¹ - 1) = d⁻¹ by ring,
      show d⁻¹ - 1 + 2 = d⁻¹ + 1 by ring, Real.log_inv] using
      Real.lt_log_one_add_of_pos (sub_pos.mpr hinv)
  have hm := (div_lt_iff₀ (by positivity : 0 < d⁻¹ + 1)).mp hlog
  have hm' : 2 - 2 * d < -Real.log d * (1 + d) := by
    convert mul_lt_mul_of_pos_left hm hd using 1 <;> field_simp
  apply div_neg_of_pos_of_neg (by nlinarith [hm'])
  simpa only [pow_succ] using mul_neg_of_pos_of_neg
    (sq_pos_of_ne_zero (sub_ne_zero.mpr h₁.ne)) (sub_neg.mpr h₁)

/-- Shearer's function is strictly decreasing on its nonnegative domain. -/
theorem shearerF_strictAntiOn : StrictAntiOn shearerF (Ici 0) := by
  have hl : StrictAntiOn shearerF (Icc 0 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Icc 0 1) shearerF_continuous.continuousOn
    intro d hd
    rw [interior_Icc] at hd
    exact shearerF_deriv_neg_of_lt_one hd.1 hd.2
  have hr : StrictAntiOn shearerF (Ici 1) := by
    apply strictAntiOn_of_deriv_neg (convex_Ici 1) shearerF_continuous.continuousOn
    intro d hd
    rw [interior_Ici] at hd
    exact shearerF_deriv_neg_of_one_lt hd
  have hu := hl.union hr (isGreatest_Icc (show (0 : ℝ) ≤ 1 by norm_num)) isLeast_Ici
  simpa only [Icc_union_Ici_eq_Ici (show (0 : ℝ) ≤ 1 by norm_num)] using hu

theorem shearerF_tendsto_atTop : Tendsto shearerF atTop (𝓝 0) := by
  have hl : Tendsto (fun d : ℝ ↦ Real.log d / d) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hi : Tendsto (fun d : ℝ ↦ d⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hlim : Tendsto
      (fun d : ℝ ↦ (Real.log d / d - d⁻¹ + (d⁻¹) ^ 2) / (1 - d⁻¹) ^ 2)
      atTop (𝓝 0) := by
    simpa [Pi.div_def] using ((hl.sub hi).add (hi.pow 2)).div
      ((tendsto_const_nhds.sub hi).pow 2) (by norm_num)
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with d hd
  rw [shearerF_of_ne (zero_lt_one.trans hd).ne' hd.ne']
  field_simp

theorem scalarPotential_le_inverse_test {a x : ℝ} (ha : 0 ≤ a) (hx : 0 < x) :
    scalarPotential a x ≤ a * shearerF x⁻¹ + x := by
  calc
    scalarPotential a x ≤ a * shearerF x⁻¹ + x⁻¹ * x ^ 2 :=
      scalarPotential_le_test ha (inv_pos.mpr hx)
    _ = a * shearerF x⁻¹ + x := by field_simp

/-- The assigned endpoint value agrees with the limit from positive coordinates. -/
theorem scalarPotential_tendsto_zero_right {a : ℝ} (ha : 0 ≤ a) :
    Tendsto (scalarPotential a) (𝓝[>] 0) (𝓝 0) := by
  have hf := shearerF_tendsto_atTop.comp tendsto_inv_nhdsGT_zero
  have hx : Tendsto (fun x : ℝ ↦ x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hu : Tendsto (fun x : ℝ ↦ a * shearerF x⁻¹ + x) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hf).add hx
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ scalarPotential_nonneg ha) ?_ hu
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact scalarPotential_le_inverse_test ha hx

@[simp] theorem scalarPotential_abs (a x : ℝ) : scalarPotential a |x| = scalarPotential a x := by
  simp only [scalarPotential, abs_eq_zero, sq_abs]

theorem scalarPotential_continuousAt_zero {a : ℝ} (ha : 0 ≤ a) :
    ContinuousAt (scalarPotential a) 0 := by
  rw [continuousAt_iff_punctured_nhds, scalarPotential_zero]
  simpa [Function.comp_def] using
    (scalarPotential_tendsto_zero_right ha).comp tendsto_abs_nhdsNE_zero

end Cliquefree
