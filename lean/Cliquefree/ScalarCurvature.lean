module
public import Cliquefree.ScalarOptimizer

/-! # Curvature and tangent estimates for the scalar potential -/

@[expose] public section

noncomputable section

open Set Filter MeasureTheory
open scoped Topology

namespace Cliquefree

theorem scalarOptimizer_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (scalarOptimizer a)
      (-2 * x / (a * deriv (deriv shearerF) (scalarOptimizer a x))) x := by
  have hd := scalarOptimizer_pos ha hx
  have hf := (shearerF_deriv_hasDerivAt_integral hd).differentiableAt.hasDerivAt
  have hh : HasDerivAt (fun y : ℝ ↦ -(y ^ 2 / a)) (-(2 * x / a)) x := by
    simpa [Pi.neg_def, Pi.pow_def] using
      (((hasDerivAt_id' x).pow 2).div_const a).neg
  have hi := HasDerivAt.of_comp_left (scalarOptimizer_continuousAt ha hx) hf hh
    (shearerF_deriv2_pos hd).ne' (by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact (scalarOptimizer_spec ha hy).2)
  convert hi using 1
  simp [div_eq_mul_inv]
  ring

theorem scalarPotential_deriv_hasDerivAt {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    HasDerivAt (deriv (scalarPotential a))
      (2 * scalarOptimizer a x -
        4 * x ^ 2 / (a * deriv (deriv shearerF) (scalarOptimizer a x))) x := by
  have hh := ((scalarOptimizer_hasDerivAt ha hx).const_mul 2).mul (hasDerivAt_id' x)
  have he : deriv (scalarPotential a) =ᶠ[𝓝 x]
      (fun y : ℝ ↦ 2 * scalarOptimizer a y * y) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy
    exact (scalarPotential_hasDerivAt ha hy).deriv
  convert hh.congr_of_eventuallyEq he using 1
  ring

theorem shearerF_deriv2_mul_lt {d : ℝ} (hd : 0 < d) :
    d * deriv (deriv shearerF) d < -2 * deriv shearerF d := by
  have hi₁ : IntervalIntegrable (shearerFirstKernel d) volume 0 1 :=
    (shearerFirstKernel_continuousOn hd).intervalIntegrable_of_Icc zero_le_one
  have hi₂ : IntervalIntegrable (shearerSecondKernel d) volume 0 1 :=
    (shearerSecondKernel_continuousOn hd).intervalIntegrable_of_Icc zero_le_one
  have he : -2 * deriv shearerF d - d * deriv (deriv shearerF) d =
      ∫ t in (0 : ℝ)..1, 2 * t * (1 - t) ^ 2 / (1 + (d - 1) * t) ^ 3 := by
    rw [(shearerF_hasDerivAt_integral hd).deriv,
      (shearerF_deriv_hasDerivAt_integral hd).deriv,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_sub (hi₁.const_mul (-2)) (hi₂.const_mul d)]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    unfold shearerFirstKernel shearerSecondKernel
    field_simp [(shearerKernel_den_pos hd ht).ne']
    ring
  have hp : 0 < ∫ t in (0 : ℝ)..1,
      2 * t * (1 - t) ^ 2 / (1 + (d - 1) * t) ^ 3 := by
    apply intervalIntegral.integral_pos zero_lt_one
    · exact ((continuousOn_const.mul continuousOn_id).mul
        ((continuousOn_const.sub continuousOn_id).pow 2)).div
        ((continuousOn_const.add (continuousOn_const.mul continuousOn_id)).pow 3)
        (fun t ht ↦ pow_ne_zero 3 (shearerKernel_den_pos hd ht).ne')
    · intro t ht
      exact div_nonneg (mul_nonneg (mul_nonneg zero_le_two ht.1.le) (sq_nonneg _))
        (pow_nonneg (shearerKernel_den_pos hd ⟨ht.1.le, ht.2⟩).le 3)
    · refine ⟨1 / 2, by norm_num, ?_⟩
      exact div_pos (by norm_num) (pow_pos (shearerKernel_den_pos hd (by norm_num)) 3)
  linarith

theorem shearerF_deriv_quadratic_nonneg {d : ℝ} (hd : 0 < d) (z : ℝ) :
    0 ≤ shearerF d + 2 * z * deriv shearerF d +
      z ^ 2 / 2 * deriv (deriv shearerF) d := by
  have hi₀ := shearerKernel_intervalIntegrable hd
  have hi₁ : IntervalIntegrable (shearerFirstKernel d) volume 0 1 :=
    (shearerFirstKernel_continuousOn hd).intervalIntegrable_of_Icc zero_le_one
  have hi₂ : IntervalIntegrable (shearerSecondKernel d) volume 0 1 :=
    (shearerSecondKernel_continuousOn hd).intervalIntegrable_of_Icc zero_le_one
  have he : shearerF d + 2 * z * deriv shearerF d +
      z ^ 2 / 2 * deriv (deriv shearerF) d =
      ∫ t in (0 : ℝ)..1,
        (1 - t) * (1 + (d - 1) * t - z * t) ^ 2 / (1 + (d - 1) * t) ^ 3 := by
    rw [shearerF_eq_integral hd, (shearerF_hasDerivAt_integral hd).deriv,
      (shearerF_deriv_hasDerivAt_integral hd).deriv,
      ← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
      ← intervalIntegral.integral_add hi₀ (hi₁.const_mul (2 * z)),
      ← intervalIntegral.integral_add (hi₀.add (hi₁.const_mul (2 * z)))
        (hi₂.const_mul (z ^ 2 / 2))]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le zero_le_one] at ht
    unfold shearerKernel shearerFirstKernel shearerSecondKernel
    field_simp [(shearerKernel_den_pos hd ht).ne']
    ring
  rw [he]
  apply intervalIntegral.integral_nonneg zero_le_one
  intro t ht
  exact div_nonneg (mul_nonneg (sub_nonneg.mpr ht.2) (sq_nonneg _))
    (pow_nonneg (shearerKernel_den_pos hd ht).le 3)

theorem shearerF_deriv_sq_le {d : ℝ} (hd : 0 < d) :
    2 * (deriv shearerF d) ^ 2 ≤ shearerF d * deriv (deriv shearerF) d := by
  let z := -2 * deriv shearerF d / deriv (deriv shearerF) d
  have hp := shearerF_deriv2_pos hd
  have hn := mul_nonneg (shearerF_deriv_quadratic_nonneg hd z) hp.le
  have he : (shearerF d + 2 * z * deriv shearerF d +
      z ^ 2 / 2 * deriv (deriv shearerF) d) * deriv (deriv shearerF) d =
      shearerF d * deriv (deriv shearerF) d - 2 * (deriv shearerF d) ^ 2 := by
    dsimp [z]
    field_simp [hp.ne']
    ring
  rw [he] at hn
  linarith

theorem scalarPotential_deriv2_neg {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    deriv (deriv (scalarPotential a)) x < 0 := by
  have hd := scalarOptimizer_pos ha hx
  have h₂ := shearerF_deriv2_pos hd
  have ht := mul_lt_mul_of_pos_left (shearerF_deriv2_mul_lt hd) ha
  have hs := scalarOptimizer_stationary ha hx
  have hb : 2 * scalarOptimizer a x <
      4 * x ^ 2 / (a * deriv (deriv shearerF) (scalarOptimizer a x)) := by
    apply (lt_div_iff₀ (mul_pos ha h₂)).mpr
    nlinarith
  rw [(scalarPotential_deriv_hasDerivAt ha hx).deriv]
  linarith

theorem scalarPotential_curvature_le_xi {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    -deriv (deriv (scalarPotential a)) x ≤ 2 * scalarXi a x / x ^ 2 := by
  let d := scalarOptimizer a x
  have hd : 0 < d := scalarOptimizer_pos ha hx
  have h₂ := shearerF_deriv2_pos hd
  have hs := scalarOptimizer_stationary ha hx
  have hc := mul_le_mul_of_nonneg_left (shearerF_deriv_sq_le hd) (sq_nonneg a)
  have ht : 2 * x ^ 2 / (a * deriv (deriv shearerF) d) ≤ a * shearerF d / x ^ 2 := by
    apply (div_le_div_iff₀ (mul_pos ha h₂) (sq_pos_of_pos hx)).mpr
    dsimp [d] at hc ⊢
    nlinarith [sq_nonneg (a * deriv shearerF (scalarOptimizer a x))]
  have he : 2 * scalarXi a x / x ^ 2 = 2 * (a * shearerF d / x ^ 2) - 2 * d := by
    rw [scalarXi_eq_optimizer ha hx]
    dsimp [d]
    field_simp [hx.ne']
  rw [(scalarPotential_deriv_hasDerivAt ha hx).deriv, he]
  change -(2 * d - 4 * x ^ 2 / (a * deriv (deriv shearerF) d)) ≤ _
  rw [show 4 * x ^ 2 / (a * deriv (deriv shearerF) d) =
    2 * (2 * x ^ 2 / (a * deriv (deriv shearerF) d)) by ring]
  linarith

theorem scalarPotential_strictConcaveOn {a : ℝ} (ha : 0 < a) :
    StrictConcaveOn ℝ (Ici 0) (scalarPotential a) := by
  apply strictConcaveOn_of_deriv2_neg (convex_Ici 0)
    (scalarPotential_continuous ha).continuousOn
  intro x hx
  rw [interior_Ici] at hx
  exact scalarPotential_deriv2_neg ha hx

theorem scalarPotential_tangent_nonneg {a x y : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hy : 0 ≤ y) :
    0 ≤ scalarPotential a x + deriv (scalarPotential a) x * (y - x) -
      scalarPotential a y := by
  have hc := (scalarPotential_strictConcaveOn ha).concaveOn
  have hf := (scalarPotential_hasDerivAt ha hx).differentiableAt
  rcases lt_trichotomy x y with h | rfl | h
  · have hs := hc.slope_le_deriv hx.le hy h hf
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    linarith
  · simp
  · have hs := hc.deriv_le_slope hy hx.le h hf
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith

theorem scalarOptimizer_mul_scalarXi_eq {a x : ℝ} (ha : 0 < a) (hx : 0 < x) :
    scalarOptimizer a x * scalarXi a x = a - scalarPotential a x := by
  have ho := scalarOptimizer_ode ha hx
  have he : scalarPotential a x = scalarXi a x + 2 * scalarOptimizer a x * x ^ 2 := by
    rw [scalarXi, (scalarPotential_hasDerivAt ha hx).deriv]
    ring
  linarith

theorem scalarOptimizer_mul_scalarXi_antitone {a x y : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxy : x ≤ y) :
    scalarOptimizer a y * scalarXi a y ≤ scalarOptimizer a x * scalarXi a x := by
  rw [scalarOptimizer_mul_scalarXi_eq ha (hx.trans_le hxy),
    scalarOptimizer_mul_scalarXi_eq ha hx]
  exact sub_le_sub_left (scalarPotential_mono_coordinate ha.le hx.le hxy) a

theorem scalarPotential_deriv_sq_bound {a x y : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxy : x ≤ y) :
    -8 * (scalarOptimizer a x * scalarXi a x) / y ≤
      2 * deriv (scalarPotential a) y * deriv (deriv (scalarPotential a)) y := by
  have hy := hx.trans_le hxy
  have hd := scalarOptimizer_pos ha hy
  have hc := (le_div_iff₀ (sq_pos_of_pos hy)).mp (scalarPotential_curvature_le_xi ha hy)
  have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hd.le)
  have ht := scalarOptimizer_mul_scalarXi_antitone ha hx hxy
  apply (div_le_iff₀ hy).mpr
  rw [(scalarPotential_hasDerivAt ha hy).deriv]
  nlinarith

theorem scalarPotential_deriv_sq_log {a x y : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxy : x ≤ y) :
    (deriv (scalarPotential a) x) ^ 2 - (deriv (scalarPotential a) y) ^ 2 ≤
      8 * (scalarOptimizer a x * scalarXi a x) * Real.log (y / x) := by
  let C := 8 * (scalarOptimizer a x * scalarXi a x)
  let H := fun z : ℝ ↦ (deriv (scalarPotential a) z) ^ 2 + C * Real.log z
  have hd : ∀ z ∈ Ici x, HasDerivAt H
      (2 * deriv (scalarPotential a) z * deriv (deriv (scalarPotential a)) z + C / z) z := by
    intro z hz
    have hp := hx.trans_le hz
    have h₁ := (scalarPotential_deriv_hasDerivAt ha hp).differentiableAt.hasDerivAt
    have h₂ := (Real.hasDerivAt_log hp.ne').const_mul C
    convert (h₁.pow 2).add h₂ using 1
    simp [pow_one, div_eq_mul_inv]
  have hm : MonotoneOn H (Ici x) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici x)
      (fun z hz ↦ (hd z hz).continuousAt.continuousWithinAt)
      (fun z hz ↦ (hd z (interior_subset hz)).differentiableAt.differentiableWithinAt)
    intro z hz
    rw [(hd z (interior_subset hz)).deriv]
    have hb := scalarPotential_deriv_sq_bound ha hx (interior_subset hz)
    dsimp [C]
    rw [neg_mul, neg_div] at hb
    linarith
  have hb := hm (show x ∈ Ici x by simp) (show y ∈ Ici x from hxy) hxy
  dsimp [H, C] at hb
  rw [Real.log_div (hx.trans_le hxy).ne' hx.ne']
  nlinarith

theorem scalarPotential_deriv_antitoneOn {a : ℝ} (ha : 0 < a) :
    AntitoneOn (deriv (scalarPotential a)) (Ioi 0) := by
  apply ((scalarPotential_strictConcaveOn ha).concaveOn.subset
    Ioi_subset_Ici_self (convex_Ioi 0)).antitoneOn_deriv
  exact fun _ hx ↦ (scalarPotential_hasDerivAt ha hx).differentiableAt

theorem scalarPotential_deriv_log {a x y : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hxy : x ≤ y) :
    x * (deriv (scalarPotential a) x - deriv (scalarPotential a) y) ≤
      4 * scalarXi a x * Real.log (y / x) := by
  have hy := hx.trans_le hxy
  have hd := scalarOptimizer_pos ha hx
  have hp := (scalarPotential_hasDerivAt ha hx).deriv
  have hq : 0 ≤ deriv (scalarPotential a) y := by
    rw [(scalarPotential_hasDerivAt ha hy).deriv]
    exact mul_nonneg (mul_nonneg zero_le_two (scalarOptimizer_pos ha hy).le) hy.le
  have hm := scalarPotential_deriv_antitoneOn ha hx hy hxy
  have hs := scalarPotential_deriv_sq_log ha hx hxy
  have hn := mul_nonneg hq (sub_nonneg.mpr hm)
  apply (mul_le_mul_iff_right₀ (mul_pos zero_lt_two hd)).mp
  rw [hp] at hs hn ⊢
  nlinarith only [hs, hn]

theorem scalarPotential_tangent_loss {a x r : ℝ} (ha : 0 < a) (hx : 0 < x)
    (hr : 1 ≤ r) :
    scalarPotential a x + deriv (scalarPotential a) x * (r * x - x) -
      scalarPotential a (r * x) ≤ 4 * scalarXi a x * (r - 1) * Real.log r := by
  have hxy : x ≤ r * x := by nlinarith
  have ht := scalarPotential_tangent_nonneg ha (hx.trans_le hxy) hx.le
  have hd := scalarPotential_deriv_log ha hx hxy
  rw [mul_div_cancel_right₀ r hx.ne'] at hd
  have hm := mul_le_mul_of_nonneg_left hd (sub_nonneg.mpr hr)
  nlinarith only [ht, hm]

theorem scalarPotential_tangent_loss_zero (a x : ℝ) :
    scalarPotential a x + deriv (scalarPotential a) x * (0 - x) -
      scalarPotential a 0 = scalarXi a x := by
  rw [scalarPotential_zero, scalarXi]
  ring

end Cliquefree
