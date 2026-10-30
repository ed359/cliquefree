module
public import Cliquefree.TriangleEntropy

/-! # Pinsker's inequality for finite probability laws -/

@[expose] public section

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace Cliquefree

/-- Subtracting the quadratic strong-convexity term from negative binary entropy. -/
def binaryEntropyQuadratic (p : ℝ) : ℝ := -Real.binEntropy p - 2 * p ^ 2

theorem binaryEntropyQuadratic_hasDerivAt {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    HasDerivAt binaryEntropyQuadratic (Real.log p - Real.log (1 - p) - 4 * p) p := by
  have he := (Real.hasDerivAt_binEntropy hp₀.ne' (ne_of_lt hp₁)).neg
  convert he.sub (((hasDerivAt_id' p).pow 2).const_mul 2) using 1 <;>
    first | rfl | ring

theorem binaryEntropyQuadratic_deriv_hasDerivAt {p : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1) :
    HasDerivAt (deriv binaryEntropyQuadratic) (1 / (p * (1 - p)) - 4) p := by
  have h₁ := Real.hasDerivAt_log hp₀.ne'
  have h₂ := ((hasDerivAt_const p (1 : ℝ)).sub (hasDerivAt_id' p)).log
    (sub_pos.mpr hp₁).ne'
  have hh := (h₁.sub h₂).sub ((hasDerivAt_id' p).const_mul 4)
  have he : deriv binaryEntropyQuadratic =ᶠ[𝓝 p]
      (fun y : ℝ ↦ Real.log y - Real.log (1 - y) - 4 * y) := by
    filter_upwards [Ioo_mem_nhds hp₀ hp₁] with y hy
    exact (binaryEntropyQuadratic_hasDerivAt hy.1 hy.2).deriv
  have hraw : HasDerivAt (fun y : ℝ ↦ Real.log y - Real.log (1 - y) - 4 * y)
      (1 / (p * (1 - p)) - 4) p := by
    simp only [Pi.sub_apply] at hh
    convert hh using 1
    field_simp [hp₀.ne', (sub_pos.mpr hp₁).ne']
    ring
  exact hraw.congr_of_eventuallyEq he

theorem binaryEntropyQuadratic_convexOn : ConvexOn ℝ (Icc 0 1) binaryEntropyQuadratic := by
  apply convexOn_of_deriv2_nonneg (convex_Icc 0 1)
  · unfold binaryEntropyQuadratic
    fun_prop
  · intro p hp
    rw [interior_Icc] at hp
    exact (binaryEntropyQuadratic_hasDerivAt hp.1 hp.2).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    exact
      (binaryEntropyQuadratic_deriv_hasDerivAt hp.1 hp.2).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    change 0 ≤ deriv (deriv binaryEntropyQuadratic) p
    rw [(binaryEntropyQuadratic_deriv_hasDerivAt hp.1 hp.2).deriv]
    have hden : 0 < p * (1 - p) := mul_pos hp.1 (sub_pos.mpr hp.2)
    have hbound : 4 ≤ 1 / (p * (1 - p)) := by
      apply (le_div_iff₀ hden).mpr
      nlinarith [sq_nonneg (p - 1 / 2)]
    linarith only [hbound]

theorem binaryEntropyQuadratic_tangent {p q : ℝ} (hp : p ∈ Icc 0 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    binaryEntropyQuadratic q + (Real.log q - Real.log (1 - q) - 4 * q) * (p - q) ≤
      binaryEntropyQuadratic p := by
  have hf := (binaryEntropyQuadratic_hasDerivAt hq₀ hq₁).differentiableAt
  have hq : q ∈ Icc (0 : ℝ) 1 := ⟨hq₀.le, hq₁.le⟩
  rcases lt_trichotomy q p with h | rfl | h
  · have hs := binaryEntropyQuadratic_convexOn.deriv_le_slope hq hp h hf
    rw [(binaryEntropyQuadratic_hasDerivAt hq₀ hq₁).deriv, slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr h)).mp hs
    linarith only [hm]
  · simp
  · have hs := binaryEntropyQuadratic_convexOn.slope_le_deriv hp hq h hf
    rw [(binaryEntropyQuadratic_hasDerivAt hq₀ hq₁).deriv, slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr h)).mp hs
    nlinarith only [hm]

theorem binary_entropy_pinsker {p q : ℝ} (hp : p ∈ Icc 0 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    2 * (p - q) ^ 2 ≤ -Real.binEntropy p - p * Real.log q -
      (1 - p) * Real.log (1 - q) := by
  have ht := binaryEntropyQuadratic_tangent hp hq₀ hq₁
  have he : Real.binEntropy q = -q * Real.log q - (1 - q) * Real.log (1 - q) := by
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def]
    ring
  unfold binaryEntropyQuadratic at ht
  rw [he] at ht
  nlinarith only [ht]

theorem binary_relativeEntropy_pinsker {p q : ℝ} (hp : p ∈ Icc 0 1)
    (hq₀ : 0 < q) (hq₁ : q < 1) :
    2 * (p - q) ^ 2 ≤ p * Real.log (p / q) +
      (1 - p) * Real.log ((1 - p) / (1 - q)) := by
  have he (x y : ℝ) (hy : y ≠ 0) :
      x * Real.log (x / y) = x * Real.log x - x * Real.log y := by
    by_cases hx : x = 0
    · simp only [hx, zero_mul, sub_self]
    rw [Real.log_div hx hy]
    ring
  rw [he p q hq₀.ne', he (1 - p) (1 - q) (sub_pos.mpr hq₁).ne']
  have hh := binary_entropy_pinsker hp hq₀ hq₁
  rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def] at hh
  nlinarith only [hh]

variable {Ω : Type*} [Fintype Ω]

/-- Coordinates where the first probability law has greater mass than the second. -/
def FiniteLaw.positiveDifference (μ ν : FiniteLaw Ω) : Finset Ω := by
  classical
  exact Finset.univ.filter (fun y ↦ ν.mass y < μ.mass y)

@[simp] theorem FiniteLaw.mem_positiveDifference (μ ν : FiniteLaw Ω) (y : Ω) :
    y ∈ μ.positiveDifference ν ↔ ν.mass y < μ.mass y := by
  classical
  simp [positiveDifference]

theorem FiniteLaw.totalVariation_eq_sub (μ ν : FiniteLaw Ω) :
    μ.totalVariation ν = (∑ y ∈ μ.positiveDifference ν, μ.mass y) -
      ∑ y ∈ μ.positiveDifference ν, ν.mass y := by
  classical
  have he (y : Ω) : |μ.mass y - ν.mass y| =
      2 * (if y ∈ μ.positiveDifference ν then μ.mass y - ν.mass y else 0) -
        (μ.mass y - ν.mass y) := by
    by_cases hy : y ∈ μ.positiveDifference ν
    · rw [ite_eq_left hy, abs_of_pos (sub_pos.mpr ((μ.mem_positiveDifference ν y).mp hy))]
      ring
    · rw [ite_eq_right hy, abs_of_nonpos (sub_nonpos.mpr
        (not_lt.mp ((μ.mem_positiveDifference ν y).not.mp hy)))]
      ring
  unfold totalVariation
  simp_rw [he]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_mem_eq,
    Finset.sum_sub_distrib, Finset.sum_sub_distrib, μ.sum_mass, ν.sum_mass]
  ring

theorem FiniteLaw.relativeEntropy_ge_binary (μ ν : FiniteLaw Ω)
    (hdom : ∀ y, 0 < μ.mass y → 0 < ν.mass y) (S : Finset Ω) :
    (∑ y ∈ S, μ.mass y) * Real.log ((∑ y ∈ S, μ.mass y) / ∑ y ∈ S, ν.mass y) +
      (1 - ∑ y ∈ S, μ.mass y) *
        Real.log ((1 - ∑ y ∈ S, μ.mass y) / (1 - ∑ y ∈ S, ν.mass y)) ≤
      μ.relativeEntropy ν := by
  classical
  have h₁ := sum_mul_log_div_ge S (fun y _ ↦ μ.nonneg y) (fun y _ ↦ ν.nonneg y)
    (fun y _ ↦ hdom y)
  have h₂ := sum_mul_log_div_ge Sᶜ (fun y _ ↦ μ.nonneg y) (fun y _ ↦ ν.nonneg y)
    (fun y _ ↦ hdom y)
  have hμ : (∑ y ∈ Sᶜ, μ.mass y) = 1 - ∑ y ∈ S, μ.mass y := by
    have h := Finset.sum_add_sum_compl S μ.mass
    rw [μ.sum_mass] at h
    linarith only [h]
  have hν : (∑ y ∈ Sᶜ, ν.mass y) = 1 - ∑ y ∈ S, ν.mass y := by
    have h := Finset.sum_add_sum_compl S ν.mass
    rw [ν.sum_mass] at h
    linarith only [h]
  rw [hμ, hν] at h₂
  unfold relativeEntropy
  rw [← Finset.sum_add_sum_compl S]
  exact add_le_add h₁ h₂

/-- Pinsker's inequality with the sharp universal constant for natural logarithms. -/
theorem FiniteLaw.pinsker_sq (μ ν : FiniteLaw Ω)
    (hdom : ∀ y, 0 < μ.mass y → 0 < ν.mass y) :
    μ.totalVariation ν ^ 2 ≤ μ.relativeEntropy ν / 2 := by
  classical
  have hTV := μ.totalVariation_nonneg ν
  by_cases hz : μ.totalVariation ν = 0
  · rw [hz, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact div_nonneg (μ.relativeEntropy_nonneg ν hdom) (by norm_num)
  have hTV' : 0 < μ.totalVariation ν := lt_of_le_of_ne hTV (Ne.symm hz)
  let S := μ.positiveDifference ν
  let p := ∑ y ∈ S, μ.mass y
  let q := ∑ y ∈ S, ν.mass y
  have he : μ.totalVariation ν = p - q := μ.totalVariation_eq_sub ν
  have hp₀ : 0 ≤ p := Finset.sum_nonneg (fun y _ ↦ μ.nonneg y)
  have hq₀ : 0 ≤ q := Finset.sum_nonneg (fun y _ ↦ ν.nonneg y)
  have hp₁ : p ≤ 1 := by
    have hh := Finset.sum_add_sum_compl S μ.mass
    rw [μ.sum_mass] at hh
    have hc : 0 ≤ ∑ y ∈ Sᶜ, μ.mass y := Finset.sum_nonneg (fun y _ ↦ μ.nonneg y)
    dsimp [p]
    linarith only [hh, hc]
  have hp' : 0 < p := by linarith only [he, hTV', hq₀]
  have hq' : 0 < q := by
    obtain ⟨y, hy, hym⟩ :=
      (Finset.sum_pos_iff_of_nonneg (fun y (_ : y ∈ S) ↦ μ.nonneg y)).mp hp'
    exact (hdom y hym).trans_le
      (Finset.single_le_sum (fun y (_ : y ∈ S) ↦ ν.nonneg y) hy)
  have hq₁ : q < 1 := by linarith only [he, hTV', hp₁]
  have hbin := binary_relativeEntropy_pinsker ⟨hp₀, hp₁⟩ hq' hq₁
  have hkl := μ.relativeEntropy_ge_binary ν hdom S
  change p * Real.log (p / q) + (1 - p) * Real.log ((1 - p) / (1 - q)) ≤
    μ.relativeEntropy ν at hkl
  have hb := hbin.trans hkl
  rw [he]
  linarith only [hb]

theorem FiniteLaw.sq_expectation_le (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    μ.expectation X ^ 2 ≤ μ.expectation (fun y ↦ X y ^ 2) := by
  have hn := μ.expectation_nonneg (fun y ↦ sq_nonneg (X y - μ.expectation X))
  have he : (fun y ↦ (X y - μ.expectation X) ^ 2) =
      (fun y ↦ X y ^ 2 - (2 * μ.expectation X) * X y + μ.expectation X ^ 2) := by
    funext y
    ring
  rw [he, μ.expectation_add, μ.expectation_sub, μ.expectation_smul,
    μ.expectation_const] at hn
  nlinarith only [hn]

theorem FiniteLaw.expected_pinsker {Ξ : Type*} [Fintype Ξ] (μ : FiniteLaw Ω)
    (P Q : Ω → FiniteLaw Ξ)
    (hdom : ∀ z, 0 < μ.mass z → ∀ y, 0 < (P z).mass y → 0 < (Q z).mass y) :
    μ.expectation (fun z ↦ (P z).totalVariation (Q z)) ≤
      Real.sqrt (μ.expectation (fun z ↦ (P z).relativeEntropy (Q z)) / 2) := by
  apply Real.le_sqrt_of_sq_le
  apply (μ.sq_expectation_le (fun z ↦ (P z).totalVariation (Q z))).trans
  have hh := μ.expectation_mono_support (fun z hz ↦ (P z).pinsker_sq (Q z) (hdom z hz))
  rw [μ.expectation_div] at hh
  exact hh

theorem FiniteLaw.totalVariation_comm (μ ν : FiniteLaw Ω) :
    μ.totalVariation ν = ν.totalVariation μ := by
  simp only [totalVariation, abs_sub_comm]

theorem FiniteLaw.nearby_rows_of_entropy_bounds {Ξ : Type*} [Fintype Ξ]
    (μ : FiniteLaw Ω) (P Q R : Ω → FiniteLaw Ξ) {δ : ℝ}
    (hPR : ∀ z, 0 < μ.mass z → ∀ y, 0 < (P z).mass y → 0 < (R z).mass y)
    (hQR : ∀ z, 0 < μ.mass z → ∀ y, 0 < (Q z).mass y → 0 < (R z).mass y)
    (hP : μ.expectation (fun z ↦ (P z).relativeEntropy (R z)) ≤ 2 * δ)
    (hQ : μ.expectation (fun z ↦ (Q z).relativeEntropy (R z)) ≤ 2 * δ) :
    μ.expectation (fun z ↦ (P z).totalVariation (Q z)) ≤ 2 * Real.sqrt δ := by
  have h₁ := (μ.expected_pinsker P R hPR).trans
    (Real.sqrt_le_sqrt (show μ.expectation (fun z ↦ (P z).relativeEntropy (R z)) / 2 ≤ δ by
      linarith only [hP]))
  have h₂ := (μ.expected_pinsker Q R hQR).trans
    (Real.sqrt_le_sqrt (show μ.expectation (fun z ↦ (Q z).relativeEntropy (R z)) / 2 ≤ δ by
      linarith only [hQ]))
  have ht := μ.expectation_mono_support (fun z (_ : 0 < μ.mass z) ↦
    show (P z).totalVariation (Q z) ≤ (P z).totalVariation (R z) +
      (Q z).totalVariation (R z) from by
        rw [(Q z).totalVariation_comm (R z)]
        exact (P z).totalVariation_triangle (R z) (Q z))
  rw [μ.expectation_add] at ht
  linarith only [ht, h₁, h₂]

end Cliquefree
