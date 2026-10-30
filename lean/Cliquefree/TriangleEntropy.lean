module
public import Cliquefree.FiniteLaw

/-! # Entropy and total variation for finite probability laws -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

/-- Total variation distance between two finite laws. -/
def FiniteLaw.totalVariation (μ ν : FiniteLaw Ω) : ℝ :=
  (∑ y, |μ.mass y - ν.mass y|) / 2

/-- Relative entropy; domination is assumed separately in inequalities involving this definition. -/
def FiniteLaw.relativeEntropy (μ ν : FiniteLaw Ω) : ℝ :=
  ∑ y, μ.mass y * Real.log (μ.mass y / ν.mass y)

/-- Entropy relative to positive reference masses, which need not sum to one. -/
def FiniteLaw.referenceEntropy (μ : FiniteLaw Ω) (r : Ω → ℝ) : ℝ :=
  ∑ y, μ.mass y * Real.log (r y / μ.mass y)

/-- Mix finite laws using another finite law as the distribution of the branch. -/
def FiniteLaw.kernelMix (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) : FiniteLaw Ξ where
  mass y := ∑ z, μ.mass z * (K z).mass y
  nonneg y := Finset.sum_nonneg (fun z _ ↦ mul_nonneg (μ.nonneg z) ((K z).nonneg y))
  sum_mass := by
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, FiniteLaw.sum_mass, mul_one]

theorem FiniteLaw.kernelMix_pos (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    {z : Ω} (hz : 0 < μ.mass z) {y : Ξ} (hy : 0 < (K z).mass y) :
    0 < (μ.kernelMix K).mass y := by
  apply (mul_pos hz hy).trans_le
  exact Finset.single_le_sum
    (fun i (_ : i ∈ Finset.univ) ↦ mul_nonneg (μ.nonneg i) ((K i).nonneg y))
    (Finset.mem_univ z)

theorem sub_le_mul_log_div {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxy : 0 < x → 0 < y) : x - y ≤ x * Real.log (x / y) := by
  by_cases hx₀ : x = 0
  · simp only [hx₀, zero_sub, zero_mul]
    exact neg_nonpos.mpr hy
  have hx' := lt_of_le_of_ne hx (Ne.symm hx₀)
  have hy' := hxy hx'
  have hl := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hy' hx')) hx
  have he : x * (y / x - 1) = y - x := by field_simp
  rw [he, Real.log_div hy'.ne' hx₀] at hl
  rw [Real.log_div hx₀ hy'.ne']
  nlinarith only [hl]

theorem FiniteLaw.relativeEntropy_nonneg (μ ν : FiniteLaw Ω)
    (hdom : ∀ y, 0 < μ.mass y → 0 < ν.mass y) : 0 ≤ μ.relativeEntropy ν := by
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun y _ ↦ sub_le_mul_log_div (μ.nonneg y) (ν.nonneg y) (hdom y))
  simpa only [FiniteLaw.relativeEntropy, Finset.sum_sub_distrib, μ.sum_mass, ν.sum_mass,
    sub_self] using hsum

theorem FiniteLaw.referenceEntropy_kernelMix (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    {r : Ξ → ℝ} (hr : ∀ y, 0 < r y) :
    (μ.kernelMix K).referenceEntropy r =
      μ.expectation (fun z ↦ (K z).referenceEntropy r) +
      μ.expectation (fun z ↦ (K z).relativeEntropy (μ.kernelMix K)) := by
  unfold referenceEntropy relativeEntropy expectation
  rw [← Finset.sum_add_distrib]
  simp_rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  change (∑ z, μ.mass z * (K z).mass y) * Real.log (r y / (μ.kernelMix K).mass y) = _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hz : μ.mass z = 0
  · simp [hz]
  by_cases hy : (K z).mass y = 0
  · simp [hy]
  have hz' : 0 < μ.mass z := lt_of_le_of_ne (μ.nonneg z) (Ne.symm hz)
  have hy' : 0 < (K z).mass y := lt_of_le_of_ne ((K z).nonneg y) (Ne.symm hy)
  have hm := μ.kernelMix_pos K hz' hy'
  rw [Real.log_div (hr y).ne' hm.ne', Real.log_div (hr y).ne' hy,
    Real.log_div hy hm.ne']
  ring

theorem FiniteLaw.referenceEntropy_increment (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    {r : Ξ → ℝ} (hr : ∀ y, 0 < r y) :
    (μ.kernelMix K).referenceEntropy r - μ.expectation (fun z ↦ (K z).referenceEntropy r) =
      μ.expectation (fun z ↦ (K z).relativeEntropy (μ.kernelMix K)) := by
  rw [μ.referenceEntropy_kernelMix K hr]
  ring

theorem FiniteLaw.referenceEntropy_kernelMix_ge (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ)
    {r : Ξ → ℝ} (hr : ∀ y, 0 < r y) :
    μ.expectation (fun z ↦ (K z).referenceEntropy r) ≤ (μ.kernelMix K).referenceEntropy r := by
  have hh := μ.expectation_mono_support (X := fun _ ↦ 0)
    (Y := fun z ↦ (K z).relativeEntropy (μ.kernelMix K)) (fun z hz ↦
      (K z).relativeEntropy_nonneg (μ.kernelMix K) (fun _ hy ↦ μ.kernelMix_pos K hz hy))
  rw [μ.expectation_const] at hh
  rw [μ.referenceEntropy_kernelMix K hr]
  linarith only [hh]

theorem FiniteLaw.totalVariation_nonneg (μ ν : FiniteLaw Ω) : 0 ≤ μ.totalVariation ν :=
  div_nonneg (Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)) (by norm_num)

theorem FiniteLaw.totalVariation_triangle (μ ν ρ : FiniteLaw Ω) :
    μ.totalVariation ρ ≤ μ.totalVariation ν + ν.totalVariation ρ := by
  unfold totalVariation
  rw [← add_div]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro y _
  exact abs_sub_le (μ.mass y) (ν.mass y) (ρ.mass y)

omit [Fintype Ω] in
/-- The finite log-sum inequality, including zero numerator masses. -/
theorem sum_mul_log_div_ge (s : Finset Ω) {x y : Ω → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hy : ∀ i ∈ s, 0 ≤ y i)
    (hdom : ∀ i ∈ s, 0 < x i → 0 < y i) :
    (∑ i ∈ s, x i) * Real.log ((∑ i ∈ s, x i) / ∑ i ∈ s, y i) ≤
      ∑ i ∈ s, x i * Real.log (x i / y i) := by
  classical
  let X := ∑ i ∈ s, x i
  let Y := ∑ i ∈ s, y i
  have hX : 0 ≤ X := Finset.sum_nonneg hx
  by_cases hX₀ : X = 0
  · have hz : ∀ i ∈ s, x i = 0 := by
      intro i hi
      have hh := Finset.single_le_sum hx hi
      change x i ≤ X at hh
      linarith [hx i hi]
    simp only [show (∑ i ∈ s, x i) = 0 from hX₀, zero_mul]
    exact Finset.sum_nonneg (fun i hi ↦ by simp only [hz i hi, zero_mul]; rfl)
  have hX' : 0 < X := lt_of_le_of_ne hX (Ne.symm hX₀)
  have hY : 0 < Y := by
    obtain ⟨i, hi, hx'⟩ := (Finset.sum_pos_iff_of_nonneg hx).mp hX'
    exact (hdom i hi hx').trans_le (Finset.single_le_sum hy hi)
  let c := X / Y
  have hc : 0 < c := div_pos hX' hY
  have hp : ∀ i ∈ s, x i - c * y i ≤
      x i * Real.log (x i / y i) - x i * Real.log c := by
    intro i hi
    have hb := sub_le_mul_log_div (hx i hi) (mul_nonneg hc.le (hy i hi))
      (fun hxi ↦ mul_pos hc (hdom i hi hxi))
    by_cases hxi : x i = 0
    · simpa only [hxi, zero_sub, zero_mul, sub_zero] using hb
    have hx' := lt_of_le_of_ne (hx i hi) (Ne.symm hxi)
    have hy' := hdom i hi hx'
    have he : x i * Real.log (x i / (c * y i)) =
        x i * Real.log (x i / y i) - x i * Real.log c := by
      rw [Real.log_div hxi (mul_pos hc hy').ne', Real.log_mul hc.ne' hy'.ne',
        Real.log_div hxi hy'.ne']
      ring
    rwa [he] at hb
  have hs := Finset.sum_le_sum hp
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib,
    ← Finset.sum_mul] at hs
  have he : X - c * Y = 0 := by dsimp [c]; field_simp; ring
  change X - c * Y ≤ (∑ i ∈ s, x i * Real.log (x i / y i)) - X * Real.log c at hs
  rw [he] at hs
  exact sub_nonneg.mp hs

theorem FiniteLaw.referenceEntropy_le_log_sum (μ : FiniteLaw Ω) {r : Ω → ℝ}
    (hr : ∀ y, 0 < r y) : μ.referenceEntropy r ≤ Real.log (∑ y, r y) := by
  have hh := sum_mul_log_div_ge Finset.univ (fun y _ ↦ μ.nonneg y)
    (fun y _ ↦ (hr y).le) (fun y _ _ ↦ hr y)
  have he (y : Ω) : μ.mass y * Real.log (μ.mass y / r y) =
      -(μ.mass y * Real.log (r y / μ.mass y)) := by
    rw [← inv_div (r y) (μ.mass y), Real.log_inv]
    ring
  simp_rw [he] at hh
  rw [μ.sum_mass, one_mul, one_div, Real.log_inv, Finset.sum_neg_distrib] at hh
  exact neg_le_neg_iff.mp hh

omit [Fintype Ω] in
/-- The entropy contribution of a set is bounded by its total probability and reference mass. -/
theorem sum_mul_log_div_le (s : Finset Ω) {x r : Ω → ℝ}
    (hx : ∀ i ∈ s, 0 ≤ x i) (hr : ∀ i ∈ s, 0 ≤ r i)
    (hdom : ∀ i ∈ s, 0 < x i → 0 < r i) :
    (∑ i ∈ s, x i * Real.log (r i / x i)) ≤
      (∑ i ∈ s, x i) * Real.log ((∑ i ∈ s, r i) / ∑ i ∈ s, x i) := by
  have hh := sum_mul_log_div_ge s hx hr hdom
  have he (i : Ω) : x i * Real.log (x i / r i) = -(x i * Real.log (r i / x i)) := by
    rw [← inv_div (r i) (x i), Real.log_inv]
    ring
  simp_rw [he] at hh
  rw [Finset.sum_neg_distrib, ← inv_div (∑ i ∈ s, r i) (∑ i ∈ s, x i),
    Real.log_inv, mul_neg] at hh
  exact neg_le_neg_iff.mp hh

theorem FiniteLaw.referenceEntropy_density_lower (μ : FiniteLaw Ω) {r : Ω → ℝ}
    (hr : ∀ y, 0 < r y) {t : ℝ} (ht : 0 < t) (hd : ∀ y, μ.mass y ≤ t * r y) :
    -Real.log t ≤ μ.referenceEntropy r := by
  have hp (y : Ω) : μ.mass y * (-Real.log t) ≤
      μ.mass y * Real.log (r y / μ.mass y) := by
    by_cases hy : μ.mass y = 0
    · simp only [hy, zero_mul, le_refl]
    have hy' := lt_of_le_of_ne (μ.nonneg y) (Ne.symm hy)
    have hratio : 1 / t ≤ r y / μ.mass y := by
      apply (div_le_div_iff₀ ht hy').mpr
      simpa only [one_mul, mul_comm] using hd y
    have hl := (Real.log_le_log_iff (div_pos zero_lt_one ht) (div_pos (hr y) hy')).mpr hratio
    rw [one_div, Real.log_inv] at hl
    exact mul_le_mul_of_nonneg_left hl (μ.nonneg y)
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun y _ ↦ hp y)
  rw [← Finset.sum_mul, μ.sum_mass, one_mul] at hs
  exact hs

end Cliquefree
