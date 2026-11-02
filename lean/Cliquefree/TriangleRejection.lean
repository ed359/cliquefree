module

public import Cliquefree.TriangleEntropy
public import Cliquefree.TriangleScales

/-!
# Reversible incidence rejection

Reverse transition densities turn the reference entropy into a Markov bound on rejected
directed incidences.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {Ω : Type*} [Fintype Ω]

/-- Reversibility identifies the mean reverse log density with the ordinary reference entropy. -/
theorem reversible_reverse_entropy (π : FiniteLaw Ω) (K : Ω → FiniteLaw Ω) (r : Ω → ℝ)
    (hrev : ∀ x y, π.mass x * (K x).mass y = π.mass y * (K y).mass x) :
    π.expectation (fun x ↦ (K x).expectation
      (fun y ↦ Real.log (r x / (K y).mass x))) =
      π.expectation (fun x ↦ (K x).referenceEntropy r) := by
  simp only [FiniteLaw.expectation, FiniteLaw.referenceEntropy, Finset.mul_sum, ← mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [hrev y x]

/-- A positive transition density bounded by a reference mass has a lower log-density bound. -/
theorem reverse_log_density_lower {p r t : ℝ} (hp : 0 < p) (hr : 0 < r)
    (ht : 0 < t) (hd : p ≤ t * r) :
    -Real.log t ≤ Real.log (r / p) := by
  have h := Real.log_le_log hp hd
  rw [Real.log_mul ht.ne' hr.ne'] at h
  rw [Real.log_div hr.ne' hp.ne']
  linarith

/-- A reversible density test is controlled by the shifted mean reference entropy. -/
theorem reversible_rejection_markov (π : FiniteLaw Ω) (K : Ω → FiniteLaw Ω)
    (hπ : ∀ x, 0 < π.mass x)
    (hrev : ∀ x y, π.mass x * (K x).mass y = π.mass y * (K y).mass x)
    {r : Ω → ℝ} (hr : ∀ x, 0 < r x) {t S : ℝ} (ht : 0 < t) (hS : 0 < S)
    (hd : ∀ x y, (K x).mass y ≤ t * r y) :
    (Real.log S + Real.log t) *
      π.expectation (fun x ↦ (K x).expectation
        (fun y ↦ if (K y).mass x < r x / S then 1 else 0)) ≤
      π.expectation (fun x ↦ (K x).referenceEntropy r) + Real.log t := by
  classical
  have hpoint (x y : Ω) :
      (K x).mass y * ((Real.log S + Real.log t) *
        (if (K y).mass x < r x / S then 1 else 0)) ≤
      (K x).mass y * (Real.log (r x / (K y).mass x) + Real.log t) := by
    by_cases hz : (K x).mass y = 0
    · simp [hz]
    have hk : 0 < (K x).mass y := lt_of_le_of_ne ((K x).nonneg y) (Ne.symm hz)
    have hkr : 0 < (K y).mass x := by
      have h := hrev x y
      have hmul := mul_pos (hπ x) hk
      rw [h] at hmul
      exact (mul_pos_iff_of_pos_left (hπ y)).mp hmul
    apply mul_le_mul_of_nonneg_left _ hk.le
    have hlower := reverse_log_density_lower hkr (hr x) ht (hd y x)
    by_cases hbad : (K y).mass x < r x / S
    · simp only [hbad, ite_true, mul_one]
      have hlog := Real.log_le_log hkr hbad.le
      rw [Real.log_div (hr x).ne' hS.ne'] at hlog
      rw [Real.log_div (hr x).ne' hkr.ne']
      linarith
    · simp only [hbad, ite_false, mul_zero]
      linarith
  have hrow (x : Ω) :
      (K x).expectation (fun y ↦ (Real.log S + Real.log t) *
        (if (K y).mass x < r x / S then 1 else 0)) ≤
      (K x).expectation (fun y ↦ Real.log (r x / (K y).mass x) + Real.log t) :=
    Finset.sum_le_sum (fun y _ ↦ hpoint x y)
  have h := π.expectation_mono_support (fun x _ ↦ hrow x)
  simp_rw [FiniteLaw.expectation_smul, FiniteLaw.expectation_add,
    FiniteLaw.expectation_const] at h
  rw [reversible_reverse_entropy π K r hrev] at h
  exact h

/-- Rejection averaging over a finite family of reversible kernels preserves the entropy bound. -/
theorem family_rejection_bound {I : Type*} [Fintype I] {E : I → Type*}
    [∀ i, Fintype (E i)] (μ : FiniteLaw I) (π : ∀ i, FiniteLaw (E i))
    (K : ∀ i, E i → FiniteLaw (E i)) (hπ : ∀ i x, 0 < (π i).mass x)
    (hrev : ∀ i x y, (π i).mass x * (K i x).mass y = (π i).mass y * (K i y).mass x)
    {r : ∀ i, E i → ℝ} (hr : ∀ i x, 0 < r i x) {t S : ℝ}
    (ht : 0 < t) (hS : 0 < S) (hden : 0 < Real.log S + Real.log t)
    (hd : ∀ i x y, (K i x).mass y ≤ t * r i y) :
    μ.expectation (fun i ↦ (π i).expectation (fun x ↦ (K i x).expectation
      (fun y ↦ if (K i y).mass x < r i x / S then 1 else 0))) ≤
      (μ.expectation (fun i ↦ (π i).expectation
        (fun x ↦ (K i x).referenceEntropy (r i))) + Real.log t) /
          (Real.log S + Real.log t) := by
  have h := μ.expectation_mono_support (fun i _ ↦
    reversible_rejection_markov (π i) (K i) (hπ i) (hrev i) (hr i) ht hS (hd i))
  simp_rw [FiniteLaw.expectation_smul, FiniteLaw.expectation_add,
    FiniteLaw.expectation_const] at h
  apply (le_div_iff₀ hden).mpr
  simpa only [mul_comm] using h

/-- The dyadic retained-load threshold supplies the square-root denominator in rejection bounds. -/
theorem triangle_rejection_denominator_lower {t : ℕ} (ht : 32 ≤ t) :
    Real.sqrt (t : ℝ) / 2 ≤
      Real.log ((2 : ℝ) ^ nextTriangleScale t) + Real.log (t : ℝ) := by
  have hceil : Real.sqrt (t : ℝ) ≤ (nextTriangleScale t : ℝ) := Nat.le_ceil _
  have hlog₂ : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlogt : 0 ≤ Real.log (t : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
  rw [Real.log_pow]
  have h := mul_le_mul_of_nonneg_right hceil (le_trans (by norm_num) hlog₂)
  have h' := mul_le_mul_of_nonneg_left hlog₂ (Real.sqrt_nonneg (t : ℝ))
  nlinarith

/-- An upper entropy budget gives an explicit incidence rejection estimate. -/
theorem triangle_rejection_ratio_le {t : ℕ} (ht : 32 ≤ t) {H : ℝ}
    (hH : H ≤ (witnessA : ℝ) * Real.log (t : ℝ)) :
    (H + Real.log (t : ℝ)) /
      (Real.log ((2 : ℝ) ^ nextTriangleScale t) + Real.log (t : ℝ)) ≤
        2 * ((witnessA : ℝ) + 1) * Real.log (t : ℝ) / Real.sqrt (t : ℝ) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hr := Real.sqrt_pos.mpr htpos
  have hd := triangle_rejection_denominator_lower ht
  have hden : 0 < Real.log ((2 : ℝ) ^ nextTriangleScale t) + Real.log (t : ℝ) :=
    lt_of_lt_of_le (by positivity) hd
  have hlogt : 0 ≤ Real.log (t : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
  calc
    _ ≤ (((witnessA : ℝ) + 1) * Real.log (t : ℝ)) /
        (Real.log ((2 : ℝ) ^ nextTriangleScale t) + Real.log (t : ℝ)) := by
      apply div_le_div_of_nonneg_right _ hden.le
      nlinarith only [hH]
    _ ≤ (((witnessA : ℝ) + 1) * Real.log (t : ℝ)) / (Real.sqrt (t : ℝ) / 2) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hd
    _ = _ := by ring

end Cliquefree
