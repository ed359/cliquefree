module

public import Cliquefree.TriangleEntropy
public import Cliquefree.Constants

/-! # Entropy bounds from concentration on a set of small reference mass -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
/-- Entropy contributed by a subset is bounded using any upper bound for its reference mass. -/
theorem FiniteLaw.referenceEntropy_on_le (μ : FiniteLaw Ω) {r : Ω → ℝ}
    (hr : ∀ y, 0 < r y) (S : Finset Ω) {a : ℝ} (ha : 0 < a)
    (hSa : ∑ y ∈ S, r y ≤ a) :
    (∑ y ∈ S, μ.mass y * Real.log (r y / μ.mass y)) ≤
      (∑ y ∈ S, μ.mass y) * Real.log a -
        (∑ y ∈ S, μ.mass y) * Real.log (∑ y ∈ S, μ.mass y) := by
  have hbase := sum_mul_log_div_le S (fun y _ ↦ μ.nonneg y)
    (fun y _ ↦ (hr y).le) (fun y _ _ ↦ hr y)
  let m := ∑ y ∈ S, μ.mass y
  have hm : 0 ≤ m := Finset.sum_nonneg (fun y _ ↦ μ.nonneg y)
  by_cases hm₀ : m = 0
  · change (∑ y ∈ S, μ.mass y * Real.log (r y / μ.mass y)) ≤
      m * Real.log a - m * Real.log m
    change (∑ y ∈ S, μ.mass y * Real.log (r y / μ.mass y)) ≤
      m * Real.log ((∑ y ∈ S, r y) / m) at hbase
    simpa only [hm₀, zero_mul, sub_zero] using hbase
  have hm' : 0 < m := lt_of_le_of_ne hm (Ne.symm hm₀)
  have hA : 0 < ∑ y ∈ S, r y := by
    obtain ⟨y, hy, _⟩ := (Finset.sum_pos_iff_of_nonneg (fun y _ ↦ μ.nonneg y)).mp hm'
    exact (hr y).trans_le (Finset.single_le_sum (fun z _ ↦ (hr z).le) hy)
  calc
    _ ≤ m * Real.log ((∑ y ∈ S, r y) / m) := hbase
    _ ≤ m * Real.log (a / m) :=
      mul_le_mul_of_nonneg_left
        (Real.log_le_log (div_pos hA hm') (div_le_div_of_nonneg_right hSa hm)) hm
    _ = _ := by rw [Real.log_div ha.ne' hm₀]; ring

/-- Most probability on a set of small reference mass forces a small total reference entropy. -/
theorem FiniteLaw.referenceEntropy_concentration (μ : FiniteLaw Ω) {r : Ω → ℝ}
    (hr : ∀ y, 0 < r y) (S : Finset Ω) {a L ε : ℝ} (ha : 1 ≤ a) (hL : 1 ≤ L)
    (hSa : ∑ y ∈ S, r y ≤ a) (hSL : ∑ y, r y ≤ L)
    (hleak : ∑ y ∈ Sᶜ, μ.mass y ≤ ε) :
    μ.referenceEntropy r ≤ Real.log 2 + Real.log a + ε * Real.log L := by
  let m := ∑ y ∈ S, μ.mass y
  let c := ∑ y ∈ Sᶜ, μ.mass y
  have hm : 0 ≤ m := Finset.sum_nonneg (fun y _ ↦ μ.nonneg y)
  have hc : 0 ≤ c := Finset.sum_nonneg (fun y _ ↦ μ.nonneg y)
  have hmc : m + c = 1 := by
    dsimp [m, c]
    rw [Finset.sum_add_sum_compl, μ.sum_mass]
  have hm₁ : m ≤ 1 := by linarith only [hmc, hc]
  have hrC : ∑ y ∈ Sᶜ, r y ≤ L :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun y _ _ ↦ (hr y).le)).trans hSL
  have hfirst := μ.referenceEntropy_on_le hr S (lt_of_lt_of_le (by norm_num) ha) hSa
  have hsecond := μ.referenceEntropy_on_le hr Sᶜ (lt_of_lt_of_le (by norm_num) hL) hrC
  have htotal : μ.referenceEntropy r ≤
      m * Real.log a + c * Real.log L - m * Real.log m - c * Real.log c := by
    change _ ≤ m * Real.log a - m * Real.log m at hfirst
    change _ ≤ c * Real.log L - c * Real.log c at hsecond
    have h := add_le_add hfirst hsecond
    rw [Finset.sum_add_sum_compl] at h
    exact h.trans_eq (by ring)
  have hb : -m * Real.log m - c * Real.log c ≤ Real.log 2 := by
    have h : Real.binEntropy m ≤ Real.log 2 := Real.binEntropy_le_log_two
    rw [Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog_def,
      show 1 - m = c by linarith only [hmc]] at h
    linarith only [h]
  have ha' := mul_le_mul_of_nonneg_right hm₁ (Real.log_nonneg ha)
  have hL' := mul_le_mul_of_nonneg_right hleak (Real.log_nonneg hL)
  change c * Real.log L ≤ ε * Real.log L at hL'
  nlinarith only [htotal, hb, ha', hL']

omit [DecidableEq Ω] in
/-- A uniform bound on rare exceptional outcomes can be added to a bound elsewhere. -/
theorem FiniteLaw.expectation_le_exceptional (μ : FiniteLaw Ω) (S : Finset Ω)
    {X : Ω → ℝ} {B U γ : ℝ} (hB : 0 ≤ B) (hU : 0 ≤ U)
    (hgood : ∀ x, x ∉ S → X x ≤ B) (hall : ∀ x, X x ≤ U)
    (hS : ∑ x ∈ S, μ.mass x ≤ γ) : μ.expectation X ≤ B + γ * U := by
  classical
  have hp (x : Ω) : X x ≤ B + if x ∈ S then U else 0 := by
    by_cases hx : x ∈ S
    · simp only [hx, ite_true]
      exact (hall x).trans (by linarith only [hB])
    · simp only [hx, ite_false, add_zero]
      exact hgood x hx
  calc
    _ ≤ μ.expectation (fun x ↦ B + if x ∈ S then U else 0) :=
      μ.expectation_mono_support (fun x _ ↦ hp x)
    _ = B + (∑ x ∈ S, μ.mass x) * U := by
      rw [μ.expectation_add, μ.expectation_const]
      congr 1
      simp only [FiniteLaw.expectation, mul_ite, mul_zero]
      rw [Finset.sum_ite_mem_eq, Finset.sum_mul]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hS hU)

/-- The entropy bound for a nonexceptional row at time `t`. -/
theorem FiniteLaw.referenceEntropy_walk_concentration (μ : FiniteLaw Ω) {r : Ω → ℝ}
    (hr : ∀ y, 0 < r y) (S : Finset Ω) {t : ℕ} (ht : 1 ≤ t)
    (hSa : ∑ y ∈ S, r y ≤ (t : ℝ) ^ 10)
    (hSL : ∑ y, r y ≤ (2 : ℝ) ^ t)
    (hleak : ∑ y ∈ Sᶜ, μ.mass y ≤ 1 / (t : ℝ) ^ 3) :
    μ.referenceEntropy r ≤ Real.log 2 + 10 * Real.log t + 1 / (t : ℝ) ^ 2 := by
  have ht₁ : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have ht₀ : (0 : ℝ) < t := by linarith only [ht₁]
  have h := μ.referenceEntropy_concentration hr S (one_le_pow₀ ht₁)
    (one_le_pow₀ (by norm_num)) hSa hSL hleak
  rw [Real.log_pow, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  have htwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have htail : 1 / (t : ℝ) ^ 3 * ((t : ℝ) * Real.log 2) ≤ 1 / (t : ℝ) ^ 2 := by
    calc
      _ ≤ 1 / (t : ℝ) ^ 3 * ((t : ℝ) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left htwo ht₀.le) (by positivity)
      _ = _ := by field_simp
  exact h.trans (by linarith only [htail])

omit [DecidableEq Ω] in
/-- Total reference mass at most `2^t` bounds every row entropy by `t`. -/
theorem FiniteLaw.referenceEntropy_le_time (μ : FiniteLaw Ω) {r : Ω → ℝ}
    (hr : ∀ y, 0 < r y) (t : ℕ) (hSL : ∑ y, r y ≤ (2 : ℝ) ^ t) :
    μ.referenceEntropy r ≤ t := by
  have hsum : 0 < ∑ y, r y := by
    obtain ⟨y, _⟩ := μ.exists_pos_mass
    exact (hr y).trans_le (Finset.single_le_sum
      (fun z (_ : z ∈ Finset.univ) ↦ (hr z).le) (Finset.mem_univ y))
  have h := (μ.referenceEntropy_le_log_sum hr).trans (Real.log_le_log hsum hSL)
  rw [Real.log_pow] at h
  have htwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  exact h.trans (by simpa using mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg t))

/-- The explicit entropy coefficient absorbs the concentration and exceptional-row remainders. -/
theorem witness_entropy_numeric_bound {t : ℕ} (ht : 3 ≤ t) :
    Real.log 2 + 10 * Real.log t + 1 / (t : ℝ) ^ 2 +
      12 * (witnessC : ℝ) ^ 2 / (t : ℝ) ^ 5 ≤ (witnessA : ℝ) * Real.log t := by
  have ht₃ : (3 : ℝ) ≤ t := by exact_mod_cast ht
  have ht₁ : (1 : ℝ) ≤ t := by linarith only [ht₃]
  have ht₀ : (0 : ℝ) < t := by linarith only [ht₃]
  have hl : 1 ≤ Real.log t :=
    (Real.le_log_iff_exp_le ht₀).mpr (Real.exp_one_lt_three.le.trans ht₃)
  have htwo : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have h₂ : 1 / (t : ℝ) ^ 2 ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one (one_le_pow₀ ht₁ (n := 2))
  have h₅ : 1 / (t : ℝ) ^ 5 ≤ 1 := by
    simpa using one_div_le_one_div_of_le zero_lt_one (one_le_pow₀ ht₁ (n := 5))
  have hC := mul_le_mul_of_nonneg_left h₅ (show 0 ≤ 12 * (witnessC : ℝ) ^ 2 by positivity)
  have hClog := mul_le_mul_of_nonneg_left hl
    (show 0 ≤ 12 * (witnessC : ℝ) ^ 2 by positivity)
  unfold witnessA
  push_cast
  simp only [div_eq_mul_inv, one_mul, mul_one] at hC h₂ ⊢
  nlinarith only [hl, htwo, h₂, hC, hClog]

omit [DecidableEq Ω] in
/-- Exceptional-mass and leakage estimates give the explicit mean entropy bound. -/
theorem FiniteLaw.expected_referenceEntropy_walk {E : Ω → Type*}
    [∀ x, Fintype (E x)] [∀ x, DecidableEq (E x)]
    (ν : FiniteLaw Ω) (μ : ∀ x, FiniteLaw (E x)) (r : ∀ x, E x → ℝ)
    (hr : ∀ x y, 0 < r x y) (bad : Finset Ω) (S : ∀ x, Finset (E x))
    {t : ℕ} (ht : 3 ≤ t)
    (hSa : ∀ x, x ∉ bad → ∑ y ∈ S x, r x y ≤ (t : ℝ) ^ 10)
    (hSL : ∀ x, ∑ y, r x y ≤ (2 : ℝ) ^ t)
    (hleak : ∀ x, x ∉ bad → ∑ y ∈ (S x)ᶜ, (μ x).mass y ≤ 1 / (t : ℝ) ^ 3)
    (hbad : ∑ x ∈ bad, ν.mass x ≤ 12 * (witnessC : ℝ) ^ 2 / (t : ℝ) ^ 6) :
    ν.expectation (fun x ↦ (μ x).referenceEntropy (r x)) ≤
      (witnessA : ℝ) * Real.log t := by
  have ht₁ : 1 ≤ t := by omega
  have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have h := ν.expectation_le_exceptional bad
    (X := fun x ↦ (μ x).referenceEntropy (r x))
    (B := Real.log 2 + 10 * Real.log t + 1 / (t : ℝ) ^ 2)
    (U := (t : ℝ)) (by
      exact add_nonneg (add_nonneg (Real.log_nonneg (by norm_num))
        (mul_nonneg (by norm_num) (Real.log_nonneg (by exact_mod_cast ht₁)))) (by positivity))
    ht₀.le (fun x hx ↦ (μ x).referenceEntropy_walk_concentration
      (hr x) (S x) ht₁ (hSa x hx) (hSL x) (hleak x hx))
    (fun x ↦ (μ x).referenceEntropy_le_time (hr x) t (hSL x)) hbad
  apply h.trans
  convert witness_entropy_numeric_bound ht using 1
  congr 1
  field_simp

omit [DecidableEq Ω] in
/-- Uniform row densities bound reference entropy below after any finite averaging. -/
theorem FiniteLaw.expected_referenceEntropy_density_lower {E : Ω → Type*}
    [∀ x, Fintype (E x)] (ν : FiniteLaw Ω) (μ : ∀ x, FiniteLaw (E x))
    (r : ∀ x, E x → ℝ) (hr : ∀ x y, 0 < r x y) {t : ℝ} (ht : 0 < t)
    (hd : ∀ x y, (μ x).mass y ≤ t * r x y) :
    -Real.log t ≤ ν.expectation (fun x ↦ (μ x).referenceEntropy (r x)) := by
  calc
    _ = ν.expectation (fun _ ↦ -Real.log t) := (ν.expectation_const _).symm
    _ ≤ _ := ν.expectation_mono_support
      (fun x _ ↦ (μ x).referenceEntropy_density_lower (hr x) ht (hd x))

end Cliquefree
