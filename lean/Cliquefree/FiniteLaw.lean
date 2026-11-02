module

public import Mathlib

/-!
# Finite probability laws

Finite laws and their expectations support the triangle dichotomy and disjointification arguments.
Outcomes of positive mass represent the support; zero-mass outcomes are allowed in the sample space.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

/-- A probability law on a finite sample space, represented by its real point masses. -/
structure FiniteLaw (Ω : Type*) [Fintype Ω] where
  /-- The probability mass of an outcome. -/
  mass : Ω → ℝ
  /-- Point masses are nonnegative. -/
  nonneg : ∀ ω, 0 ≤ mass ω
  /-- The total probability is one. -/
  sum_mass : ∑ ω, mass ω = 1

variable {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]

/-- The expectation of a real observable is its probability-weighted finite sum. -/
def FiniteLaw.expectation (μ : FiniteLaw Ω) (X : Ω → ℝ) : ℝ :=
  ∑ ω, μ.mass ω * X ω

/-- A finite probability law always has an outcome of positive mass. -/
theorem FiniteLaw.exists_pos_mass (μ : FiniteLaw Ω) : ∃ ω, 0 < μ.mass ω := by
  by_contra! h
  have hsum : ∑ ω, μ.mass ω ≤ 0 := Finset.sum_nonpos (fun ω _ ↦ h ω)
  rw [μ.sum_mass] at hsum
  norm_num at hsum

/-- The expectation of a constant is that constant. -/
@[simp] theorem FiniteLaw.expectation_const (μ : FiniteLaw Ω) (c : ℝ) :
    μ.expectation (fun _ ↦ c) = c := by
  rw [FiniteLaw.expectation, ← Finset.sum_mul, μ.sum_mass, one_mul]

/-- Expectation is additive in its observable. -/
theorem FiniteLaw.expectation_add (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    μ.expectation (fun ω ↦ X ω + Y ω) = μ.expectation X + μ.expectation Y := by
  simp only [FiniteLaw.expectation, mul_add, Finset.sum_add_distrib]

/-- A scalar can be taken outside a finite expectation. -/
theorem FiniteLaw.expectation_smul (μ : FiniteLaw Ω) (c : ℝ) (X : Ω → ℝ) :
    μ.expectation (fun ω ↦ c * X ω) = c * μ.expectation X := by
  simp only [FiniteLaw.expectation, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Expectation commutes with differences of observables. -/
theorem FiniteLaw.expectation_sub (μ : FiniteLaw Ω) (X Y : Ω → ℝ) :
    μ.expectation (fun ω ↦ X ω - Y ω) = μ.expectation X - μ.expectation Y := by
  simp only [FiniteLaw.expectation, mul_sub, Finset.sum_sub_distrib]

/-- Expectation commutes with finite sums, including sums over vertices or edges. -/
theorem FiniteLaw.expectation_sum (μ : FiniteLaw Ω) (X : Ξ → Ω → ℝ) :
    μ.expectation (fun ω ↦ ∑ ξ, X ξ ω) = ∑ ξ, μ.expectation (X ξ) := by
  simp only [FiniteLaw.expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- Pointwise comparison is needed only at outcomes of positive probability. -/
theorem FiniteLaw.expectation_mono_support (μ : FiniteLaw Ω) {X Y : Ω → ℝ}
    (hXY : ∀ ω, 0 < μ.mass ω → X ω ≤ Y ω) : μ.expectation X ≤ μ.expectation Y := by
  apply Finset.sum_le_sum
  intro ω _
  by_cases hω : 0 < μ.mass ω
  · exact mul_le_mul_of_nonneg_left (hXY ω hω) (μ.nonneg ω)
  · have hzero : μ.mass ω = 0 := le_antisymm (le_of_not_gt hω) (μ.nonneg ω)
    simp [hzero]

/-- A nonnegative observable has nonnegative expectation. -/
theorem FiniteLaw.expectation_nonneg (μ : FiniteLaw Ω) {X : Ω → ℝ}
    (hX : ∀ ω, 0 ≤ X ω) : 0 ≤ μ.expectation X := by
  exact Finset.sum_nonneg (fun ω _ ↦ mul_nonneg (μ.nonneg ω) (hX ω))

/-- A uniform bound on the support bounds the expectation. -/
theorem FiniteLaw.expectation_le (μ : FiniteLaw Ω) {X : Ω → ℝ} {b : ℝ}
    (hX : ∀ ω, 0 < μ.mass ω → X ω ≤ b) : μ.expectation X ≤ b := by
  simpa only [FiniteLaw.expectation_const] using μ.expectation_mono_support hX

/-- Strict pointwise bounds on a finite support yield a strict expectation bound. -/
theorem FiniteLaw.expectation_lt (μ : FiniteLaw Ω) {X : Ω → ℝ} {b : ℝ}
    (hX : ∀ ω, 0 < μ.mass ω → X ω < b) : μ.expectation X < b := by
  obtain ⟨ω₀, hω₀⟩ := μ.exists_pos_mass
  have hle : ∀ ω ∈ (Finset.univ : Finset Ω), μ.mass ω * X ω ≤ μ.mass ω * b := by
    intro ω _
    by_cases hω : 0 < μ.mass ω
    · exact le_of_lt (mul_lt_mul_of_pos_left (hX ω hω) hω)
    · have hzero : μ.mass ω = 0 := le_antisymm (le_of_not_gt hω) (μ.nonneg ω)
      simp [hzero]
  have hlt := Finset.sum_lt_sum hle
    ⟨ω₀, Finset.mem_univ _, mul_lt_mul_of_pos_left (hX ω₀ hω₀) hω₀⟩
  change μ.expectation X < μ.expectation (fun _ ↦ b) at hlt
  simpa only [FiniteLaw.expectation_const] using hlt

/-- Some outcome of positive probability attains at least the mean. -/
theorem FiniteLaw.exists_ge_expectation (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    ∃ ω, 0 < μ.mass ω ∧ μ.expectation X ≤ X ω := by
  by_contra! h
  exact (lt_irrefl _) (μ.expectation_lt h)

/-- Negation commutes with expectation. -/
theorem FiniteLaw.expectation_neg (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    μ.expectation (fun ω ↦ -X ω) = -μ.expectation X := by
  simpa only [neg_one_mul] using μ.expectation_smul (-1) X

/-- Some outcome of positive probability has observable at most the mean. -/
theorem FiniteLaw.exists_le_expectation (μ : FiniteLaw Ω) (X : Ω → ℝ) :
    ∃ ω, 0 < μ.mass ω ∧ X ω ≤ μ.expectation X := by
  obtain ⟨ω, hω, hX⟩ := μ.exists_ge_expectation (fun ω ↦ -X ω)
  rw [μ.expectation_neg] at hX
  exact ⟨ω, hω, neg_le_neg_iff.mp hX⟩

/-- The deterministic law concentrated at one chosen outcome. -/
def FiniteLaw.pure (ω : Ω) : FiniteLaw Ω := by
  classical
  exact ⟨fun ξ ↦ if ξ = ω then 1 else 0,
    fun ξ ↦ by split_ifs <;> norm_num, by simp⟩

/-- Expectation under a deterministic law is evaluation at its chosen outcome. -/
@[simp] theorem FiniteLaw.expectation_pure (ω : Ω) (X : Ω → ℝ) :
    (FiniteLaw.pure ω).expectation X = X ω := by
  classical
  simp [FiniteLaw.expectation, FiniteLaw.pure]

/-- A constant denominator can be taken outside a finite expectation. -/
theorem FiniteLaw.expectation_div (μ : FiniteLaw Ω) (X : Ω → ℝ) (c : ℝ) :
    μ.expectation (fun ω ↦ X ω / c) = μ.expectation X / c := by
  simp only [FiniteLaw.expectation, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  ring

/-- Sample a branch, then a finite conditional law on that branch's own outcome type. -/
def FiniteLaw.sigma {ι : Type*} [Fintype ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (p : FiniteLaw ι) (μ : ∀ i, FiniteLaw (κ i)) : FiniteLaw (Sigma κ) where
  mass ω := p.mass ω.1 * (μ ω.1).mass ω.2
  nonneg ω := mul_nonneg (p.nonneg ω.1) ((μ ω.1).nonneg ω.2)
  sum_mass := by
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ i, p.mass i := by
        apply Finset.sum_congr rfl
        intro i _
        change (∑ y : κ i, p.mass i * (μ i).mass y) = p.mass i
        rw [← Finset.mul_sum, (μ i).sum_mass, mul_one]
      _ = 1 := p.sum_mass

/-- Finite conditional expectation on a disjoint union of branch sample spaces. -/
theorem FiniteLaw.expectation_sigma {ι : Type*} [Fintype ι] {κ : ι → Type*}
    [∀ i, Fintype (κ i)] (p : FiniteLaw ι) (μ : ∀ i, FiniteLaw (κ i))
    (X : ∀ i, κ i → ℝ) :
    (FiniteLaw.sigma p μ).expectation (fun ω ↦ X ω.1 ω.2) =
      p.expectation (fun i ↦ (μ i).expectation (X i)) := by
  simp only [FiniteLaw.expectation, FiniteLaw.sigma, Fintype.sum_sigma,
    mul_assoc, Finset.mul_sum]

end Cliquefree
