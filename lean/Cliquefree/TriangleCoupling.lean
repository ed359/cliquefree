module

public import Cliquefree.ThresholdAtoms
public import Cliquefree.FiniteProduct

/-!
# Simultaneous incidence couplings

All local grand couplings can be chosen jointly while preserving each row marginal and
its pairwise disagreement estimate.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

/-- Independent products combine a dependent family of grand couplings. -/
theorem exists_family_grand_coupling {X : Type*} [Fintype X] [DecidableEq X]
    {I Y : X → Type*} [∀ x, Fintype (I x)] [∀ x, Fintype (Y x)]
    [∀ x, DecidableEq (I x)] [∀ x, DecidableEq (Y x)]
    (P : ∀ x, I x → FiniteLaw (Y x)) :
    ∃ μ : FiniteLaw (∀ x, I x → Y x),
      (∀ x i y, μ.expectation (fun f ↦ if f x i = y then 1 else 0) = (P x i).mass y) ∧
      (∀ x i j, μ.expectation (fun f ↦ if f x i ≠ f x j then 1 else 0) ≤
        2 * (P x i).totalVariation (P x j)) := by
  classical
  choose μ hm hd using (fun x ↦ exists_grand_coupling (P x))
  refine ⟨FiniteLaw.product μ, ?_, ?_⟩
  · intro x i y
    rw [FiniteLaw.expectation_product_apply μ x (fun f ↦ if f i = y then 1 else 0)]
    exact hm x i y
  · intro x i j
    rw [FiniteLaw.expectation_product_apply μ x (fun f ↦ if f i ≠ f j then 1 else 0)]
    exact hd x i j

/-- Correct point marginals determine the expectation of every finite observable. -/
theorem FiniteLaw.expectation_of_marginals {Ω Y : Type*} [Fintype Ω] [Fintype Y]
    [DecidableEq Y] (μ : FiniteLaw Ω) (ν : FiniteLaw Y) (f : Ω → Y)
    (hm : ∀ y, μ.expectation (fun ω ↦ if f ω = y then 1 else 0) = ν.mass y)
    (X : Y → ℝ) : μ.expectation (fun ω ↦ X (f ω)) = ν.expectation X := by
  calc
    _ = μ.expectation (fun ω ↦ ∑ y, X y * (if f ω = y then 1 else 0)) := by
      congr 1
      funext ω
      simp
    _ = ∑ y, X y * μ.expectation (fun ω ↦ if f ω = y then 1 else 0) := by
      rw [μ.expectation_sum]
      apply Finset.sum_congr rfl
      intro y _
      exact μ.expectation_smul (X y) _
    _ = ∑ y, X y * ν.mass y := by
      apply Finset.sum_congr rfl
      intro y _
      rw [hm y]
    _ = _ := by simp only [FiniteLaw.expectation, mul_comm]

end Cliquefree
