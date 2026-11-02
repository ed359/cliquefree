module

public import Cliquefree.FiniteLaw

/-!
# Products of finitely supported laws

Independent products let one choose all the local incidence couplings at once.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

/-- The independent product of a finite family of finite laws. -/
def FiniteLaw.product {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : ι → Type*} [∀ i, Fintype (κ i)]
    (μ : ∀ i, FiniteLaw (κ i)) : FiniteLaw (∀ i, κ i) where
  mass f := ∏ i, (μ i).mass (f i)
  nonneg f := Finset.prod_nonneg (fun i _ ↦ (μ i).nonneg (f i))
  sum_mass := by
    classical
    rw [← Fintype.prod_sum]
    simp only [FiniteLaw.sum_mass, Finset.prod_const_one]

/-- Independent products factor the expectation of a product of coordinate functions. -/
theorem FiniteLaw.expectation_product {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : ∀ i, FiniteLaw (κ i))
    (X : ∀ i, κ i → ℝ) :
    (FiniteLaw.product μ).expectation (fun f ↦ ∏ i, X i (f i)) =
      ∏ i, (μ i).expectation (X i) := by
  classical
  simp only [FiniteLaw.expectation, FiniteLaw.product, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun i x ↦ (μ i).mass x * X i x)).symm

/-- Each coordinate of the independent product has its prescribed original law. -/
theorem FiniteLaw.expectation_product_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    {κ : ι → Type*} [∀ i, Fintype (κ i)] (μ : ∀ i, FiniteLaw (κ i))
    (i : ι) (X : κ i → ℝ) :
    (FiniteLaw.product μ).expectation (fun f ↦ X (f i)) = (μ i).expectation X := by
  classical
  let Y : ∀ j, κ j → ℝ := fun j ↦ if h : j = i then fun x ↦ X (h ▸ x) else fun _ ↦ 1
  have hpoint (f : ∀ j, κ j) : (∏ j, Y j (f j)) = X (f i) := by
    rw [Fintype.prod_eq_single i]
    · simp [Y]
    · intro j hj
      simp [Y, hj]
  have hexp : (∏ j, (μ j).expectation (Y j)) = (μ i).expectation X := by
    rw [Fintype.prod_eq_single i]
    · simp [Y]
    · intro j hj
      simp [Y, hj]
  simpa only [hpoint, hexp] using FiniteLaw.expectation_product μ Y

end Cliquefree
