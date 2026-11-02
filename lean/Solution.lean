module

public import Cliquefree.LinearExistence

/-!
# Proofs of the independent existence statements

The two existence statements are proved from `Cliquefree.LinearExistence`.
This module defines their vocabulary independently of `Challenge.lean` for Comparator.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u

namespace CliquefreeResults

/-- Shearer's function with its continuous values at zero and one. `Real.log` is natural log. -/
def shearerF (d : ℝ) : ℝ :=
  if d = 0 then 1 else if d = 1 then 1 / 2 else
    (d * Real.log d - d + 1) / (d - 1) ^ 2

/-- The sum of the weights on the open neighborhood of `v`, divided by the weight at `v`. -/
def weightedDegree {V : Type*} [Fintype V] (G : SimpleGraph V) (s : V → ℝ) (v : V) : ℝ := by
  classical
  exact (∑ x ∈ G.neighborFinset v, s x) / s v

/-- The explicit absolute constant `B₀ = 2^X`, where `X = (100 a_*)^4`,
`a_* = 24 (A_* + 1)`, and `A_* = 20 + 12 · 24²`. The exponent is a natural number. -/
def triangleConstant : ℚ :=
  2 ^ ((100 * (24 * ((20 + 12 * 24 ^ 2) + 1))) ^ 4 : ℕ)

private theorem weightedDegree_eq {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s : V → ℝ) (v : V) :
    weightedDegree G s v = Cliquefree.weightedDegree G s v := by
  classical
  rw [weightedDegree, Cliquefree.weightedDegree,
    Cliquefree.neighborhoodMass_eq_sum_neighborFinset]

private theorem benchmark_eq {V : Type*} [Fintype V]
    (G : SimpleGraph V) (s a : V → ℝ) :
    (∑ v, a v * shearerF (weightedDegree G s v)) = Cliquefree.benchmark G a s := by
  simp only [Cliquefree.benchmark, weightedDegree_eq, shearerF, Cliquefree.shearerF]

private theorem triangleConstant_eq : triangleConstant = Cliquefree.triangleBoundConstant := rfl

/-- The weighted existence theorem: a positive rational family of order `1 / r`
works for every finite `K_r`-free graph, positive real degree weights, and nonnegative real
objective weights. The independent set realizes at least the displayed weighted Shearer sum. -/
theorem weighted_existence :
    ∃ c : ℕ → ℚ, (∀ r : ℕ, 4 ≤ r → 0 < c r) ∧
      (∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ r : ℕ, 4 ≤ r →
        A / (r : ℝ) ≤ (c r : ℝ) ∧ (c r : ℝ) ≤ B / (r : ℝ)) ∧
      ∀ r : ℕ, 4 ≤ r → ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (s a : V → ℝ),
        G.CliqueFree r → (∀ v, 0 < s v) → (∀ v, 0 ≤ a v) →
          ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
            (c r : ℝ) * (∑ v, a v * shearerF (weightedDegree G s v)) ≤ ∑ v ∈ I, a v := by
  refine ⟨Cliquefree.linearExistenceConstant,
    fun r _ ↦ Cliquefree.linearExistenceConstant_pos r,
    Cliquefree.linearExistenceConstant_order_inverse, ?_⟩
  intro r hr V inst G s a hG hs ha
  simpa only [benchmark_eq, Cliquefree.Independent, Cliquefree.weightSum] using
    Cliquefree.linear_exists_independent_set_bound G (by omega : 2 ≤ r) hG ha hs

/-- The explicit existence coefficient, with `K = 24 r`:
`c_r = 1 / (1 + 1152 B₀ r)`. It is a positive rational and gives the existence guarantee. -/
theorem weighted_existence_explicit {V : Type u} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (hr : 4 ≤ r) (s a : V → ℝ)
    (hG : G.CliqueFree r) (hs : ∀ v, 0 < s v) (ha : ∀ v, 0 ≤ a v) :
    let c : ℚ := 1 / (1 + 1152 * triangleConstant * (r : ℚ))
    0 < c ∧ ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      (c : ℝ) * (∑ v, a v * shearerF (weightedDegree G s v)) ≤ ∑ v ∈ I, a v := by
  dsimp only
  rw [triangleConstant_eq, ← Cliquefree.linearExistenceConstant_formula]
  refine ⟨Cliquefree.linearExistenceConstant_pos r, ?_⟩
  simpa only [benchmark_eq, Cliquefree.Independent, Cliquefree.weightSum] using
    Cliquefree.linear_exists_independent_set_bound G (by omega : 2 ≤ r) hG ha hs

end CliquefreeResults
