module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
# Weighted independent sets in clique-free graphs: existence statements

The weighted degree, Shearer function, and absolute constant below give two formulations of
the existence theorem. Both conclusions use Mathlib's independent-set predicate.

`weighted_existence` states the blueprint existence theorem. Its positive comparison constants
are uniform in the clique order, graph, and weights, expressing the order `1 / r`.
`weighted_existence_explicit` gives the coefficient `c_r = 1 / (1 + 1152 B₀ r)`.
Both statements allow empty graphs and zero objective weights.
Setting both weight vectors to one gives the ordinary degree-sequence independence bound.

The two theorem bodies in this module are admitted with `sorry`. Comparator checks these
statements and their definition dependencies against the independent proofs in `Solution.lean`,
allowing the three standard Lean axioms.
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
  sorry

/-- The explicit existence coefficient, with `K = 24 r`:
`c_r = 1 / (1 + 1152 B₀ r)`. It is a positive rational and gives the existence guarantee. -/
theorem weighted_existence_explicit {V : Type u} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (hr : 4 ≤ r) (s a : V → ℝ)
    (hG : G.CliqueFree r) (hs : ∀ v, 0 < s v) (ha : ∀ v, 0 ≤ a v) :
    let c : ℚ := 1 / (1 + 1152 * triangleConstant * (r : ℚ))
    0 < c ∧ ∃ I : Finset V, G.IsIndepSet (I : Set V) ∧
      (c : ℝ) * (∑ v, a v * shearerF (weightedDegree G s v)) ≤ ∑ v ∈ I, a v := by
  sorry

end CliquefreeResults
