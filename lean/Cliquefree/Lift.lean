module

public import Cliquefree.Potential
public import Cliquefree.GraphIdentities
public import Cliquefree.ScalarCalculus

/-!
# Lifting the prescribed weights

The prescribed weights lift to positive auxiliary weights with no loss in the benchmark.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- A nonisolated vertex has positive weighted degree under positive weights. -/
theorem weightedDegree_pos_of_neighbor (G : SimpleGraph V) {s : V → ℝ}
    (hs : ∀ v, 0 < s v) {x : V} (hx : ∃ y, G.Adj x y) : 0 < weightedDegree G s x := by
  classical
  apply div_pos ?_ (hs x)
  unfold neighborhoodMass
  apply Finset.sum_pos'
  · intro y _
    split_ifs
    · exact (hs y).le
    · exact le_rfl
  · obtain ⟨y, hy⟩ := hx
    exact ⟨y, Finset.mem_univ y, by simpa only [ite_eq_left hy] using hs y⟩

/-- The scalar lift is positive at every vertex of a graph without isolates. -/
theorem liftedWeights_pos (G : SimpleGraph V) {u s : V → ℝ}
    (hu : ∀ v, 0 < u v) (hs : ∀ v, 0 < s v) (hG : ∀ v, ∃ y, G.Adj v y) (v : V) :
    0 < liftedWeights G u s v :=
  sqrt_neg_shearerF_deriv_pos (hu v) (weightedDegree_pos_of_neighbor G hs (hG v))

/-- At the lifted coordinate, the prescribed degree realizes the scalar infimum. -/
theorem scalarPotential_liftedWeights (G : SimpleGraph V) {u s : V → ℝ}
    (hu : ∀ v, 0 < u v) (hs : ∀ v, 0 < s v) (hG : ∀ v, ∃ y, G.Adj v y) (v : V) :
    scalarPotential (u v) (liftedWeights G u s v) =
      u v * shearerF (weightedDegree G s v) +
      weightedDegree G s v * (liftedWeights G u s v) ^ 2 :=
  scalarPotential_sqrt_neg_deriv (hu v) (weightedDegree_pos_of_neighbor G hs (hG v))

/-- The potential surplus of a lift equals its quadratic graph discrepancy. -/
theorem graphPotential_lift_discrepancy (G : SimpleGraph V) {u s : V → ℝ}
    (hu : ∀ v, 0 < u v) (hs : ∀ v, 0 < s v) (hG : ∀ v, ∃ y, G.Adj v y) :
    graphPotential G u (liftedWeights G u s) - benchmark G u s =
      (∑ v, weightedDegree G s v * (liftedWeights G u s v) ^ 2) -
      2 * edgeMass G (liftedWeights G u s) := by
  unfold graphPotential benchmark
  simp_rw [scalarPotential_liftedWeights G hu hs hG]
  rw [Finset.sum_add_distrib]
  ring

/-- Lifting prescribed weights never decreases their benchmark. -/
theorem benchmark_le_lifted_potential (G : SimpleGraph V) {u s : V → ℝ}
    (hu : ∀ v, 0 < u v) (hs : ∀ v, 0 < s v) (hG : ∀ v, ∃ y, G.Adj v y) :
    benchmark G u s ≤ graphPotential G u (liftedWeights G u s) := by
  have h := weighted_lift_discrepancy_nonneg G s (liftedWeights G u s) hs
  rw [← graphPotential_lift_discrepancy G hu hs hG] at h
  exact sub_nonneg.mp h

end Cliquefree
