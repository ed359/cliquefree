module

public import Cliquefree.Induction

/-!
# Restricting weights and independent sets
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Increasing the vertex weights increases every neighborhood mass. -/
theorem neighborhoodMass_mono (G : SimpleGraph V) {w q : V → ℝ}
    (h : ∀ v, w v ≤ q v) (x : V) : neighborhoodMass G w x ≤ neighborhoodMass G q x := by
  classical
  unfold neighborhoodMass
  apply Finset.sum_le_sum
  intro v _
  split_ifs
  · exact h v
  · exact le_rfl

/-- Restricting a nonnegative weighting can only decrease a remaining neighborhood mass. -/
theorem neighborhoodMass_induce_le (G : SimpleGraph V) (A : Finset V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (v : A) :
    neighborhoodMass (G.induce (A : Set V)) (fun x ↦ w x) v ≤ neighborhoodMass G w v := by
  classical
  rw [← neighborhoodMass_extendByZero_coe]
  apply neighborhoodMass_mono
  intro x
  by_cases hx : x ∈ A <;> simp [extendByZero, hx, hw x]

/-- Restricting positive prescribed weights decreases their weighted degrees. -/
theorem weightedDegree_induce_le (G : SimpleGraph V) (A : Finset V) {s : V → ℝ}
    (hs : ∀ v, 0 < s v) (v : A) :
    weightedDegree (G.induce (A : Set V)) (fun x ↦ s x) v ≤ weightedDegree G s v := by
  unfold weightedDegree
  exact div_le_div_of_nonneg_right (neighborhoodMass_induce_le G A (fun x ↦ (hs x).le) v)
    (hs v).le

/-- Restricting a graph increases the benchmark contribution of the retained vertices. -/
theorem benchmark_restrict_le (G : SimpleGraph V) (A : Finset V) {u s : V → ℝ}
    (hu : ∀ v, 0 ≤ u v) (hs : ∀ v, 0 < s v) :
    weightSum (fun v ↦ u v * shearerF (weightedDegree G s v)) A ≤
      benchmark (G.induce (A : Set V)) (fun v ↦ u v) (fun v ↦ s v) := by
  calc
    _ = ∑ v : A, u v * shearerF (weightedDegree G s v) :=
      (sum_restrict_eq_weightSum A _).symm
    _ ≤ ∑ v : A, u v * shearerF
        (weightedDegree (G.induce (A : Set V)) (fun x ↦ s x) v) := by
      apply Finset.sum_le_sum
      intro v _
      apply mul_le_mul_of_nonneg_left _ (hu v)
      exact shearerF_strictAntiOn.antitoneOn
        (weightedDegree_nonneg (G.induce (A : Set V)) (fun x ↦ hs x) v)
        (weightedDegree_nonneg G hs v) (weightedDegree_induce_le G A hs v)
    _ = _ := by rfl

/-- Removing only zero-objective vertices cannot decrease the prescribed benchmark. -/
theorem benchmark_le_induce_of_zero_outside (G : SimpleGraph V) (A : Finset V)
    {u s : V → ℝ} (hu : ∀ v, 0 ≤ u v) (hs : ∀ v, 0 < s v)
    (hz : ∀ v, v ∉ A → u v = 0) :
    benchmark G u s ≤ benchmark (G.induce (A : Set V)) (fun v ↦ u v) (fun v ↦ s v) := by
  classical
  calc
    _ = weightSum (fun v ↦ u v * shearerF (weightedDegree G s v)) A := by
      symm
      apply Finset.sum_subset (Finset.subset_univ A)
      intro v _ hv
      rw [hz v hv, zero_mul]
    _ ≤ _ := benchmark_restrict_le G A hu hs

/-- Removing only zero-objective vertices cannot decrease the extremal benchmark. -/
theorem extremalBenchmark_le_induce_of_zero_outside (G : SimpleGraph V) (A : Finset V)
    {u : V → ℝ} (hu : ∀ v, 0 ≤ u v) (hz : ∀ v, v ∉ A → u v = 0) :
    extremalBenchmark G u ≤ extremalBenchmark (G.induce (A : Set V)) (fun v ↦ u v) := by
  apply csSup_le (benchmark_values_nonempty G u)
  rintro a ⟨s, hs, rfl⟩
  exact (benchmark_le_induce_of_zero_outside G A hu hs hz).trans
    (benchmark_le_extremalBenchmark (G.induce (A : Set V)) (fun v ↦ hu v) (fun v ↦ hs v))

end Cliquefree
