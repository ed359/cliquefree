module

public import Cliquefree.Independence

/-!
# Removing an isolated vertex
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Removing an isolated vertex leaves every other neighborhood mass unchanged. -/
theorem neighborhoodMass_induce_erase_isolated [DecidableEq V] (G : SimpleGraph V)
    (s : V → ℝ) {x : V} (hx : ∀ y, ¬G.Adj x y)
    (v : (Finset.univ.erase x : Finset V)) :
    neighborhoodMass (G.induce ((Finset.univ.erase x : Finset V) : Set V))
      (fun y ↦ s y) v = neighborhoodMass G s v := by
  classical
  rw [← neighborhoodMass_extendByZero_coe]
  unfold neighborhoodMass
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y = x
  · subst y
    have hno : ¬G.Adj (v : V) x := fun h ↦ hx v h.symm
    simp [hno]
  · simp [extendByZero, hy]

/-- An isolated vertex contributes exactly its objective weight to the benchmark. -/
theorem benchmark_erase_isolated [DecidableEq V] (G : SimpleGraph V) (u s : V → ℝ)
    {x : V} (hx : ∀ y, ¬G.Adj x y) :
    benchmark G u s = u x +
      benchmark (G.induce ((Finset.univ.erase x : Finset V) : Set V))
        (fun v ↦ u v) (fun v ↦ s v) := by
  classical
  have hv (v : (Finset.univ.erase x : Finset V)) :
      weightedDegree (G.induce ((Finset.univ.erase x : Finset V) : Set V))
        (fun y ↦ s y) v = weightedDegree G s v := by
    unfold weightedDegree
    rw [neighborhoodMass_induce_erase_isolated G s hx]
  have he : benchmark
      (G.induce ((Finset.univ.erase x : Finset V) : Set V))
      (fun v ↦ u v) (fun v ↦ s v) =
        weightSum (fun v ↦ u v * shearerF (weightedDegree G s v)) (Finset.univ.erase x) := by
    unfold benchmark
    simp_rw [hv]
    exact sum_restrict_eq_weightSum (Finset.univ.erase x)
      (fun v ↦ u v * shearerF (weightedDegree G s v))
  rw [he]
  have hs := Finset.sum_erase_add Finset.univ
    (fun v ↦ u v * shearerF (weightedDegree G s v)) (Finset.mem_univ x)
  rw [weightedDegree_eq_zero_of_isolated G s hx, shearerF_zero, mul_one] at hs
  unfold benchmark weightSum
  linarith

/-- The extremal benchmark loses at most the objective weight of a removed isolated vertex. -/
theorem extremalBenchmark_erase_isolated_le [DecidableEq V] (G : SimpleGraph V)
    {u : V → ℝ} (hu : ∀ v, 0 ≤ u v) {x : V} (hx : ∀ y, ¬G.Adj x y) :
    extremalBenchmark G u ≤ u x +
      extremalBenchmark (G.induce ((Finset.univ.erase x : Finset V) : Set V))
        (fun v ↦ u v) := by
  apply csSup_le (benchmark_values_nonempty G u)
  rintro a ⟨s, hs, rfl⟩
  rw [benchmark_erase_isolated G u s hx]
  gcongr
  exact benchmark_le_extremalBenchmark _ (fun v ↦ hu v) (fun v ↦ hs v)

/-- Deleting the closed neighborhood of an isolated vertex deletes just that vertex. -/
theorem closedNeighborhood_eq_singleton_of_isolated (G : SimpleGraph V) {x : V}
    (hx : ∀ y, ¬G.Adj x y) : closedNeighborhood G x = {x} := by
  classical
  ext y
  simp [mem_closedNeighborhood, hx]

/-- Selecting an isolated vertex adds its objective weight to the remaining independent optimum. -/
theorem selection_isolated_independenceWeight_le [DecidableEq V] (G : SimpleGraph V)
    (u : V → ℝ) {x : V} (hx : ∀ y, ¬G.Adj x y) :
    u x + independenceWeight
      (G.induce ((Finset.univ.erase x : Finset V) : Set V))
      (fun v ↦ u v) ≤ independenceWeight G u := by
  have h := selection_independenceWeight_le G u x
  rw [closedNeighborhood_eq_singleton_of_isolated G hx, Finset.sdiff_singleton_eq_erase] at h
  exact h


end Cliquefree
