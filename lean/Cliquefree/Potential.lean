module

public import Cliquefree.Basic
public import Cliquefree.Scalar

/-!
# Graph potentials and the prescribed weighted benchmark

The comparison theorem holds at every positive auxiliary weighting, without stationarity.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- The prescribed weighted Shearer benchmark `Φ`. -/
def benchmark (G : SimpleGraph V) (u s : V → ℝ) : ℝ :=
  ∑ v, u v * shearerF (weightedDegree G s v)

/-- The graph potential `𝒰`, defined also on nonnegative auxiliary weights. -/
def graphPotential (G : SimpleGraph V) (u w : V → ℝ) : ℝ :=
  (∑ v, scalarPotential (u v) (w v)) - 2 * edgeMass G w

/-- The coordinate residual of the graph potential. -/
def residual (G : SimpleGraph V) (u w : V → ℝ) (v : V) : ℝ :=
  deriv (scalarPotential (u v)) (w v) - 2 * neighborhoodMass G w v

/-- Deletion is represented by zeroing the coordinates in a finite vertex set. -/
def eraseWeights (w : V → ℝ) (A : Finset V) : V → ℝ := by
  classical
  exact fun v ↦ if v ∈ A then 0 else w v

/-- Reward for selecting a vertex and zeroing its closed neighborhood. -/
def deletionReward (G : SimpleGraph V) (u w : V → ℝ) (c : ℝ) (x : V) : ℝ :=
  u x + c * graphPotential G u (eraseWeights w (closedNeighborhood G x)) -
    c * graphPotential G u w

/-- The supremum benchmark over all strictly positive prescribed weights. -/
def extremalBenchmark (G : SimpleGraph V) (u : V → ℝ) : ℝ :=
  sSup {a | ∃ s : V → ℝ, (∀ v, 0 < s v) ∧ benchmark G u s = a}

/-- The explicit candidate lift of prescribed weights. -/
def liftedWeights (G : SimpleGraph V) (u s : V → ℝ) (v : V) : ℝ :=
  Real.sqrt (-u v * deriv shearerF (weightedDegree G s v))

/-- The benchmark never exceeds the total objective weight. -/
theorem benchmark_le_total (G : SimpleGraph V) {u s : V → ℝ}
    (hu : ∀ v, 0 ≤ u v) (hs : ∀ v, 0 < s v) : benchmark G u s ≤ ∑ v, u v := by
  apply Finset.sum_le_sum
  intro v _
  exact mul_le_of_le_one_right (hu v) (shearerF_le_one (weightedDegree_nonneg G hs v))

/-- Common nonzero rescaling of prescribed weights preserves the benchmark. -/
theorem benchmark_scale (G : SimpleGraph V) (u s : V → ℝ) {a : ℝ} (ha : a ≠ 0) :
    benchmark G u (fun v ↦ a * s v) = benchmark G u s := by
  simp only [benchmark, weightedDegree_scale G s ha]

/-- Graph potential is bounded by the weighted Shearer benchmark at the same positive weights. -/
theorem graphPotential_le_benchmark (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 ≤ u v) (hw : ∀ v, 0 < w v) :
    graphPotential G u w ≤ benchmark G u w := by
  have hterm (v : V) : scalarPotential (u v) (w v) ≤
      u v * shearerF (weightedDegree G w v) + w v * neighborhoodMass G w v := by
    have ht := scalarPotential_le_test_nonneg (x := w v) (hu v)
      (weightedDegree_nonneg G hw v)
    have heq : weightedDegree G w v * w v ^ 2 = w v * neighborhoodMass G w v := by
      unfold weightedDegree
      field_simp [(hw v).ne']
    simpa only [heq] using ht
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset V)) ↦ hterm v)
  rw [Finset.sum_add_distrib, weighted_handshake G w] at hsum
  unfold graphPotential benchmark
  linarith

/-- The set defining the extremal benchmark is nonempty, including on the empty graph. -/
theorem benchmark_values_nonempty (G : SimpleGraph V) (u : V → ℝ) :
    {a | ∃ s : V → ℝ, (∀ v, 0 < s v) ∧ benchmark G u s = a}.Nonempty :=
  ⟨benchmark G u (fun _ ↦ 1), fun _ ↦ 1, by simp, rfl⟩

/-- The benchmark supremum is finite for nonnegative objective weights. -/
theorem benchmark_values_bddAbove (G : SimpleGraph V) {u : V → ℝ} (hu : ∀ v, 0 ≤ u v) :
    BddAbove {a | ∃ s : V → ℝ, (∀ v, 0 < s v) ∧ benchmark G u s = a} := by
  refine ⟨∑ v, u v, ?_⟩
  rintro a ⟨s, hs, rfl⟩
  exact benchmark_le_total G hu hs

/-- Every positive prescribed weighting is bounded by the extremal benchmark. -/
theorem benchmark_le_extremalBenchmark (G : SimpleGraph V) {u s : V → ℝ}
    (hu : ∀ v, 0 ≤ u v) (hs : ∀ v, 0 < s v) : benchmark G u s ≤ extremalBenchmark G u :=
  le_csSup (benchmark_values_bddAbove G hu) ⟨s, hs, rfl⟩

/-- The extremal benchmark also lies below the total objective weight. -/
theorem extremalBenchmark_le_total (G : SimpleGraph V) {u : V → ℝ}
    (hu : ∀ v, 0 ≤ u v) : extremalBenchmark G u ≤ ∑ v, u v := by
  apply csSup_le (benchmark_values_nonempty G u)
  rintro a ⟨s, hs, rfl⟩
  exact benchmark_le_total G hu hs

/-- Any positive auxiliary weighting has potential bounded by the extremal benchmark. -/
theorem graphPotential_le_extremalBenchmark (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 ≤ u v) (hw : ∀ v, 0 < w v) :
    graphPotential G u w ≤ extremalBenchmark G u :=
  (graphPotential_le_benchmark G hu hw).trans (benchmark_le_extremalBenchmark G hu hw)

end Cliquefree
