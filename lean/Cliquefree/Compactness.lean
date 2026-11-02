module

public import Cliquefree.Maximizer

/-!
# Normalized maximizing sequences
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Normalize a prescribed weighting to have total mass one. -/
def normalizeWeights (s : V → ℝ) (v : V) : ℝ := s v / ∑ x, s x

/-- A positive weighting on a nonempty finite vertex type has positive total mass. -/
theorem totalWeight_pos [Nonempty V] {s : V → ℝ} (hs : ∀ v, 0 < s v) :
    0 < ∑ v, s v :=
  Finset.sum_pos (fun v _ ↦ hs v) Finset.univ_nonempty

/-- Normalizing a positive weighting preserves positivity. -/
theorem normalizeWeights_pos [Nonempty V] {s : V → ℝ} (hs : ∀ v, 0 < s v) (v : V) :
    0 < normalizeWeights s v := div_pos (hs v) (totalWeight_pos hs)

/-- A normalized positive weighting belongs to the closed standard simplex. -/
theorem normalizeWeights_mem_simplex [Nonempty V] {s : V → ℝ} (hs : ∀ v, 0 < s v) :
    (∀ v, 0 ≤ normalizeWeights s v) ∧ ∑ v, normalizeWeights s v = 1 := by
  refine ⟨fun v ↦ (normalizeWeights_pos hs v).le, ?_⟩
  simp only [normalizeWeights, ← Finset.sum_div]
  exact div_self (totalWeight_pos hs).ne'

/-- Normalization preserves all weighted degrees and hence the benchmark. -/
theorem benchmark_normalizeWeights [Nonempty V] (G : SimpleGraph V) (u : V → ℝ)
    {s : V → ℝ} (hs : ∀ v, 0 < s v) :
    benchmark G u (normalizeWeights s) = benchmark G u s := by
  have he : normalizeWeights s = fun v ↦ (∑ x, s x)⁻¹ * s v := by
    funext v
    simp [normalizeWeights, div_eq_mul_inv, mul_comm]
  rw [he]
  exact benchmark_scale G u s (inv_ne_zero (totalWeight_pos hs).ne')

/-- The extremal benchmark admits a sequence of positive normalized approximate maximizers. -/
theorem exists_normalized_maximizing_sequence [Nonempty V] (G : SimpleGraph V)
    {u : V → ℝ} (hu : ∀ v, 0 ≤ u v) :
    ∃ s : ℕ → V → ℝ, (∀ n v, 0 < s n v) ∧
      (∀ n, (∀ v, 0 ≤ s n v) ∧ ∑ v, s n v = 1) ∧
      Tendsto (fun n ↦ benchmark G u (s n)) atTop (𝓝 (extremalBenchmark G u)) := by
  obtain ⟨a, _, ht, ha⟩ := exists_seq_tendsto_sSup
    (benchmark_values_nonempty G u) (benchmark_values_bddAbove G hu)
  choose s hs he using ha
  refine ⟨fun n ↦ normalizeWeights (s n), fun n v ↦ normalizeWeights_pos (hs n) v,
    fun n ↦ normalizeWeights_mem_simplex (hs n), ?_⟩
  have hEq : (fun n ↦ benchmark G u (normalizeWeights (s n))) = a := by
    funext n
    rw [benchmark_normalizeWeights G u (hs n)]
    exact he n
  rw [hEq]
  exact ht

/-- Compactness supplies a convergent normalized maximizing sequence with a simplex limit. -/
theorem exists_normalized_maximizing_limit [Nonempty V] (G : SimpleGraph V)
    {u : V → ℝ} (hu : ∀ v, 0 ≤ u v) :
    ∃ (s : ℕ → V → ℝ) (s₀ : V → ℝ),
      (∀ n v, 0 < s n v) ∧ (∀ n, (∀ v, 0 ≤ s n v) ∧ ∑ v, s n v = 1) ∧
      ((∀ v, 0 ≤ s₀ v) ∧ ∑ v, s₀ v = 1) ∧ Tendsto s atTop (𝓝 s₀) ∧
      Tendsto (fun n ↦ benchmark G u (s n)) atTop (𝓝 (extremalBenchmark G u)) := by
  obtain ⟨s, hs, hsimplex, ht⟩ := exists_normalized_maximizing_sequence G hu
  have hcompact : IsCompact {s : V → ℝ | (∀ v, 0 ≤ s v) ∧ ∑ v, s v = 1} := by
    convert isCompact_range
      (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ V).continuous using 1
    ext s
    simp [Convexity.StdSimplex.range_toFun_comp_weights]
  obtain ⟨s₀, h₀, φ, hφ, hlim⟩ := hcompact.tendsto_subseq hsimplex
  exact ⟨s ∘ φ, s₀, fun n v ↦ hs (φ n) v, fun n ↦ hsimplex (φ n), h₀,
    hlim, ht.comp hφ.tendsto_atTop⟩

/-- A simplex limit has a nonempty positive support. -/
theorem simplex_positive_support_nonempty {s : V → ℝ}
    (hs : (∀ v, 0 ≤ s v) ∧ ∑ v, s v = 1) :
    ∃ v, 0 < s v := by
  by_contra! h
  have hsum : ∑ v, s v = 0 := Finset.sum_eq_zero (fun v _ ↦ le_antisymm (h v) (hs.1 v))
  rw [hs.2] at hsum
  norm_num at hsum

/-- The benchmark is continuous at every positive prescribed weighting. -/
theorem benchmark_continuousAt (G : SimpleGraph V) (u : V → ℝ) {s : V → ℝ}
    (hs : ∀ v, 0 < s v) : ContinuousAt (benchmark G u) s := by
  unfold benchmark
  apply tendsto_finsetSum
  intro v _
  apply ContinuousAt.const_mul
  apply shearerF_continuous.continuousAt.comp
  exact (neighborhoodMass_continuous G v).continuousAt.div
    (continuous_apply v).continuousAt (hs v).ne'

/-- If a maximizing sequence has a positive limit, that limit attains the extremal benchmark. -/
theorem maximizing_limit_attains (G : SimpleGraph V) (u : V → ℝ)
    {s : ℕ → V → ℝ} {s₀ : V → ℝ} (hs₀ : ∀ v, 0 < s₀ v)
    (hs : Tendsto s atTop (𝓝 s₀))
    (hmax : Tendsto (fun n ↦ benchmark G u (s n)) atTop (𝓝 (extremalBenchmark G u))) :
    benchmark G u s₀ = extremalBenchmark G u :=
  tendsto_nhds_unique ((benchmark_continuousAt G u hs₀).tendsto.comp hs) hmax

end Cliquefree
