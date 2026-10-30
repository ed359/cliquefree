module
public import Cliquefree.Compactness
public import Cliquefree.Induced
public import Cliquefree.Restrictions

/-! # Boundary decomposition of maximizing prescribed weights -/

@[expose] public section

noncomputable section

open Set Filter
open scoped BigOperators Topology

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Coordinates where a nonnegative limiting weight vector is positive. -/
def positiveSupport (s : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun v ↦ 0 < s v)

@[simp] theorem mem_positiveSupport (s : V → ℝ) (v : V) :
    v ∈ positiveSupport s ↔ 0 < s v := by
  classical
  simp [positiveSupport]

/-- Vertices outside a limiting support and with no neighbor in that support. -/
def boundaryRemainder (G : SimpleGraph V) (A : Finset V) : Finset V := by
  classical
  exact Finset.univ.filter (fun v ↦ v ∉ A ∧ ∀ a ∈ A, ¬ G.Adj v a)

@[simp] theorem mem_boundaryRemainder (G : SimpleGraph V) (A : Finset V) (v : V) :
    v ∈ boundaryRemainder G A ↔ v ∉ A ∧ ∀ a ∈ A, ¬ G.Adj v a := by
  classical
  simp [boundaryRemainder]

theorem extendByZero_positiveSupport {s : V → ℝ} (hs : ∀ v, 0 ≤ s v) :
    extendByZero (positiveSupport s) (fun v ↦ s v) = s := by
  classical
  funext v
  by_cases hv : v ∈ positiveSupport s
  · exact extendByZero_coe (positiveSupport s) (fun v ↦ s v) ⟨v, hv⟩
  · rw [extendByZero_not_mem _ _ hv]
    exact (le_antisymm (le_of_not_gt ((mem_positiveSupport s v).not.mp hv)) (hs v)).symm

theorem weightedDegree_positiveSupport (G : SimpleGraph V) {s : V → ℝ}
    (hs : ∀ v, 0 ≤ s v) (v : positiveSupport s) :
    weightedDegree G s v =
      weightedDegree (G.induce (positiveSupport s : Set V))
        (fun a : positiveSupport s ↦ s a) v := by
  classical
  have he := neighborhoodMass_extendByZero_coe G (positiveSupport s)
    (fun a : positiveSupport s ↦ s a) v
  simpa only [weightedDegree, extendByZero_positiveSupport hs] using
    congrArg (fun t : ℝ ↦ t / s v) he

theorem weightedDegree_tendsto_support (G : SimpleGraph V) {s : ℕ → V → ℝ}
    {s₀ : V → ℝ} (h₀ : ∀ v, 0 ≤ s₀ v) (hs : Tendsto s atTop (𝓝 s₀))
    (v : positiveSupport s₀) :
    Tendsto (fun n ↦ weightedDegree G (s n) v) atTop
      (𝓝 (weightedDegree (G.induce (positiveSupport s₀ : Set V))
        (fun a : positiveSupport s₀ ↦ s₀ a) v)) := by
  rw [← weightedDegree_positiveSupport G h₀ v]
  exact ((neighborhoodMass_continuous G v).tendsto s₀ |>.comp hs).div
    ((continuous_apply (v : V)).tendsto s₀ |>.comp hs)
    ((mem_positiveSupport s₀ v).mp v.property).ne'

theorem weightedDegree_tendsto_boundary (G : SimpleGraph V) {s : ℕ → V → ℝ}
    {s₀ : V → ℝ} (hpos : ∀ n v, 0 < s n v) (h₀ : ∀ v, 0 ≤ s₀ v)
    (hs : Tendsto s atTop (𝓝 s₀)) {v : V} (hv : s₀ v = 0)
    (hadj : ∃ a, 0 < s₀ a ∧ G.Adj v a) :
    Tendsto (fun n ↦ weightedDegree G (s n) v) atTop atTop := by
  classical
  have hm : 0 < neighborhoodMass G s₀ v := by
    obtain ⟨a, ha, hva⟩ := hadj
    have hle : s₀ a ≤ neighborhoodMass G s₀ v := by
      unfold neighborhoodMass
      have hh := Finset.single_le_sum
        (f := fun y ↦ if G.Adj v y then s₀ y else 0)
        (fun y (_ : y ∈ Finset.univ) ↦ by split_ifs <;> simp_all) (Finset.mem_univ a)
      simpa only [ite_eq_left hva] using hh
    exact ha.trans_le hle
  have hz : Tendsto (fun n ↦ s n v) atTop (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    exact ⟨by simpa only [hv, Function.comp_def] using (continuous_apply v).tendsto s₀ |>.comp hs,
      Eventually.of_forall (fun n ↦ hpos n v)⟩
  simpa only [weightedDegree, div_eq_mul_inv, Pi.inv_apply, Function.comp_def] using
    ((neighborhoodMass_continuous G v).tendsto s₀ |>.comp hs).pos_mul_atTop hm
      hz.inv_tendsto_nhdsGT_zero

theorem benchmark_summand_tendsto_boundary (G : SimpleGraph V) (u : V → ℝ)
    {s : ℕ → V → ℝ} {s₀ : V → ℝ} (hpos : ∀ n v, 0 < s n v)
    (h₀ : ∀ v, 0 ≤ s₀ v) (hs : Tendsto s atTop (𝓝 s₀)) {v : V} (hv : s₀ v = 0)
    (hadj : ∃ a, 0 < s₀ a ∧ G.Adj v a) :
    Tendsto (fun n ↦ u v * shearerF (weightedDegree G (s n) v)) atTop (𝓝 0) := by
  have hf := shearerF_tendsto_atTop.comp
    (weightedDegree_tendsto_boundary G hpos h₀ hs hv hadj)
  simpa only [mul_zero, Function.comp_def] using hf.const_mul (u v)

theorem boundary_complement_summand_tendsto [DecidableEq V] (G : SimpleGraph V)
    (u : V → ℝ) {s : ℕ → V → ℝ} {s₀ : V → ℝ} (hpos : ∀ n v, 0 < s n v)
    (h₀ : ∀ v, 0 ≤ s₀ v) (hs : Tendsto s atTop (𝓝 s₀)) (v : V) :
    Tendsto (fun n ↦ if v ∈ boundaryRemainder G (positiveSupport s₀) then 0
      else u v * shearerF (weightedDegree G (s n) v)) atTop
      (𝓝 (if v ∈ positiveSupport s₀ then u v * shearerF (weightedDegree G s₀ v) else 0)) := by
  by_cases hvA : v ∈ positiveSupport s₀
  · have hvB : v ∉ boundaryRemainder G (positiveSupport s₀) := by
      simp only [mem_boundaryRemainder, not_and_or]
      exact Or.inl (not_not.mpr hvA)
    simp only [ite_eq_right hvB, ite_eq_left hvA]
    have hd := weightedDegree_tendsto_support G h₀ hs ⟨v, hvA⟩
    rw [← weightedDegree_positiveSupport G h₀ ⟨v, hvA⟩] at hd
    simpa only [Function.comp_def] using
      (shearerF_continuous.tendsto _ |>.comp hd).const_mul (u v)
  · by_cases hvB : v ∈ boundaryRemainder G (positiveSupport s₀)
    · simp only [ite_eq_left hvB, ite_eq_right hvA]
      exact tendsto_const_nhds
    · simp only [ite_eq_right hvB, ite_eq_right hvA]
      have hv₀ : s₀ v = 0 :=
        le_antisymm (le_of_not_gt ((mem_positiveSupport s₀ v).not.mp hvA)) (h₀ v)
      have hadj : ∃ a, 0 < s₀ a ∧ G.Adj v a := by
        rw [mem_boundaryRemainder] at hvB
        push Not at hvB
        obtain ⟨a, ha, hadj⟩ := hvB hvA
        exact ⟨a, (mem_positiveSupport s₀ a).mp ha, hadj⟩
      exact benchmark_summand_tendsto_boundary G u hpos h₀ hs hv₀ hadj

theorem boundary_complement_sum_tendsto [DecidableEq V] (G : SimpleGraph V)
    (u : V → ℝ) {s : ℕ → V → ℝ} {s₀ : V → ℝ} (hpos : ∀ n v, 0 < s n v)
    (h₀ : ∀ v, 0 ≤ s₀ v) (hs : Tendsto s atTop (𝓝 s₀)) :
    Tendsto (fun n ↦ ∑ v, if v ∈ boundaryRemainder G (positiveSupport s₀) then 0
      else u v * shearerF (weightedDegree G (s n) v)) atTop
      (𝓝 (benchmark (G.induce (positiveSupport s₀ : Set V))
        (fun v : positiveSupport s₀ ↦ u v) (fun v : positiveSupport s₀ ↦ s₀ v))) := by
  have he : (∑ v, if v ∈ positiveSupport s₀ then
      u v * shearerF (weightedDegree G s₀ v) else 0) =
      benchmark (G.induce (positiveSupport s₀ : Set V))
        (fun v : positiveSupport s₀ ↦ u v) (fun v : positiveSupport s₀ ↦ s₀ v) := by
    rw [Finset.sum_ite_mem_eq, ← Finset.sum_coe_sort]
    unfold benchmark
    apply Finset.sum_congr rfl
    intro v _
    rw [weightedDegree_positiveSupport G h₀ v]
  rw [← he]
  apply tendsto_finsetSum
  intro v _
  exact boundary_complement_summand_tendsto G u hpos h₀ hs v

theorem benchmark_le_complement_add_extremal [DecidableEq V] (G : SimpleGraph V)
    (B : Finset V) {u s : V → ℝ} (hu : ∀ v, 0 ≤ u v) (hs : ∀ v, 0 < s v) :
    benchmark G u s ≤ (∑ v, if v ∈ B then 0 else u v * shearerF (weightedDegree G s v)) +
      extremalBenchmark (G.induce (B : Set V)) (fun v : B ↦ u v) := by
  have he : benchmark G u s =
      (∑ v, if v ∈ B then 0 else u v * shearerF (weightedDegree G s v)) +
      weightSum (fun v ↦ u v * shearerF (weightedDegree G s v)) B := by
    unfold benchmark weightSum
    rw [← Finset.sum_ite_mem_eq B, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ B <;> simp only [hv, ite_true, ite_false, zero_add, add_zero]
  rw [he]
  apply add_le_add le_rfl
  exact (benchmark_restrict_le G B hu hs).trans
    (benchmark_le_extremalBenchmark (G.induce (B : Set V))
      (fun v ↦ hu v) (fun v ↦ hs v))

/-- Boundary limits split the extremal benchmark across the support and its nonneighbors. -/
theorem boundary_decomposition (G : SimpleGraph V) {u : V → ℝ} (hu : ∀ v, 0 ≤ u v)
    {s : ℕ → V → ℝ} {s₀ : V → ℝ} (hpos : ∀ n v, 0 < s n v)
    (h₀ : ∀ v, 0 ≤ s₀ v) (hs : Tendsto s atTop (𝓝 s₀))
    (hmax : Tendsto (fun n ↦ benchmark G u (s n)) atTop (𝓝 (extremalBenchmark G u))) :
    extremalBenchmark G u ≤
      extremalBenchmark (G.induce (positiveSupport s₀ : Set V))
        (fun v : positiveSupport s₀ ↦ u v) +
      extremalBenchmark (G.induce (boundaryRemainder G (positiveSupport s₀) : Set V))
        (fun v : boundaryRemainder G (positiveSupport s₀) ↦ u v) := by
  classical
  have ht := (boundary_complement_sum_tendsto G u hpos h₀ hs).add_const
    (extremalBenchmark (G.induce (boundaryRemainder G (positiveSupport s₀) : Set V))
      (fun v : boundaryRemainder G (positiveSupport s₀) ↦ u v))
  have hb := le_of_tendsto_of_tendsto hmax ht (Eventually.of_forall
    (fun n ↦ benchmark_le_complement_add_extremal G
      (boundaryRemainder G (positiveSupport s₀)) hu (hpos n)))
  apply hb.trans
  apply add_le_add _ le_rfl
  exact benchmark_le_extremalBenchmark (G.induce (positiveSupport s₀ : Set V))
    (fun v ↦ hu v) (fun v ↦ (mem_positiveSupport s₀ v).mp v.property)

end Cliquefree
