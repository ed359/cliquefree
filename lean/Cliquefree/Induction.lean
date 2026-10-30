module

public import Cliquefree.Induced
public import Cliquefree.Potential

/-!
# Induced subgraphs in the existence induction
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- An independent set in an induced graph remains independent in the original graph. -/
theorem independent_map_subtype (G : SimpleGraph V) (A : Finset V) {I : Finset A}
    (hI : Independent (G.induce (A : Set V)) I) :
    Independent G (I.map (Function.Embedding.subtype (· ∈ A))) := by
  intro a ha b hb hab
  obtain ⟨a, haI, rfl⟩ := Finset.mem_map.mp ha
  obtain ⟨b, hbI, rfl⟩ := Finset.mem_map.mp hb
  exact hI haI hbI (fun he ↦ hab (congrArg Subtype.val he))

omit [Fintype V] in
/-- Embedding a finite induced vertex set preserves its objective weight. -/
theorem weightSum_map_subtype (A : Finset V) (I : Finset A) (u : V → ℝ) :
    weightSum u (I.map (Function.Embedding.subtype (· ∈ A))) =
      weightSum (fun v : A ↦ u v) I := by
  simp [weightSum]

omit [Fintype V] in
/-- Passing to an induced graph cannot increase the maximum independent weight. -/
theorem independenceWeight_induce_le [Finite V] (G : SimpleGraph V) (A : Finset V) (u : V → ℝ) :
    independenceWeight (G.induce (A : Set V)) (fun v ↦ u v) ≤ independenceWeight G u := by
  obtain ⟨I, hI, hvalue⟩ := independenceWeight_attained (G.induce (A : Set V)) (fun v ↦ u v)
  calc
    _ = weightSum (fun v : (A : Set V) ↦ u v) I := hvalue.symm
    _ = weightSum u (I.map (Function.Embedding.subtype (· ∈ A))) := by simp [weightSum]
    _ ≤ _ := weightSum_le_independenceWeight G u (independent_map_subtype G A hI)

/-- Zero extension preserves the potential of an induced subgraph. -/
theorem graphPotential_extendByZero (G : SimpleGraph V) (A : Finset V) (u : V → ℝ)
    (w : A → ℝ) :
    graphPotential G u (extendByZero A w) =
      graphPotential (G.induce (A : Set V)) (fun v ↦ u v) w := by
  classical
  unfold graphPotential
  rw [edgeMass_extendByZero]
  congr 1
  trans ∑ v, extendByZero A (fun x ↦ scalarPotential (u x) (w x)) v
  · apply Finset.sum_congr rfl
    intro v _
    by_cases hv : v ∈ A <;> simp [extendByZero, hv]
  · exact sum_extendByZero A _

/-- Erasing a vertex set is zero extension from its complement. -/
theorem eraseWeights_eq_extend_compl [DecidableEq V] (w : V → ℝ) (A : Finset V) :
    eraseWeights w A = extendByZero (Finset.univ \ A) (fun v ↦ w v) := by
  classical
  funext v
  by_cases hv : v ∈ A <;> simp [eraseWeights, extendByZero, hv]

/-- Erasing vertices in the potential agrees exactly with passing to the induced complement. -/
theorem graphPotential_eraseWeights_eq_induce [DecidableEq V] (G : SimpleGraph V) (A : Finset V)
    (u w : V → ℝ) :
    graphPotential G u (eraseWeights w A) =
      graphPotential (G.induce ((Finset.univ \ A : Finset V) : Set V))
        (fun v ↦ u v) (fun v ↦ w v) := by
  rw [eraseWeights_eq_extend_compl, graphPotential_extendByZero]
  rfl

/-- A selected vertex adds its weight to the independent optimum outside its closed neighborhood. -/
theorem selection_independenceWeight_le [DecidableEq V] (G : SimpleGraph V) (u : V → ℝ) (x : V) :
    u x + independenceWeight
      (G.induce ((Finset.univ \ closedNeighborhood G x : Finset V) : Set V))
      (fun v ↦ u v) ≤ independenceWeight G u := by
  classical
  let A := Finset.univ \ closedNeighborhood G x
  obtain ⟨I, hI, hv⟩ := independenceWeight_attained (G.induce (A : Set V)) (fun v ↦ u v)
  change u x + independenceWeight (G.induce (A : Set V)) (fun v ↦ u v) ≤ _
  rw [← hv]
  convert selection_weight_le_independenceWeight G u
    (x := x) (independent_map_subtype G A hI) ?_ using 1
  · simp [weightSum]
  apply Finset.disjoint_left.mpr
  intro v hv hn
  obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hv
  exact (Finset.mem_sdiff.mp v.property).2 hn


end Cliquefree
