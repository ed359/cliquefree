module

public import Cliquefree.Restrictions

/-!
# Combining and restricting independent sets
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Independent sets with no edges between them have an independent union. -/
theorem independent_union_of_no_edges [DecidableEq V] (G : SimpleGraph V)
    {I J : Finset V} (hI : Independent G I) (hJ : Independent G J)
    (hIJ : ∀ x ∈ I, ∀ y ∈ J, ¬G.Adj x y) : Independent G (I ∪ J) := by
  intro x hx y hy hxy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact hI hx hy hxy
  · exact hIJ x hx y hy
  · exact fun h ↦ hIJ y hy x hx h.symm
  · exact hJ hx hy hxy

omit [Fintype V] in
/-- Nonadjacent disjoint induced graphs supply independent sets whose weights add. -/
theorem independenceWeight_induce_add_le [Finite V] (G : SimpleGraph V) (u : V → ℝ)
    {A B : Finset V} (hAB : Disjoint A B)
    (hE : ∀ a ∈ A, ∀ b ∈ B, ¬G.Adj a b) :
    independenceWeight (G.induce (A : Set V)) (fun v ↦ u v) +
      independenceWeight (G.induce (B : Set V)) (fun v ↦ u v) ≤ independenceWeight G u := by
  classical
  obtain ⟨I, hI, hvI⟩ := independenceWeight_attained (G.induce (A : Set V)) (fun v ↦ u v)
  obtain ⟨J, hJ, hvJ⟩ := independenceWeight_attained (G.induce (B : Set V)) (fun v ↦ u v)
  let I' := I.map (Function.Embedding.subtype (· ∈ A))
  let J' := J.map (Function.Embedding.subtype (· ∈ B))
  have hiA : I' ⊆ A := by
    intro v hv
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hv
    exact v.property
  have hjB : J' ⊆ B := by
    intro v hv
    obtain ⟨v, _, rfl⟩ := Finset.mem_map.mp hv
    exact v.property
  have hij : Disjoint I' J' := hAB.mono hiA hjB
  have hind : Independent G (I' ∪ J') :=
    independent_union_of_no_edges G (independent_map_subtype G A hI)
      (independent_map_subtype G B hJ) (fun x hx y hy ↦ hE x (hiA hx) y (hjB hy))
  have hsum : weightSum u (I' ∪ J') =
      independenceWeight (G.induce (A : Set V)) (fun v ↦ u v) +
        independenceWeight (G.induce (B : Set V)) (fun v ↦ u v) := by
    change (∑ v ∈ I' ∪ J', u v) = _
    rw [Finset.sum_union hij]
    change weightSum u I' + weightSum u J' = _
    rw [weightSum_map_subtype, weightSum_map_subtype]
    exact congrArg₂ (· + ·) hvI hvJ
  rw [← hsum]
  exact weightSum_le_independenceWeight G u hind

end Cliquefree
