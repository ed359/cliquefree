module

public import Cliquefree.Isolated

/-!
# Finite reductions for the existence induction
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- Clique exclusion passes to every induced graph. -/
theorem cliqueFree_induce (G : SimpleGraph V) (A : Finset V) {r : ℕ}
    (hG : G.CliqueFree r) : (G.induce (A : Set V)).CliqueFree r :=
  (SimpleGraph.cliqueFree_induce_iff G (A : Set V) r).mpr hG.cliqueFreeOn

/-- A proper induced vertex set has strictly fewer vertices. -/
theorem card_induced_lt {A : Finset V} (hA : A ≠ Finset.univ) :
    Fintype.card (A : Set V) < Fintype.card V := by
  have h := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ A, hA⟩)
  simpa using h

/-- Erasing any vertex produces a proper induced vertex set. -/
theorem erase_univ_ne_univ [DecidableEq V] (x : V) :
    (Finset.univ : Finset V).erase x ≠ Finset.univ := by
  intro h
  have hx : x ∈ (Finset.univ : Finset V).erase x := by
    rw [h]
    exact Finset.mem_univ x
  exact Finset.notMem_erase x Finset.univ hx


end Cliquefree
