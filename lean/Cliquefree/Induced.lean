module

public import Cliquefree.Basic

/-!
# Extending induced-subgraph weights by zero
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Extend weights on an induced vertex set by zero outside that set. -/
def extendByZero (A : Finset V) (w : A → ℝ) : V → ℝ := by
  classical
  exact fun v ↦ if hv : v ∈ A then w ⟨v, hv⟩ else 0

omit [Fintype V] in
/-- Zero extension preserves each coordinate in its original domain. -/
@[simp] theorem extendByZero_coe (A : Finset V) (w : A → ℝ) (v : A) :
    extendByZero A w v = w v := by
  classical
  simp [extendByZero, v.property]

omit [Fintype V] in
/-- Zero extension vanishes outside its original domain. -/
theorem extendByZero_not_mem (A : Finset V) (w : A → ℝ) {v : V} (hv : v ∉ A) :
    extendByZero A w v = 0 := by
  classical
  simp [extendByZero, hv]

/-- Zero extension preserves total mass. -/
theorem sum_extendByZero (A : Finset V) (w : A → ℝ) :
    ∑ v, extendByZero A w v = ∑ v : A, w v := by
  classical
  simpa only [extendByZero, Finset.univ_eq_attach] using
    (Finset.sum_attach_eq_sum_dite A w).symm

/-- Neighborhood mass of a zero extension is the sum over the induced vertex set. -/
theorem neighborhoodMass_extendByZero (G : SimpleGraph V) (A : Finset V) (w : A → ℝ)
    (v : V) [DecidableRel G.Adj] :
    neighborhoodMass G (extendByZero A w) v =
      ∑ y : A, if G.Adj v y then w y else 0 := by
  classical
  rw [← sum_extendByZero A (fun y ↦ if G.Adj v y then w y else 0)]
  unfold neighborhoodMass
  apply Finset.sum_congr rfl
  intro y _
  unfold extendByZero
  split_ifs <;> simp_all

/-- At an induced vertex, neighborhood mass agrees with the induced graph. -/
theorem neighborhoodMass_extendByZero_coe (G : SimpleGraph V) (A : Finset V) (w : A → ℝ)
    (v : A) :
    neighborhoodMass G (extendByZero A w) v = neighborhoodMass (G.induce (A : Set V)) w v := by
  classical
  rw [neighborhoodMass_extendByZero]
  rfl

/-- Zero extension preserves the weighted edge mass of an induced subgraph. -/
theorem edgeMass_extendByZero (G : SimpleGraph V) (A : Finset V) (w : A → ℝ) :
    edgeMass G (extendByZero A w) = edgeMass (G.induce (A : Set V)) w := by
  classical
  unfold edgeMass
  congr 1
  trans ∑ v, extendByZero A
    (fun x ↦ w x * neighborhoodMass (G.induce (A : Set V)) w x) v
  swap
  · exact sum_extendByZero A _
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ A
  · have h := neighborhoodMass_extendByZero_coe G A w ⟨v, hv⟩
    simpa only [extendByZero, dite_eq_left hv] using congrArg (fun x ↦ w ⟨v, hv⟩ * x) h
  · simp [extendByZero, hv]

omit [Fintype V] in
/-- Restricting a global weighting to a finite set gives its finite weight sum. -/
theorem sum_restrict_eq_weightSum (A : Finset V) (w : V → ℝ) :
    (∑ v : A, w v) = weightSum w A := by
  classical
  exact Finset.sum_coe_sort A w

end Cliquefree
