module

public import Cliquefree.TriangleRetention
public import Cliquefree.TriangleWalks

/-!
# Triangle averages through the reversible edge law

Weighted ordered-triangle sums become expectations under the directed-edge law and its
conditional local walk, linking entropy estimates to the splitting retention bound.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

open Classical in
/-- Summing over the third triangle vertex gives the common-neighbor incidence weight. -/
theorem orderedTriangleSum_incidence (G : SimpleGraph V) (w : V → ℝ)
    (F : V → V → ℝ) :
    orderedTriangleSum G w (fun x y _ ↦ F x y) =
      ∑ x, ∑ y, if G.Adj x y then w x * w y * commonNeighborhoodMass G w x y * F x y
        else 0 := by
  classical
  unfold orderedTriangleSum
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : G.Adj x y
  · rw [ite_eq_left hxy]
    simp only [commonNeighborhoodMass, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    have hzx : G.Adj z x ↔ G.Adj x z := G.adj_comm z x
    simp only [hxy, true_and, hzx, and_comm]
    split_ifs <;> simp
  · simp only [hxy, false_and, ite_false, Finset.sum_const_zero]

open Classical in
/-- The directed-edge law is the normalized weighted ordered-triangle incidence sum. -/
theorem triangleEdgeLaw_expectation (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (F : V → V → ℝ) :
    (triangleEdgeLaw G w hw hT).expectation (fun e ↦ F e.1 e.2) =
      orderedTriangleSum G w (fun x y _ ↦ F x y) / (6 * triangleMass G w) := by
  classical
  rw [orderedTriangleSum_incidence]
  unfold FiniteLaw.expectation
  simp only [triangleEdgeLaw, Fintype.sum_prod_type, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> ring

/-- Multiplication by total ordered-triangle mass reverses incidence normalization. -/
theorem orderedTriangleSum_eq_edgeExpectation (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (F : V → V → ℝ) :
    orderedTriangleSum G w (fun x y _ ↦ F x y) =
      (6 * triangleMass G w) * (triangleEdgeLaw G w hw hT).expectation
        (fun e ↦ F e.1 e.2) := by
  rw [triangleEdgeLaw_expectation]
  field_simp

/-- Cross mass against a whole neighborhood sums the corresponding common-neighbor masses. -/
theorem crossMass_neighbor_eq_common (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (B : Finset V) (v : V) :
    crossMass G w B (G.neighborFinset v) = ∑ x ∈ B, w x * commonNeighborhoodMass G w v x := by
  classical
  simp only [commonNeighborhoodMass_eq_sum_neighbor,
    Finset.mul_sum, mul_ite, mul_zero, crossMass]
  apply Finset.sum_congr rfl
  intro x _
  convert (Finset.sum_coe_sort (G.neighborFinset v)
    (fun y ↦ if G.Adj x y then w x * w y else 0)).symm using 1
  congr 3
  funext y
  by_cases h : G.Adj x y <;> simp [h]

open Classical in
/-- An exceptional directed pair set is counted by neighborhood cross masses. -/
theorem orderedTriangleSum_incidence_set (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (B : V → Finset V) (hB : ∀ v, B v ⊆ G.neighborFinset v) :
    orderedTriangleSum G w (fun x v _ ↦ if x ∈ B v then 1 else 0) =
      ∑ v, w v * crossMass G w (B v) (G.neighborFinset v) := by
  classical
  rw [orderedTriangleSum_incidence, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [crossMass_neighbor_eq_common, Finset.mul_sum]
  calc
    _ = ∑ x, if x ∈ B v then w v * (w x * commonNeighborhoodMass G w v x) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ B v
      · have hvx := (G.mem_neighborFinset v x).mp (hB v hx)
        simp only [hx, ite_true, hvx.symm, mul_one, commonNeighborhoodMass_comm G w x v]
        ring
      · simp only [hx, ite_false, mul_zero, ite_self]
    _ = _ := by simp

open Classical in
/-- Exceptional-pair probability is its neighborhood cross mass divided by six triangle mass. -/
theorem triangleEdgeLaw_exceptional_probability (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (B : V → Finset V) (hB : ∀ v, B v ⊆ G.neighborFinset v) :
    (triangleEdgeLaw G w hw hT).expectation (fun e ↦ if e.1 ∈ B e.2 then 1 else 0) =
      (∑ v, w v * crossMass G w (B v) (G.neighborFinset v)) / (6 * triangleMass G w) := by
  classical
  rw [triangleEdgeLaw_expectation G w hw hT (fun x v ↦ if x ∈ B v then 1 else 0),
    orderedTriangleSum_incidence_set G w B hB]

end Cliquefree
