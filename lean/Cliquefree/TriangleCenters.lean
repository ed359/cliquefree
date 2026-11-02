module

public import Cliquefree.TriangleAverages

/-!
# Probability laws on centers incident to weighted triangles

Centers with zero local triangle mass are omitted, so the conditional neighbor laws are
well-defined even when the original graph contains isolated vertices.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Nonnegative vertex weights give nonnegative local triangle masses. -/
theorem localTriangleMass_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (x : V) : 0 ≤ localTriangleMass G w x :=
  Finset.sum_nonneg (fun v _ ↦
    mul_nonneg (hw v) (commonNeighborhoodMass_nonneg G hw x v))

/-- Centers with positive local weighted triangle mass. -/
def triangleCenters (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ) : Finset V := by
  classical
  exact Finset.univ.filter (fun x ↦ 0 < localTriangleMass G w x)

/-- Membership in the center set records exactly the positivity needed for conditioning. -/
@[simp] theorem mem_triangleCenters (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (x : V) : x ∈ triangleCenters G w ↔ 0 < localTriangleMass G w x := by
  classical
  simp [triangleCenters]

/-- Terms weighted by local triangle mass are unchanged on deleting zero-mass centers. -/
theorem sum_triangleCenters (G : SimpleGraph V) [DecidableRel G.Adj]
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (F : V → ℝ) :
    (∑ x : triangleCenters G w, localTriangleMass G w x * F x) =
      ∑ x, localTriangleMass G w x * F x := by
  classical
  have hs : (∑ x : triangleCenters G w, localTriangleMass G w x * F x) =
      ∑ x ∈ triangleCenters G w, localTriangleMass G w x * F x := by
    convert Finset.sum_coe_sort (triangleCenters G w)
      (fun x ↦ localTriangleMass G w x * F x) using 1
  rw [hs]
  simp only [triangleCenters, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 < localTriangleMass G w x
  · rw [ite_eq_left hx]
  · have hz : localTriangleMass G w x = 0 :=
      le_antisymm (le_of_not_gt hx) (localTriangleMass_nonneg G hw x)
    simp [hz]

/-- The center of a weighted ordered triangle, restricted to positive local triangle mass. -/
def triangleCenterLaw (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w) :
    FiniteLaw (triangleCenters G w) where
  mass x := w x * localTriangleMass G w x / (6 * triangleMass G w)
  nonneg x := div_nonneg (mul_nonneg (hw x) (localTriangleMass_nonneg G hw x))
    (by positivity)
  sum_mass := by
    rw [← Finset.sum_div]
    have hs : (∑ x : triangleCenters G w, w x * localTriangleMass G w x) =
        6 * triangleMass G w := by
      simp_rw [mul_comm (w _) (localTriangleMass G w _)]
      rw [sum_triangleCenters G hw]
      simpa only [mul_comm] using sum_weight_localTriangleMass G w
    rw [hs]
    exact div_self (by positivity)

/-- Any summand vanishing at zero local triangle mass can be restricted to positive centers. -/
theorem sum_triangleCenters_of_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (F : V → ℝ)
    (hF : ∀ x, localTriangleMass G w x = 0 → F x = 0) :
    (∑ x : triangleCenters G w, F x) = ∑ x, F x := by
  classical
  have hs : (∑ x : triangleCenters G w, F x) = ∑ x ∈ triangleCenters G w, F x := by
    convert Finset.sum_coe_sort (triangleCenters G w) F using 1
  rw [hs]
  simp only [triangleCenters, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : 0 < localTriangleMass G w x
  · rw [ite_eq_left hx]
  · rw [ite_eq_right hx, hF x (le_antisymm (le_of_not_gt hx) (localTriangleMass_nonneg G hw x))]

/-- At a zero-mass center every weighted directed incidence has zero triangle mass. -/
theorem localTriangleMass_zero_term (G : SimpleGraph V) [DecidableRel G.Adj]
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (x : V) (hx : localTriangleMass G w x = 0)
    (v : G.neighborFinset x) : w v * commonNeighborhoodMass G w x v = 0 := by
  apply le_antisymm
  · have h : w v * commonNeighborhoodMass G w x v ≤ localTriangleMass G w x := by
      apply Finset.single_le_sum (f := fun y : G.neighborFinset x ↦
        w y * commonNeighborhoodMass G w x y) (a := v) (s := Finset.univ)
      · intro y _
        exact mul_nonneg (hw y) (commonNeighborhoodMass_nonneg G hw x y)
      · exact Finset.mem_univ v
    simpa only [hx] using h
  · exact mul_nonneg (hw v) (commonNeighborhoodMass_nonneg G hw x v)

open Classical in
/-- A sum over the neighbor subtype is an adjacency-filtered sum on the whole vertex type. -/
theorem sum_neighbor_subtype (G : SimpleGraph V) [DecidableRel G.Adj]
    (x : V) (F : V → ℝ) :
    (∑ v : G.neighborFinset x, F v) = ∑ v, if G.Adj x v then F v else 0 := by
  classical
  calc
    _ = ∑ v ∈ G.neighborFinset x, F v := by
      convert Finset.sum_coe_sort (G.neighborFinset x) F using 1
    _ = _ := by rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]

/-- The center law followed by its stationary neighbor law equals the directed-edge law. -/
theorem triangleCenterLaw_conditional (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (x : triangleCenters G w) (v : G.neighborFinset x.val) :
    (triangleCenterLaw G w hw hT).mass x *
      (triangleStationaryLaw G w hw x (mem_triangleCenters G w x |>.mp x.property)).mass v =
        (triangleEdgeLaw G w hw hT).mass (x, v) :=
  (triangleEdgeLaw_conditional G w hw hT x
    (mem_triangleCenters G w x |>.mp x.property) v).symm

/-- Directed-edge expectations disintegrate into a positive center and a stationary neighbor. -/
theorem triangleEdgeLaw_expectation_eq_centers (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w) (F : V → V → ℝ) :
    (triangleEdgeLaw G w hw hT).expectation (fun e ↦ F e.1 e.2) =
      (triangleCenterLaw G w hw hT).expectation (fun x ↦
        (triangleStationaryLaw G w hw x
          (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦ F x v)) := by
  classical
  symm
  calc
    _ = ∑ x : triangleCenters G w, ∑ v : G.neighborFinset x.val,
        (triangleEdgeLaw G w hw hT).mass (x, v) * F x v := by
      simp only [FiniteLaw.expectation, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro v _
      rw [← mul_assoc, triangleCenterLaw_conditional]
    _ = ∑ x, ∑ v : G.neighborFinset x,
        (triangleEdgeLaw G w hw hT).mass (x, v) * F x v := by
      apply sum_triangleCenters_of_zero G hw
        (fun x ↦ ∑ v : G.neighborFinset x, (triangleEdgeLaw G w hw hT).mass (x, v) * F x v)
      intro x hx
      apply Finset.sum_eq_zero
      intro v _
      have hv := (G.mem_neighborFinset x v).mp v.property
      have hz := localTriangleMass_zero_term G hw x hx v
      simp only [triangleEdgeLaw, hv, ite_true, mul_assoc, hz, mul_zero, zero_div, zero_mul]
    _ = _ := by
      simp only [FiniteLaw.expectation, Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro x _
      rw [sum_neighbor_subtype G x
        (fun v ↦ (triangleEdgeLaw G w hw hT).mass (x, v) * F x v)]
      apply Finset.sum_congr rfl
      intro v _
      by_cases hv : G.Adj x v
      · rw [ite_eq_left hv]
      · simp [triangleEdgeLaw, hv]

/-- A local-walk observable on directed edges, set to zero on nonedges. -/
def triangleStepAverage (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (F : V → V → V → ℝ) (x v : V) : ℝ :=
  if h : G.Adj x v then
    (triangleWalk G w hw x (hC x) ⟨v, (G.mem_neighborFinset x v).mpr h⟩).expectation
      (fun z ↦ F x v z)
  else 0

/-- On an incidence the local average equals its neighborhood walk expectation. -/
theorem triangleStepAverage_of_adj (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (F : V → V → V → ℝ) (x : V) (v : G.neighborFinset x) :
    triangleStepAverage G w hw hC F x v =
      (triangleWalk G w hw x (hC x) v).expectation (fun z ↦ F x v z) := by
  simp only [triangleStepAverage, (G.mem_neighborFinset x v).mp v.property, dite_true]

open Classical in
/-- Multiplying by common-neighbor mass removes the local walk normalization. -/
theorem common_mul_triangleStepAverage (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (F : V → V → V → ℝ) (x v : V) (hxv : G.Adj x v) :
    commonNeighborhoodMass G w x v * triangleStepAverage G w hw hC F x v =
      ∑ z, if G.Adj x z ∧ G.Adj v z then w z * F x v z else 0 := by
  classical
  have hc := (hC x v hxv).ne'
  simp only [triangleStepAverage, hxv, dite_true, FiniteLaw.expectation,
    triangleWalk, Finset.mul_sum]
  calc
    _ = ∑ z : G.neighborFinset x, if G.Adj v z then w z * F x v z else 0 := by
      apply Finset.sum_congr rfl
      intro z _
      split_ifs <;> field_simp
      ring
    _ = _ := by
      rw [sum_neighbor_subtype G x (fun z ↦ if G.Adj v z then w z * F x v z else 0)]
      apply Finset.sum_congr rfl
      intro z _
      by_cases h₁ : G.Adj x z <;> by_cases h₂ : G.Adj v z <;> simp [h₁, h₂]

/-- A triangle observable can be averaged over the local walk at its first directed edge. -/
theorem orderedTriangleSum_walk_average (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (F : V → V → V → ℝ) :
    orderedTriangleSum G w F =
      orderedTriangleSum G w (fun x v _ ↦ triangleStepAverage G w hw hC F x v) := by
  classical
  rw [orderedTriangleSum_incidence]
  unfold orderedTriangleSum
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro v _
  by_cases hxv : G.Adj x v
  · rw [ite_eq_left hxv]
    calc
      _ = w x * w v * ∑ z, if G.Adj x z ∧ G.Adj v z then w z * F x v z else 0 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z _
        have hzx : G.Adj z x ↔ G.Adj x z := G.adj_comm z x
        simp only [hxv, true_and, hzx, and_comm]
        split_ifs <;> ring
      _ = _ := by rw [← common_mul_triangleStepAverage G w hw hC F x v hxv]; ring
  · simp only [hxv, false_and, ite_false, Finset.sum_const_zero]

/-- The weighted ordered-triangle law is a positive center, stationary neighbor, and local step. -/
theorem orderedTriangleSum_eq_center_walk (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (F : V → V → V → ℝ) :
    orderedTriangleSum G w F = (6 * triangleMass G w) *
      (triangleCenterLaw G w hw hT).expectation (fun x ↦
        (triangleStationaryLaw G w hw x
          (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
            (triangleWalk G w hw x (hC x) v).expectation (fun z ↦ F x v z))) := by
  rw [orderedTriangleSum_walk_average G w hw hC F,
    orderedTriangleSum_eq_edgeExpectation G w hw hT (triangleStepAverage G w hw hC F),
    triangleEdgeLaw_expectation_eq_centers]
  congr 1
  apply congrArg
  funext x
  apply congrArg
  funext v
  exact triangleStepAverage_of_adj G w hw hC F x v

end Cliquefree
