module

public import Cliquefree.Basic

/-!
# Weighted graph identities

The lifting identity writes the difference between a weighted degree sum and twice the edge
mass as a sum of squares. Its ordered double sum is divided by two: the summand is unchanged
when its endpoints are exchanged, so each unordered edge contributes once.
-/

@[expose] public section

open scoped BigOperators

namespace Cliquefree

noncomputable section

/-- The two reciprocal square-root ratios turn the edge contribution into a square. -/
theorem sqrt_ratio_square {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (x y : ℝ) :
    (Real.sqrt (b / a) * x - Real.sqrt (a / b) * y) ^ 2 =
      b / a * x ^ 2 + a / b * y ^ 2 - 2 * x * y := by
  have hprod : Real.sqrt (b / a) * Real.sqrt (a / b) = 1 := by
    rw [← Real.sqrt_mul (div_nonneg hb.le ha.le)]
    have hratio : b / a * (a / b) = 1 := by field_simp
    rw [hratio, Real.sqrt_one]
  calc
    _ = Real.sqrt (b / a) ^ 2 * x ^ 2 + Real.sqrt (a / b) ^ 2 * y ^ 2 -
        2 * (Real.sqrt (b / a) * Real.sqrt (a / b)) * (x * y) := by ring
    _ = _ := by
      rw [Real.sq_sqrt (div_nonneg hb.le ha.le), Real.sq_sqrt (div_nonneg ha.le hb.le),
        hprod]
      ring

variable {V : Type*} [Fintype V]

/-- Reversing both endpoints preserves any ordered sum over graph edges. -/
theorem sum_adj_swap (G : SimpleGraph V) [DecidableRel G.Adj] (F : V → V → ℝ) :
    (∑ x, ∑ y, if G.Adj x y then F x y else 0) =
      ∑ x, ∑ y, if G.Adj x y then F y x else 0 := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  simp only [G.adj_comm]

/-- The weighted neighborhood bilinear form is symmetric. -/
theorem sum_mul_neighborhoodMass_comm (G : SimpleGraph V) (a b : V → ℝ) :
    (∑ x, a x * neighborhoodMass G b x) = ∑ x, b x * neighborhoodMass G a x := by
  classical
  simp only [neighborhoodMass, Finset.mul_sum, mul_ite, mul_zero]
  rw [sum_adj_swap]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  simp only [mul_comm]

/-- Expanding a weighted degree against a square gives an ordered edge sum. -/
theorem weightedDegree_mul_sq_eq_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (s q : V → ℝ) (x : V) :
    weightedDegree G s x * q x ^ 2 =
      ∑ y, if G.Adj x y then s y / s x * q x ^ 2 else 0 := by
  classical
  simp only [weightedDegree, neighborhoodMass, Finset.sum_div, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

/-- The weighted lift discrepancy is a sum of edge squares. The ordered sum is divided by two,
so each unordered edge contributes its squared discrepancy once. -/
theorem weighted_lift_square_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (s q : V → ℝ) (hs : ∀ v, 0 < s v) :
    (∑ v, weightedDegree G s v * q v ^ 2) - 2 * edgeMass G q =
      (∑ x, ∑ y, if G.Adj x y then
        (Real.sqrt (s y / s x) * q x - Real.sqrt (s x / s y) * q y) ^ 2 else 0) / 2 := by
  classical
  have hdiag : (∑ x, ∑ y, if G.Adj x y then s y / s x * q x ^ 2 else 0) =
      ∑ v, weightedDegree G s v * q v ^ 2 := by
    simp_rw [weightedDegree_mul_sq_eq_sum]
  have hswap : (∑ x, ∑ y, if G.Adj x y then s x / s y * q y ^ 2 else 0) =
      ∑ x, ∑ y, if G.Adj x y then s y / s x * q x ^ 2 else 0 := by
    exact (sum_adj_swap G (fun x y ↦ s y / s x * q x ^ 2)).symm
  have hedge : (∑ x, ∑ y, if G.Adj x y then q x * q y else 0) = 2 * edgeMass G q := by
    rw [← weighted_handshake]
    simp only [neighborhoodMass, Finset.mul_sum, mul_ite, mul_zero]
  have hexpand : ∀ x y,
      (if G.Adj x y then
        (Real.sqrt (s y / s x) * q x - Real.sqrt (s x / s y) * q y) ^ 2 else 0) =
      (if G.Adj x y then s y / s x * q x ^ 2 else 0) +
      (if G.Adj x y then s x / s y * q y ^ 2 else 0) -
      2 * (if G.Adj x y then q x * q y else 0) := by
    intro x y
    split_ifs
    · rw [sqrt_ratio_square (hs x) (hs y)]
      ring
    · ring
  symm
  simp_rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hswap, hdiag, hedge]
  ring

/-- The weighted quadratic degree sum dominates twice the edge mass. -/
theorem weighted_lift_discrepancy_nonneg (G : SimpleGraph V) (s q : V → ℝ)
    (hs : ∀ v, 0 < s v) :
    0 ≤ (∑ v, weightedDegree G s v * q v ^ 2) - 2 * edgeMass G q := by
  classical
  rw [weighted_lift_square_identity G s q hs]
  apply div_nonneg _ (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  split_ifs
  · exact sq_nonneg _
  · exact le_rfl

/-- The mass of a closed neighborhood is the center weight plus the open-neighborhood mass. -/
theorem weightSum_closedNeighborhood (G : SimpleGraph V) (a : V → ℝ) (x : V) :
    weightSum a (closedNeighborhood G x) = a x + neighborhoodMass G a x := by
  classical
  have hclosed : closedNeighborhood G x = insert x (G.neighborFinset x) := by
    ext y
    simp [closedNeighborhood, SimpleGraph.mem_neighborFinset]
  rw [weightSum, hclosed, Finset.sum_insert (by simp)]
  congr 1
  simp only [neighborhoodMass, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]

/-- Averaging a vertex sum over closed neighborhoods gives its exact inclusion coefficient. -/
theorem sum_weight_closedNeighborhood (G : SimpleGraph V) (w a : V → ℝ) :
    (∑ x, w x * weightSum a (closedNeighborhood G x)) =
      ∑ v, (w v + neighborhoodMass G w v) * a v := by
  simp_rw [weightSum_closedNeighborhood, mul_add]
  rw [Finset.sum_add_distrib, sum_mul_neighborhoodMass_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  ring

end

end Cliquefree
