module

public import Cliquefree.GraphIdentities

/-!
# Weighted deletion counting

These finite graph identities isolate the counting needed for averaged deletion of closed
neighborhoods. They use no scalar analysis or stationarity assumptions.
-/

@[expose] public section

open scoped BigOperators

namespace Cliquefree

noncomputable section

variable {V : Type*} [Fintype V]

/-- The total weight of the common open neighbors of two vertices. -/
def commonNeighborhoodMass (G : SimpleGraph V) (w : V → ℝ) (x y : V) : ℝ := by
  classical
  exact ∑ z, if G.Adj x z ∧ G.Adj y z then w z else 0

/-- Cross mass can be expressed on the whole vertex type by membership indicators. -/
theorem crossMass_eq_sum_univ (G : SimpleGraph V) [DecidableRel G.Adj] [DecidableEq V]
    (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B =
      ∑ x, ∑ y, if x ∈ A ∧ y ∈ B ∧ G.Adj x y then w x * w y else 0 := by
  classical
  simp only [crossMass, ite_and, Finset.sum_ite_irrel, Finset.sum_ite_mem, Finset.univ_inter,
    Finset.sum_const_zero]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> rfl

/-- An adjacent pair belongs to exactly its endpoint neighborhoods and its common-neighbor
neighborhoods; their weighted inclusion coefficient is the sum of those three masses. -/
theorem sum_weight_closedNeighborhood_pair (G : SimpleGraph V) [DecidableEq V]
    (w : V → ℝ) {y z : V} (hyz : G.Adj y z) :
    (∑ x, if y ∈ closedNeighborhood G x ∧ z ∈ closedNeighborhood G x then w x else 0) =
      w y + w z + commonNeighborhoodMass G w y z := by
  classical
  have hpoint (x : V) :
      (if y ∈ closedNeighborhood G x ∧ z ∈ closedNeighborhood G x then w x else 0) =
      (if x = y then w x else 0) + (if x = z then w x else 0) +
      (if G.Adj y x ∧ G.Adj z x then w x else 0) := by
    by_cases hxy : x = y <;> by_cases hxz : x = z <;>
      simp_all [mem_closedNeighborhood, G.adj_comm, eq_comm]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp [commonNeighborhoodMass]

/-- Rooting a triangle at an oriented edge counts each unordered triangle six times. -/
theorem sum_edge_commonNeighborhoodMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) :
    (∑ y, ∑ z, if G.Adj y z then w y * w z * commonNeighborhoodMass G w y z else 0) =
      6 * triangleMass G w := by
  classical
  unfold triangleMass
  conv_rhs => ring_nf
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  by_cases hyz : G.Adj y z
  · simp only [hyz, ite_true, true_and, commonNeighborhoodMass, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    by_cases hyx : G.Adj y x <;> by_cases hzx : G.Adj z x <;>
      simp_all [G.adj_comm]
  · simp [hyz]

/-- Swapping the center and edge sums exposes the inclusion coefficient of each edge. -/
theorem sum_closedNeighborhood_crossMass_eq_pair_sum (G : SimpleGraph V)
    [DecidableRel G.Adj] [DecidableEq V] (w : V → ℝ) :
    (∑ x, w x * crossMass G w (closedNeighborhood G x) (closedNeighborhood G x)) =
      ∑ y, ∑ z, if G.Adj y z then
        w y * w z * (∑ x,
          if y ∈ closedNeighborhood G x ∧ z ∈ closedNeighborhood G x then w x else 0)
        else 0 := by
  classical
  simp_rw [crossMass_eq_sum_univ, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hyz : G.Adj y z
  · simp only [hyz, and_true, ite_true]
    apply Finset.sum_congr rfl
    intro x _
    split_ifs <;> ring
  · simp [hyz]

/-- The first endpoint contribution of an oriented edge is a squared-weight neighborhood sum. -/
theorem sum_edge_first_endpoint (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ) :
    (∑ y, ∑ z, if G.Adj y z then w y * w z * w y else 0) =
      ∑ y, w y ^ 2 * neighborhoodMass G w y := by
  classical
  apply Finset.sum_congr rfl
  intro y _
  simp only [neighborhoodMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> ring

/-- The second endpoint gives the same total contribution by edge symmetry. -/
theorem sum_edge_second_endpoint (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ) :
    (∑ y, ∑ z, if G.Adj y z then w y * w z * w z else 0) =
      ∑ y, w y ^ 2 * neighborhoodMass G w y := by
  classical
  rw [sum_adj_swap]
  convert sum_edge_first_endpoint G w using 1
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  split_ifs <;> ring

/-- Averaging the internal cross mass of closed neighborhoods produces the endpoint term
and six times the unordered triangle mass. Cross mass is twice internal edge mass,
giving the graph-counting identity needed for the averaged deletion bound. -/
theorem sum_weight_closedNeighborhood_crossMass (G : SimpleGraph V) (w : V → ℝ) :
    (∑ x, w x * crossMass G w (closedNeighborhood G x) (closedNeighborhood G x)) =
      2 * (∑ v, w v ^ 2 * neighborhoodMass G w v) + 6 * triangleMass G w := by
  classical
  rw [sum_closedNeighborhood_crossMass_eq_pair_sum]
  have hterm (y z : V) :
      (if G.Adj y z then
        w y * w z * (∑ x,
          if y ∈ closedNeighborhood G x ∧ z ∈ closedNeighborhood G x then w x else 0)
        else 0) =
      (if G.Adj y z then w y * w z * w y else 0) +
      (if G.Adj y z then w y * w z * w z else 0) +
      (if G.Adj y z then w y * w z * commonNeighborhoodMass G w y z else 0) := by
    by_cases hyz : G.Adj y z
    · simp only [hyz, ite_true, sum_weight_closedNeighborhood_pair G w hyz]
      ring
    · simp [hyz]
  simp_rw [hterm, Finset.sum_add_distrib]
  rw [sum_edge_first_endpoint, sum_edge_second_endpoint, sum_edge_commonNeighborhoodMass]
  ring

/-- Updating one coordinate changes a finite bilinear sum by its exact linear contribution. -/
theorem sum_update_mul [DecidableEq V] (w a : V → ℝ) (x : V) (t : ℝ) :
    (∑ v, Function.update w x t v * a v) =
      (∑ v, w v * a v) + (t - w x) * a x := by
  classical
  have hpoint (v : V) : Function.update w x t v * a v =
      w v * a v + if v = x then (t - w x) * a x else 0 := by
    by_cases hv : v = x
    · subst v
      simp only [Function.update_self, ite_true]
      ring
    · simp [hv, Function.update_of_ne]
  simp_rw [hpoint, Finset.sum_add_distrib]
  simp

/-- A coordinate does not belong to its own open neighborhood, so changing it leaves that
neighborhood's mass unchanged. -/
theorem neighborhoodMass_update_self (G : SimpleGraph V) [DecidableEq V]
    (w : V → ℝ) (x : V) (t : ℝ) :
    neighborhoodMass G (Function.update w x t) x = neighborhoodMass G w x := by
  classical
  unfold neighborhoodMass
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y = x
  · subst y
    simp
  · simp [hy, Function.update_of_ne]

/-- Edge mass changes linearly when one vertex weight is updated. -/
theorem edgeMass_update (G : SimpleGraph V) [DecidableEq V]
    (w : V → ℝ) (x : V) (t : ℝ) :
    edgeMass G (Function.update w x t) = edgeMass G w +
      (t - w x) * neighborhoodMass G w x := by
  have hdouble : 2 * edgeMass G (Function.update w x t) =
      2 * edgeMass G w + 2 * (t - w x) * neighborhoodMass G w x := by
    calc
      _ = ∑ v, Function.update w x t v *
          neighborhoodMass G (Function.update w x t) v :=
        (weighted_handshake G (Function.update w x t)).symm
      _ = (∑ v, w v * neighborhoodMass G (Function.update w x t) v) +
          (t - w x) * neighborhoodMass G (Function.update w x t) x :=
        sum_update_mul w (neighborhoodMass G (Function.update w x t)) x t
      _ = (∑ v, Function.update w x t v * neighborhoodMass G w v) +
          (t - w x) * neighborhoodMass G w x := by
        rw [sum_mul_neighborhoodMass_comm G w (Function.update w x t),
          neighborhoodMass_update_self]
      _ = ((∑ v, w v * neighborhoodMass G w v) +
          (t - w x) * neighborhoodMass G w x) +
          (t - w x) * neighborhoodMass G w x := by
        rw [sum_update_mul]
      _ = _ := by rw [weighted_handshake]; ring
  linarith

end

end Cliquefree
