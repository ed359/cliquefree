module

public import Cliquefree.DeletionIdentities
public import Cliquefree.Potential

/-!
# Exact deletion of weighted vertices

Deleting a vertex set is represented by zeroing its auxiliary weights. The identities here
use the scalar potential and its coordinate residual. The graph-counting steps hold for
arbitrary real weights and do not require stationarity.
-/

@[expose] public section

open scoped BigOperators

namespace Cliquefree

noncomputable section

variable {V : Type*} [Fintype V]

/-- Cross mass from a set to the whole graph is its weighted incident-neighborhood sum. -/
theorem crossMass_univ_right (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G w A Finset.univ = ∑ v ∈ A, w v * neighborhoodMass G w v := by
  classical
  simp only [crossMass, neighborhoodMass, Finset.mul_sum, mul_ite, mul_zero]

/-- Erasing a vertex set subtracts its two oriented incident masses and restores the
internal cross mass that was subtracted twice. -/
theorem crossMass_eraseWeights_univ (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    crossMass G (eraseWeights w A) Finset.univ Finset.univ =
      crossMass G w Finset.univ Finset.univ - crossMass G w A Finset.univ -
      crossMass G w Finset.univ A + crossMass G w A A := by
  classical
  simp only [crossMass_eq_sum_univ, Finset.mem_univ, true_and]
  have hpoint (x y : V) :
      (if G.Adj x y then eraseWeights w A x * eraseWeights w A y else 0) =
      (if G.Adj x y then w x * w y else 0) -
      (if x ∈ A ∧ G.Adj x y then w x * w y else 0) -
      (if y ∈ A ∧ G.Adj x y then w x * w y else 0) +
      (if x ∈ A ∧ y ∈ A ∧ G.Adj x y then w x * w y else 0) := by
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> by_cases hxy : G.Adj x y <;>
      simp [eraseWeights, hx, hy, hxy]
  simp_rw [hpoint, Finset.sum_add_distrib, Finset.sum_sub_distrib]

/-- The exact change of unordered edge mass under deletion of a vertex set. -/
theorem edgeMass_eraseWeights (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) :
    edgeMass G (eraseWeights w A) = edgeMass G w -
      (∑ v ∈ A, w v * neighborhoodMass G w v) + crossMass G w A A / 2 := by
  have h := crossMass_eraseWeights_univ G w A
  rw [crossMass_univ_univ, crossMass_univ_univ, crossMass_comm G w Finset.univ A,
    crossMass_univ_right] at h
  linarith

/-- Zeroing coordinates removes exactly their scalar-potential contributions. -/
theorem sum_scalarPotential_eraseWeights (u w : V → ℝ) (A : Finset V) :
    (∑ v, scalarPotential (u v) (eraseWeights w A v)) =
      (∑ v, scalarPotential (u v) (w v)) - ∑ v ∈ A, scalarPotential (u v) (w v) := by
  classical
  have hpoint (v : V) : scalarPotential (u v) (eraseWeights w A v) =
      scalarPotential (u v) (w v) - if v ∈ A then scalarPotential (u v) (w v) else 0 := by
    by_cases hv : v ∈ A <;> simp [eraseWeights, hv]
  simp_rw [hpoint, Finset.sum_sub_distrib]
  simp

/-- Exact potential deletion cost in terms of scalar vertex contributions and incident edges. -/
theorem graphPotential_deletion_cost (G : SimpleGraph V) (u w : V → ℝ) (A : Finset V) :
    graphPotential G u w - graphPotential G u (eraseWeights w A) =
      (∑ v ∈ A, (scalarPotential (u v) (w v) - 2 * w v * neighborhoodMass G w v)) +
      crossMass G w A A := by
  rw [graphPotential, graphPotential, sum_scalarPotential_eraseWeights, edgeMass_eraseWeights]
  simp only [Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

/-- Exact potential deletion cost expressed using the scalar remainder and coordinate residual. -/
theorem graphPotential_deletion_cost_residual (G : SimpleGraph V) (u w : V → ℝ)
    (A : Finset V) :
    graphPotential G u w - graphPotential G u (eraseWeights w A) =
      (∑ v ∈ A, (scalarXi (u v) (w v) + w v * residual G u w v)) +
      crossMass G w A A := by
  rw [graphPotential_deletion_cost]
  congr 1
  apply Finset.sum_congr rfl
  intro v _
  unfold scalarXi residual
  ring

/-- Averaging deletion costs over positive or signed center weights leaves explicit
scalar-remainder, residual, endpoint, and triangle contributions. -/
theorem averaged_deletion_cost (G : SimpleGraph V) (u w : V → ℝ) :
    (∑ x, w x * (graphPotential G u w -
      graphPotential G u (eraseWeights w (closedNeighborhood G x)))) =
      (∑ v, (w v + neighborhoodMass G w v) *
        (scalarXi (u v) (w v) + w v * residual G u w v)) +
      2 * (∑ v, w v ^ 2 * neighborhoodMass G w v) + 6 * triangleMass G w := by
  have hpoint (x : V) : w x * (graphPotential G u w -
      graphPotential G u (eraseWeights w (closedNeighborhood G x))) =
      w x * weightSum (fun v ↦ scalarXi (u v) (w v) + w v * residual G u w v)
        (closedNeighborhood G x) +
      w x * crossMass G w (closedNeighborhood G x) (closedNeighborhood G x) := by
    rw [graphPotential_deletion_cost_residual, weightSum, mul_add]
  simp_rw [hpoint, Finset.sum_add_distrib]
  rw [sum_weight_closedNeighborhood]
  rw [sum_weight_closedNeighborhood_crossMass]
  ring

/-- Averaged deletion reward before the scalar differential identity is applied. -/
theorem averaged_deletion_reward_expanded (G : SimpleGraph V) (u w : V → ℝ) (c : ℝ) :
    (∑ x, w x * deletionReward G u w c x) = objectiveMass u w - c *
      ((∑ v, (w v + neighborhoodMass G w v) *
        (scalarXi (u v) (w v) + w v * residual G u w v)) +
      2 * (∑ v, w v ^ 2 * neighborhoodMass G w v) + 6 * triangleMass G w) := by
  have hpoint (x : V) : w x * deletionReward G u w c x = u x * w x -
      c * (w x * (graphPotential G u w -
        graphPotential G u (eraseWeights w (closedNeighborhood G x)))) := by
    unfold deletionReward
    ring
  simp_rw [hpoint, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [averaged_deletion_cost]
  rfl

end

end Cliquefree
