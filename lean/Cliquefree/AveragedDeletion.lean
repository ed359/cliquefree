module

public import Cliquefree.Deletion
public import Cliquefree.ScalarOptimizer

/-!
# The averaged deletion reward

The scalar differential identity simplifies the exact weighted deletion cost. No
stationarity assumption is needed, and the residual records the entire error term.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- At positive coordinates, the residual is twice the optimizer's degree discrepancy. -/
theorem residual_eq_optimizer (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) (v : V) :
    residual G u w v =
      2 * scalarOptimizer (u v) (w v) * w v - 2 * neighborhoodMass G w v := by
  rw [residual, (scalarPotential_hasDerivAt (hu v) (hw v)).deriv]

/-- The scalar ODE cancels the optimizer from each averaged vertex contribution. -/
theorem deletion_vertex_identity (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) (v : V) :
    (w v + neighborhoodMass G w v) *
        (scalarXi (u v) (w v) + w v * residual G u w v) +
      2 * w v ^ 2 * neighborhoodMass G w v =
        u v * w v + residual G u w v *
          (w v * neighborhoodMass G w v - scalarXi (u v) (w v) / 2) := by
  rw [residual_eq_optimizer G hu hw]
  have ho := scalarOptimizer_ode (hu v) (hw v)
  linear_combination w v * ho

/-- The averaged potential loss is the objective mass, triangle term, and residual error. -/
theorem averaged_deletion_cost_residual (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) :
    (∑ x, w x * (graphPotential G u w -
      graphPotential G u (eraseWeights w (closedNeighborhood G x)))) =
        objectiveMass u w + 6 * triangleMass G w +
          ∑ v, residual G u w v *
            (w v * neighborhoodMass G w v - scalarXi (u v) (w v) / 2) := by
  rw [averaged_deletion_cost]
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset V)) rfl
    (fun v _ ↦ deletion_vertex_identity G hu hw v)
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hs
  unfold objectiveMass
  linarith

/-- The averaged deletion reward identity, valid at every positive auxiliary weighting. -/
theorem averaged_deletion_reward (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) (c : ℝ) :
    (∑ x, w x * deletionReward G u w c x) =
      (1 - c) * objectiveMass u w - 6 * c * triangleMass G w -
        c * ∑ v, residual G u w v *
          (w v * neighborhoodMass G w v - scalarXi (u v) (w v) / 2) := by
  rw [averaged_deletion_reward_expanded, ← averaged_deletion_cost G u w,
    averaged_deletion_cost_residual G hu hw]
  ring

end Cliquefree
