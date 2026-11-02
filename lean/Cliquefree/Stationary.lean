module

public import Cliquefree.Maximizer
public import Cliquefree.AveragedDeletion

/-!
# Stationary weights and deletion pivots
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- The scales used by the triangle test at a stationary auxiliary vector. -/
def stationaryScale (K : ℝ) (u w : V → ℝ) (v : V) : ℝ :=
  K * scalarXi (u v) (w v) / w v

omit [Fintype V] in
/-- The stationary scales are positive when their data are positive. -/
theorem stationaryScale_pos {K : ℝ} (hK : 0 < K) {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) (v : V) :
    0 < stationaryScale K u w v :=
  div_pos (mul_pos hK (scalarXi_pos (hu v) (hw v))) (hw v)

omit [Fintype V] in
/-- Multiplying a stationary scale by its auxiliary weight cancels its denominator. -/
theorem stationaryScale_mul {K : ℝ} {u w : V → ℝ} (hw : ∀ v, 0 < w v) (v : V) :
    stationaryScale K u w v * w v = K * scalarXi (u v) (w v) := by
  exact div_mul_cancel₀ _ (hw v).ne'

/-- A vanishing residual identifies neighborhood mass with the scalar optimizer. -/
theorem neighborhoodMass_eq_optimizer_of_stationary (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v)
    (hz : ∀ v, residual G u w v = 0) (v : V) :
    neighborhoodMass G w v = scalarOptimizer (u v) (w v) * w v := by
  have hv := hz v
  rw [residual_eq_optimizer G hu hw] at hv
  linarith

/-- Stationarity bounds the scaled degree budget by the mixed objective mass. -/
theorem stationary_degree_budget_le (G : SimpleGraph V) {K : ℝ} (hK : 0 ≤ K)
    {u w : V → ℝ} (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v)
    (hz : ∀ v, residual G u w v = 0) :
    scaledDegreeBudget G (stationaryScale K u w) w ≤ K * objectiveMass u w := by
  unfold scaledDegreeBudget objectiveMass
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro v _
  rw [stationaryScale_mul hw, neighborhoodMass_eq_optimizer_of_stationary G hu hw hz]
  have h := mul_le_mul_of_nonneg_left (scalarOptimizer_mul_scalarXi_le (hu v) (hw v))
    (mul_nonneg hK (hw v).le)
  nlinarith only [h]

/-- The objective mass is positive on a nonempty graph with positive data. -/
theorem objectiveMass_pos [Nonempty V] {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) : 0 < objectiveMass u w := by
  unfold objectiveMass
  exact Finset.sum_pos (fun v _ ↦ mul_pos (hu v) (hw v)) Finset.univ_nonempty

/-- At stationarity the residual error in the averaged deletion reward vanishes. -/
theorem averaged_deletion_reward_stationary (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) (c : ℝ)
    (hz : ∀ v, residual G u w v = 0) :
    (∑ x, w x * deletionReward G u w c x) =
      (1 - c) * objectiveMass u w - 6 * c * triangleMass G w := by
  rw [averaged_deletion_reward G hu hw]
  simp [hz]

/-- A nonnegative weighted average with positive weights has a nonnegative summand. -/
theorem exists_nonnegative_of_weighted_sum [Nonempty V] {w a : V → ℝ}
    (hw : ∀ v, 0 < w v) (hs : 0 ≤ ∑ v, w v * a v) : ∃ v, 0 ≤ a v := by
  by_contra! h
  have hn := Finset.sum_neg (fun v (_ : v ∈ (Finset.univ : Finset V)) ↦
    mul_neg_of_pos_of_neg (hw v) (h v)) Finset.univ_nonempty
  linarith


end Cliquefree
