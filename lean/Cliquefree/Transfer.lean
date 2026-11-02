module

public import Cliquefree.Lift

/-!
# Transferring an attained benchmark maximum

A positive benchmark maximizer lifts to a positive-domain potential maximizer.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Lifting a positive benchmark maximizer gives equality with its potential value. -/
theorem lifted_maximizer_value (G : SimpleGraph V) {u s : V → ℝ}
    (hu : ∀ v, 0 < u v) (hs : ∀ v, 0 < s v) (hG : ∀ v, ∃ y, G.Adj v y)
    (hmax : ∀ t : V → ℝ, (∀ v, 0 < t v) → benchmark G u t ≤ benchmark G u s) :
    graphPotential G u (liftedWeights G u s) = benchmark G u s := by
  apply le_antisymm
  · exact (graphPotential_le_benchmark G (fun v ↦ (hu v).le)
      (liftedWeights_pos G hu hs hG)).trans
      (hmax _ (liftedWeights_pos G hu hs hG))
  · exact benchmark_le_lifted_potential G hu hs hG

/-- The lifted maximizer dominates every positive potential competitor. -/
theorem lift_maximizes_positivePotential (G : SimpleGraph V) {u s : V → ℝ}
    (hu : ∀ v, 0 < u v) (hs : ∀ v, 0 < s v) (hG : ∀ v, ∃ y, G.Adj v y)
    (hmax : ∀ t : V → ℝ, (∀ v, 0 < t v) → benchmark G u t ≤ benchmark G u s) :
    ∀ w : V → ℝ, (∀ v, 0 < w v) →
      graphPotential G u w ≤ graphPotential G u (liftedWeights G u s) := by
  intro w hw
  rw [lifted_maximizer_value G hu hs hG hmax]
  exact (graphPotential_le_benchmark G (fun v ↦ (hu v).le) hw).trans (hmax w hw)

end Cliquefree
