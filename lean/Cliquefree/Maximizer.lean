module

public import Cliquefree.Transfer
public import Cliquefree.ScalarOptimizer
public import Cliquefree.DeletionIdentities

/-!
# Continuity and stationarity of potential maximizers
-/

@[expose] public section

noncomputable section

open Filter
open scoped BigOperators Topology

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Neighborhood mass is continuous in all the vertex weights. -/
theorem neighborhoodMass_continuous (G : SimpleGraph V) (v : V) :
    Continuous (fun w : V → ℝ ↦ neighborhoodMass G w v) := by
  classical
  unfold neighborhoodMass
  apply continuous_finsetSum
  intro y _
  by_cases h : G.Adj v y
  · simp only [ite_eq_left h]
    exact continuous_apply y
  · simp only [ite_eq_right h]
    exact continuous_const

/-- Weighted edge mass is a continuous quadratic function. -/
theorem edgeMass_continuous (G : SimpleGraph V) : Continuous (edgeMass G) := by
  unfold edgeMass
  apply Continuous.div_const
  exact continuous_finsetSum _ (fun v _ ↦
    (continuous_apply v).mul (neighborhoodMass_continuous G v))

/-- The graph potential is continuous, including at zero auxiliary coordinates. -/
theorem graphPotential_continuous (G : SimpleGraph V) {u : V → ℝ} (hu : ∀ v, 0 < u v) :
    Continuous (graphPotential G u) := by
  unfold graphPotential
  exact (continuous_finsetSum _ (fun v _ ↦
    (scalarPotential_continuous (hu v)).comp (continuous_apply v))).sub
    (continuous_const.mul (edgeMass_continuous G))

/-- A positive-domain maximum dominates all nonnegative competitors by continuity. -/
theorem positive_maximizer_dominates_nonnegative (G : SimpleGraph V) {u q : V → ℝ}
    (hu : ∀ v, 0 < u v)
    (hmax : ∀ w : V → ℝ, (∀ v, 0 < w v) → graphPotential G u w ≤ graphPotential G u q) :
    ∀ w : V → ℝ, (∀ v, 0 ≤ w v) → graphPotential G u w ≤ graphPotential G u q := by
  intro w hw
  have hc : Continuous (fun ε : ℝ ↦ graphPotential G u (fun v ↦ w v + ε)) :=
    (graphPotential_continuous G hu).comp
      (continuous_pi (fun _ ↦ continuous_const.add continuous_id))
  have ht : Tendsto (fun ε : ℝ ↦ graphPotential G u (fun v ↦ w v + ε))
      (𝓝[>] 0) (𝓝 (graphPotential G u w)) := by
    simpa using (hc.continuousAt (x := 0)).tendsto.mono_left nhdsWithin_le_nhds
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact hmax _ (fun v ↦ add_pos_of_nonneg_of_pos (hw v) hε)

/-- Lifting a benchmark maximizer yields a global nonnegative-domain potential maximizer. -/
theorem lift_maximizes_nonnegativePotential (G : SimpleGraph V) {u s : V → ℝ}
    (hu : ∀ v, 0 < u v) (hs : ∀ v, 0 < s v) (hG : ∀ v, ∃ y, G.Adj v y)
    (hmax : ∀ t : V → ℝ, (∀ v, 0 < t v) → benchmark G u t ≤ benchmark G u s) :
    ∀ w : V → ℝ, (∀ v, 0 ≤ w v) →
      graphPotential G u w ≤ graphPotential G u (liftedWeights G u s) :=
  positive_maximizer_dominates_nonnegative G hu
    (lift_maximizes_positivePotential G hu hs hG hmax)

/-- Changing one coordinate separates its scalar term and its incident edge contribution. -/
theorem graphPotential_update (G : SimpleGraph V) [DecidableEq V] (u w : V → ℝ)
    (x : V) (t : ℝ) :
    graphPotential G u (Function.update w x t) = graphPotential G u w +
      scalarPotential (u x) t - scalarPotential (u x) (w x) -
        2 * (t - w x) * neighborhoodMass G w x := by
  classical
  have hp (v : V) :
      scalarPotential (u v) (Function.update w x t v) = scalarPotential (u v) (w v) +
        if v = x then scalarPotential (u x) t - scalarPotential (u x) (w x) else 0 := by
    by_cases hv : v = x
    · subst v
      simp
    · simp [hv]
  simp only [graphPotential, hp, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, edgeMass_update]
  ring

/-- The partial derivative of graph potential is exactly its coordinate residual. -/
theorem graphPotential_hasDerivAt_update (G : SimpleGraph V) [DecidableEq V]
    {u w : V → ℝ} (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) (x : V) :
    HasDerivAt (fun t : ℝ ↦ graphPotential G u (Function.update w x t))
      (residual G u w x) (w x) := by
  have hfun : (fun t : ℝ ↦ graphPotential G u (Function.update w x t)) =
      (fun t : ℝ ↦ graphPotential G u w + scalarPotential (u x) t -
        scalarPotential (u x) (w x) - 2 * neighborhoodMass G w x * (t - w x)) := by
    funext t
    rw [graphPotential_update]
    ring
  rw [hfun, residual, (scalarPotential_hasDerivAt (hu x) (hw x)).deriv]
  have hs := ((hasDerivAt_const (𝕜 := ℝ) (w x) (graphPotential G u w)).add
    (scalarPotential_hasDerivAt (hu x) (hw x))).sub_const
      (scalarPotential (u x) (w x))
  have he := ((hasDerivAt_id (𝕜 := ℝ) (w x)).sub_const (w x)).const_mul
    (2 * neighborhoodMass G w x)
  convert hs.sub he using 1 <;> first | rfl | simp

/-- Every positive global maximizer satisfies all stationarity equations. -/
theorem positive_maximizer_stationary (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v)
    (hmax : ∀ q : V → ℝ, (∀ v, 0 < q v) → graphPotential G u q ≤ graphPotential G u w) :
    ∀ v, residual G u w v = 0 := by
  classical
  intro x
  have hm : IsLocalMax (fun t : ℝ ↦ graphPotential G u (Function.update w x t)) (w x) := by
    change ∀ᶠ t in 𝓝 (w x), graphPotential G u (Function.update w x t) ≤
      graphPotential G u (Function.update w x (w x))
    filter_upwards [eventually_gt_nhds (hw x)] with t ht
    simp only [Function.update_eq_self]
    apply hmax
    intro v
    by_cases hv : v = x
    · subst v
      simpa using ht
    · simpa [Function.update_of_ne hv] using hw v
  exact hm.hasDerivAt_eq_zero (graphPotential_hasDerivAt_update G hu hw x)

end Cliquefree
