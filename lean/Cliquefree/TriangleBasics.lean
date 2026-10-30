module

public import Cliquefree.DeletionIdentities
public import Cliquefree.Constants

/-!
# Graph estimates for the triangle dichotomy

The witness data and finite weighted estimates used by pruning, local walks, and the final
normalized-load contradiction in the triangle dichotomy.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- The exact strong witness required in the triangle dichotomy. Its scale is inherited
from a vertex, and negative dyadic exponents are expressed as reciprocals. -/
structure TriangleWitness (G : SimpleGraph V) (θ w : V → ℝ) where
  /-- The first witness vertex set. -/
  A : Finset V
  /-- The second witness vertex set, which may overlap the first. -/
  B : Finset V
  /-- The positive integer dyadic scale exponent. -/
  p : ℕ
  p_pos : 1 ≤ p
  /-- A vertex whose scale supplies the witness parameter. -/
  scaleVertex : V
  weight_A : weightSum w A ≤ θ scaleVertex * 2 ^ p
  weight_B : weightSum w B ≤ θ scaleVertex * 2 ^ p
  scaled_B : scaledMass θ w B ≤ θ scaleVertex ^ 2 * 2 ^ (2 * p)
  cross_large :
    24 * ((p : ℝ) * scaledMass θ w A + θ scaleVertex ^ 2 / 2 ^ p) < crossMass G w A B

/-- Common-neighbor mass is symmetric in its two endpoints. -/
theorem commonNeighborhoodMass_comm (G : SimpleGraph V) (w : V → ℝ) (x y : V) :
    commonNeighborhoodMass G w x y = commonNeighborhoodMass G w y x := by
  classical
  unfold commonNeighborhoodMass
  apply Finset.sum_congr rfl
  intro z _
  by_cases hx : G.Adj x z <;> by_cases hy : G.Adj y z <;> simp [hx, hy]

/-- Common-neighbor mass is nonnegative for nonnegative vertex weights. -/
theorem commonNeighborhoodMass_nonneg (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (x y : V) : 0 ≤ commonNeighborhoodMass G w x y := by
  classical
  unfold commonNeighborhoodMass
  apply Finset.sum_nonneg
  intro z _
  split_ifs
  · exact hw z
  · exact le_rfl

/-- Common neighbors form a subset of the neighborhood of either endpoint. -/
theorem commonNeighborhoodMass_le_left (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (x y : V) :
    commonNeighborhoodMass G w x y ≤ neighborhoodMass G w x := by
  classical
  unfold commonNeighborhoodMass neighborhoodMass
  apply Finset.sum_le_sum
  intro z _
  by_cases hx : G.Adj x z <;> by_cases hy : G.Adj y z <;> simp [hx, hy, hw z]

/-- The common-neighbor bound at the second endpoint follows by symmetry. -/
theorem commonNeighborhoodMass_le_right (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (x y : V) :
    commonNeighborhoodMass G w x y ≤ neighborhoodMass G w y := by
  rw [commonNeighborhoodMass_comm]
  exact commonNeighborhoodMass_le_left G hw y x

/-- Nonnegative scales and weights give a nonnegative triangle budget. -/
theorem scaledDegreeBudget_nonneg (G : SimpleGraph V) {θ w : V → ℝ}
    (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v) : 0 ≤ scaledDegreeBudget G θ w :=
  Finset.sum_nonneg (fun v _ ↦ mul_nonneg (mul_nonneg (hθ v) (hw v))
    (neighborhoodMass_nonneg G hw v))

/-- Summing scaled neighbor masses with the center weights recovers the degree budget. -/
theorem sum_weight_scaledMass_neighborhood (G : SimpleGraph V) [DecidableRel G.Adj]
    (θ w : V → ℝ) :
    (∑ v, w v * scaledMass θ w (G.neighborFinset v)) = scaledDegreeBudget G θ w := by
  simp only [scaledMass, weightSum, ← neighborhoodMass_eq_sum_neighborFinset]
  rw [sum_mul_neighborhoodMass_comm]
  rfl

/-- A normalized-load bound controls triangle mass by one sixth of the degree budget. -/
theorem triangleMass_le_load_budget (G : SimpleGraph V) {θ w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {L : ℝ} (hL : ∀ v, neighborhoodMass G w v ≤ L * θ v) :
    triangleMass G w ≤ L * scaledDegreeBudget G θ w / 6 := by
  classical
  have he : 6 * triangleMass G w ≤ L * scaledDegreeBudget G θ w := by
    rw [← sum_edge_commonNeighborhoodMass]
    calc
      _ ≤ ∑ x, ∑ y, if G.Adj x y then w x * w y * (L * θ x) else 0 := by
        apply Finset.sum_le_sum
        intro x _
        apply Finset.sum_le_sum
        intro y _
        split_ifs
        · exact mul_le_mul_of_nonneg_left
            ((commonNeighborhoodMass_le_left G hw x y).trans (hL x))
            (mul_nonneg (hw x) (hw y))
        · exact le_rfl
      _ = L * scaledDegreeBudget G θ w := by
        simp only [scaledDegreeBudget, neighborhoodMass, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro y _
        split_ifs <;> ring
  linarith

/-- The retained-edge condition and load bound control the ratio of adjacent scales. -/
theorem prepared_adjacent_scale_ratio (G : SimpleGraph V) {θ w : V → ℝ}
    (hθ : ∀ v, 0 < θ v) (hw : ∀ v, 0 ≤ w v) {t L : ℝ} (ht : 0 < t)
    (hL : ∀ v, neighborhoodMass G w v ≤ L * θ v)
    (hC : ∀ x y, G.Adj x y → max (θ x) (θ y) / t ≤ commonNeighborhoodMass G w x y)
    {x y : V} (hxy : G.Adj x y) : θ x / θ y ≤ t * L := by
  have hmass := (hC x y hxy).trans ((commonNeighborhoodMass_le_right G hw x y).trans
    (hL y))
  apply (div_le_iff₀ (hθ y)).mpr
  have hmax := (div_le_iff₀ ht).mp hmass
  nlinarith [le_max_left (θ x) (θ y)]

/-- Common-neighbor mass is a neighbor sum inside the center's neighborhood. -/
theorem commonNeighborhoodMass_eq_sum_neighbor (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (x v : V) :
    commonNeighborhoodMass G w x v =
      ∑ z : G.neighborFinset x, if G.Adj v z then w z else 0 := by
  classical
  rw [Finset.sum_coe_sort (G.neighborFinset x) (fun z ↦ if G.Adj v z then w z else 0)]
  simp only [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter,
    commonNeighborhoodMass]
  apply Finset.sum_congr rfl
  intro z _
  by_cases hx : G.Adj x z <;> by_cases hv : G.Adj v z <;> simp [hx, hv]

end Cliquefree
