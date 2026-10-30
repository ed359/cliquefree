module

public import Cliquefree.TriangleBasics
public import Cliquefree.FiniteLaw

/-!
# Local walks in weighted neighborhoods

The local walk and its reversible finite law use common-neighbor denominators.
The directed-edge law factors through a center and its conditional neighbor law.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Twice the weighted edge mass inside one open neighborhood. -/
def localTriangleMass (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ) (x : V) : ℝ :=
  ∑ v : G.neighborFinset x, w v * commonNeighborhoodMass G w x v

/-- Center-weighted local triangle masses count every triangle six times. -/
theorem sum_weight_localTriangleMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) : (∑ x, w x * localTriangleMass G w x) = 6 * triangleMass G w := by
  have hlocal (x : V) : localTriangleMass G w x =
      ∑ v, if G.Adj x v then w v * commonNeighborhoodMass G w x v else 0 := by
    unfold localTriangleMass
    rw [Finset.sum_coe_sort (G.neighborFinset x)
      (fun v ↦ w v * commonNeighborhoodMass G w x v)]
    rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  simp only [hlocal, Finset.mul_sum, mul_ite, mul_zero]
  simpa only [mul_assoc] using sum_edge_commonNeighborhoodMass G w

/-- One weighted step inside an open neighborhood, with common-neighbor normalization. -/
def triangleWalk (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (x : V)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (v : G.neighborFinset x) : FiniteLaw (G.neighborFinset x) where
  mass z := (if G.Adj v z then w z else 0) / commonNeighborhoodMass G w x v
  nonneg z := div_nonneg (by split_ifs <;> first | exact hw z | exact le_rfl)
    (hC v (G.mem_neighborFinset x v |>.mp v.property)).le
  sum_mass := by
    rw [← Finset.sum_div, ← commonNeighborhoodMass_eq_sum_neighbor G w x v]
    exact div_self (hC v (G.mem_neighborFinset x v |>.mp v.property)).ne'

/-- The reversible local law weights a neighbor by its incident triangle mass. -/
def triangleStationaryLaw (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (x : V) (hT : 0 < localTriangleMass G w x) :
    FiniteLaw (G.neighborFinset x) where
  mass v := w v * commonNeighborhoodMass G w x v / localTriangleMass G w x
  nonneg v := div_nonneg (mul_nonneg (hw v) (commonNeighborhoodMass_nonneg G hw x v)) hT.le
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self hT.ne'

/-- Detailed balance holds because both oriented local-edge masses are the same product. -/
theorem triangleWalk_detailedBalance (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (x : V)
    (hT : 0 < localTriangleMass G w x)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (v z : G.neighborFinset x) :
    (triangleStationaryLaw G w hw x hT).mass v * (triangleWalk G w hw x hC v).mass z =
      (triangleStationaryLaw G w hw x hT).mass z *
        (triangleWalk G w hw x hC z).mass v := by
  have hv := (hC v (G.mem_neighborFinset x v |>.mp v.property)).ne'
  have hz := (hC z (G.mem_neighborFinset x z |>.mp z.property)).ne'
  by_cases hvz : G.Adj v z
  · have hzv : G.Adj z v := hvz.symm
    simp only [triangleStationaryLaw, triangleWalk, hvz, hzv, ite_true]
    field_simp
  · have hzv : ¬G.Adj z v := fun h ↦ hvz h.symm
    simp [triangleStationaryLaw, triangleWalk, hvz, hzv]

/-- Summing detailed balance proves stationarity of the local triangle law. -/
theorem triangleWalk_stationary (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (x : V)
    (hT : 0 < localTriangleMass G w x)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (z : G.neighborFinset x) :
    (∑ v, (triangleStationaryLaw G w hw x hT).mass v *
      (triangleWalk G w hw x hC v).mass z) = (triangleStationaryLaw G w hw x hT).mass z := by
  simp_rw [triangleWalk_detailedBalance G w hw x hT hC]
  rw [← Finset.mul_sum, (triangleWalk G w hw x hC z).sum_mass, mul_one]

/-- The preparation lower bound gives a uniform density bound for one local step. -/
theorem triangleWalk_density_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (x : V)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t)
    (hCt : ∀ v, G.Adj x v → θ / t ≤ commonNeighborhoodMass G w x v)
    (v z : G.neighborFinset x) : (triangleWalk G w hw x hC v).mass z ≤ t * w z / θ := by
  have hv := G.mem_neighborFinset x v |>.mp v.property
  change (if G.Adj v z then w z else 0) / commonNeighborhoodMass G w x v ≤ _
  by_cases hvz : G.Adj v z
  · rw [ite_eq_left hvz]
    apply (div_le_div_iff₀ (hC v hv) hθ).mpr
    have hden := (div_le_iff₀ ht).mp (hCt v hv)
    nlinarith [mul_le_mul_of_nonneg_left hden (hw z)]
  · rw [ite_eq_right hvz, zero_div]
    exact div_nonneg (mul_nonneg ht.le (hw z)) hθ.le

/-- The distribution of a directed edge of a weight-biased ordered triangle. -/
def triangleEdgeLaw (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w) : FiniteLaw (V × V) where
  mass e := (if G.Adj e.1 e.2 then
    w e.1 * w e.2 * commonNeighborhoodMass G w e.1 e.2 else 0) / (6 * triangleMass G w)
  nonneg e := div_nonneg (by
    split_ifs
    · exact mul_nonneg (mul_nonneg (hw e.1) (hw e.2))
        (commonNeighborhoodMass_nonneg G hw e.1 e.2)
    · exact le_rfl) (by positivity)
  sum_mass := by
    rw [← Finset.sum_div, Fintype.sum_prod_type, sum_edge_commonNeighborhoodMass G w]
    exact div_self (by positivity)

/-- The directed-edge law factors into the center mass and its stationary conditional law. -/
theorem triangleEdgeLaw_conditional (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w) (x : V)
    (hx : 0 < localTriangleMass G w x) (v : G.neighborFinset x) :
    (triangleEdgeLaw G w hw hT).mass (x, v) =
      (w x * localTriangleMass G w x / (6 * triangleMass G w)) *
        (triangleStationaryLaw G w hw x hx).mass v := by
  have hv := G.mem_neighborFinset x v |>.mp v.property
  simp only [triangleEdgeLaw, triangleStationaryLaw, hv, ite_true]
  field_simp

end Cliquefree
