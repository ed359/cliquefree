module

public import Cliquefree.TriangleLocalEntropy
public import Cliquefree.TriangleRejection

/-!
# Incidence rejection for neighborhood walks

Prepared common-neighbor masses and the entropy estimate imply the explicit rejection
probability used in the split's weighted triangle-retention bound.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- With positive weights and prepared denominators, every stationary neighbor has positive mass. -/
theorem triangleStationaryLaw_mass_pos (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 < w v) (x : V) (hT : 0 < localTriangleMass G w x)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (v : G.neighborFinset x) :
    0 < (triangleStationaryLaw G w (fun v ↦ (hw v).le) x hT).mass v :=
  div_pos (mul_pos (hw v) (hC v ((G.mem_neighborFinset x v).mp v.property))) hT

open Classical in
/-- The reversed local-walk test satisfies the explicit incidence rejection bound. -/
theorem triangleSmoothedLaw_rejection_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} {t : ℕ} (ht : 32 ≤ t) (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v)
    (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (hcommon : ∀ x y, G.Adj x y → max (θ x) (θ y) / (t : ℝ) ≤
      commonNeighborhoodMass G w x y) (j : ℕ)
    (hH : triangleMeanEntropy G w θ (fun v ↦ (hw v).le) hT hC j ≤
      (witnessA : ℝ) * Real.log (t : ℝ)) :
    (triangleCenterLaw G w (fun v ↦ (hw v).le) hT).expectation (fun x ↦
      (triangleStationaryLaw G w (fun v ↦ (hw v).le) x
        (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (triangleSmoothedLaw G w (fun v ↦ (hw v).le) x (hC x) j v).expectation (fun y ↦
            if (triangleSmoothedLaw G w (fun v ↦ (hw v).le) x (hC x) j y).mass v <
              (w v / θ x) / (2 : ℝ) ^ nextTriangleScale t then 1 else 0))) ≤
      2 * ((witnessA : ℝ) + 1) * Real.log (t : ℝ) / Real.sqrt (t : ℝ) := by
  classical
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hS : (0 : ℝ) < 2 ^ nextTriangleScale t := by positivity
  have hden : 0 < Real.log ((2 : ℝ) ^ nextTriangleScale t) + Real.log (t : ℝ) :=
    lt_of_lt_of_le (div_pos (Real.sqrt_pos.mpr ht') (by norm_num))
      (triangle_rejection_denominator_lower ht)
  have h := family_rejection_bound (triangleCenterLaw G w (fun v ↦ (hw v).le) hT)
    (fun x ↦ triangleStationaryLaw G w (fun v ↦ (hw v).le) x
      (mem_triangleCenters G w x |>.mp x.property))
    (fun x ↦ triangleSmoothedLaw G w (fun v ↦ (hw v).le) x (hC x) j)
    (fun x v ↦ triangleStationaryLaw_mass_pos G w hw x
      (mem_triangleCenters G w x |>.mp x.property) (hC x) v)
    (fun x v y ↦ triangleSmoothedLaw_detailedBalance G w (fun v ↦ (hw v).le) x
      (mem_triangleCenters G w x |>.mp x.property) (hC x) j v y)
    (r := fun x y ↦ w y / θ x) (fun x y ↦ div_pos (hw y) (hθ x)) ht' hS hden
    (fun x v y ↦ triangleSmoothedLaw_density_le G w (fun v ↦ (hw v).le) x (hC x)
      (hθ x) ht' (fun v hv ↦
        (div_le_div_of_nonneg_right (le_max_left _ _) ht'.le).trans (hcommon x v hv)) j v y)
  rw [← triangleMeanEntropy_eq_expectation G w θ (fun v ↦ (hw v).le) hT hC j] at h
  exact h.trans (triangle_rejection_ratio_le ht hH)

end Cliquefree
