module

public import Cliquefree.TriangleCenters
public import Cliquefree.TriangleCoupling

/-!
# Joint local labels and random graph splitting

A product of the local grand couplings defines all incidence labels at once. Their exact
marginals and disagreement bounds give the weighted triangle-retention estimate.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- One neighbor label for every incidence at a positive triangle center. -/
abbrev TriangleLabeling (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ) :=
  ∀ x : triangleCenters G w, G.neighborFinset x.val → G.neighborFinset x.val

/-- Extend local neighbor labels to all incidences, using a fixed value off positive centers. -/
def centerIncidenceLabel (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ)
    (fallback : V) (f : TriangleLabeling G w) (x v : V) : V := by
  classical
  exact if hx : x ∈ triangleCenters G w then
    if hv : G.Adj x v then (f ⟨x, hx⟩ ⟨v, (G.mem_neighborFinset x v).mpr hv⟩).val
    else fallback
  else fallback

/-- Apply a local incidence test, discarding incidences outside the positive center set. -/
def centerIncidenceKeep (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ)
    (K : ∀ x : triangleCenters G w, G.neighborFinset x.val → G.neighborFinset x.val → Prop)
    (f : TriangleLabeling G w) (x v : V) : Prop := by
  classical
  exact if hx : x ∈ triangleCenters G w then
    if hv : G.Adj x v then K ⟨x, hx⟩ ⟨v, (G.mem_neighborFinset x v).mpr hv⟩
      (f ⟨x, hx⟩ ⟨v, (G.mem_neighborFinset x v).mpr hv⟩)
    else False
  else False

/-- On a genuine local incidence the extended label is the chosen neighbor label. -/
@[simp] theorem centerIncidenceLabel_coe (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (fallback : V) (f : TriangleLabeling G w)
    (x : triangleCenters G w) (v : G.neighborFinset x.val) :
    centerIncidenceLabel G w fallback f x v = (f x v).val := by
  simp only [centerIncidenceLabel, x.property, dite_true,
    (G.mem_neighborFinset x v).mp v.property]

/-- The global retention test agrees with the specified local test. -/
@[simp] theorem centerIncidenceKeep_coe (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ)
    (K : ∀ x : triangleCenters G w, G.neighborFinset x.val → G.neighborFinset x.val → Prop)
    (f : TriangleLabeling G w) (x : triangleCenters G w) (v : G.neighborFinset x.val) :
    centerIncidenceKeep G w K f x v ↔ K x v (f x v) := by
  simp only [centerIncidenceKeep, x.property, dite_true,
    (G.mem_neighborFinset x v).mp v.property]

open Classical in
/-- The local coupling bound applies unchanged to the extended vertex-valued labels. -/
theorem centerIncidenceLabel_disagreement (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (fallback : V)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (μ : FiniteLaw (TriangleLabeling G w))
    (hd : ∀ x v z, μ.expectation (fun f ↦ if f x v ≠ f x z then 1 else 0) ≤
      2 * (P x v).totalVariation (P x z))
    (x : triangleCenters G w) (v z : G.neighborFinset x.val) :
    μ.expectation (fun f ↦ if centerIncidenceLabel G w fallback f x v =
      centerIncidenceLabel G w fallback f x z then 0 else 1) ≤
        2 * (P x v).totalVariation (P x z) := by
  simpa only [centerIncidenceLabel_coe, Subtype.val_inj, ne_eq, ite_not] using hd x v z

open Classical in
/-- Exact label marginals identify rejection probability with the corresponding row average. -/
theorem centerIncidenceKeep_rejection (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (μ : FiniteLaw (TriangleLabeling G w))
    (hm : ∀ x v y, μ.expectation (fun f ↦ if f x v = y then 1 else 0) = (P x v).mass y)
    (K : ∀ x : triangleCenters G w, G.neighborFinset x.val → G.neighborFinset x.val → Prop)
    (x : triangleCenters G w) (v : G.neighborFinset x.val) :
    μ.expectation (fun f ↦ if centerIncidenceKeep G w K f x v then 0 else 1) =
      (P x v).expectation (fun y ↦ if K x v y then 0 else 1) := by
  simpa only [centerIncidenceKeep_coe] using
    μ.expectation_of_marginals (P x v) (fun f ↦ f x v) (hm x v)
      (fun y ↦ if K x v y then 0 else 1)

open Classical in
/-- A bound on the average nearby-row variation controls all weighted corner disagreements. -/
theorem centerIncidenceLabel_corner_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v) (fallback : V)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (μ : FiniteLaw (TriangleLabeling G w))
    (hd : ∀ x v z, μ.expectation (fun f ↦ if f x v ≠ f x z then 1 else 0) ≤
      2 * (P x v).totalVariation (P x z)) {δ : ℝ}
    (hnear : (triangleCenterLaw G w hw hT).expectation (fun x ↦
      (triangleStationaryLaw G w hw x
        (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (triangleWalk G w hw x (hC x) v).expectation
            (fun z ↦ (P x v).totalVariation (P x z)))) ≤ δ) :
    orderedTriangleSum G w (fun x v z ↦ μ.expectation (fun f ↦
      if centerIncidenceLabel G w fallback f x v = centerIncidenceLabel G w fallback f x z
      then 0 else 1)) ≤ 2 * δ * (6 * triangleMass G w) := by
  classical
  rw [orderedTriangleSum_eq_center_walk G w hw hT hC]
  have h := (triangleCenterLaw G w hw hT).expectation_mono_support (fun x _ ↦
    (triangleStationaryLaw G w hw x
      (mem_triangleCenters G w x |>.mp x.property)).expectation_mono_support (fun v _ ↦
        (triangleWalk G w hw x (hC x) v).expectation_mono_support (fun z _ ↦
          centerIncidenceLabel_disagreement G w fallback P μ hd x v z)))
  simp only [FiniteLaw.expectation_smul] at h
  have hmul := mul_le_mul_of_nonneg_left (h.trans (mul_le_mul_of_nonneg_left hnear
    (show (0 : ℝ) ≤ 2 by norm_num))) (show 0 ≤ 6 * triangleMass G w by positivity)
  nlinarith

open Classical in
/-- The total weighted incidence rejection is six T times the center-averaged row rejection. -/
theorem centerIncidenceKeep_aggregate (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (μ : FiniteLaw (TriangleLabeling G w))
    (hm : ∀ x v y, μ.expectation (fun f ↦ if f x v = y then 1 else 0) = (P x v).mass y)
    (K : ∀ x : triangleCenters G w, G.neighborFinset x.val → G.neighborFinset x.val → Prop) :
    orderedTriangleSum G w
      (fun x v _ ↦ μ.expectation (fun f ↦ if centerIncidenceKeep G w K f x v then 0 else 1)) =
      (6 * triangleMass G w) * (triangleCenterLaw G w hw hT).expectation (fun x ↦
        (triangleStationaryLaw G w hw x
          (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
            (P x v).expectation (fun y ↦ if K x v y then 0 else 1))) := by
  classical
  rw [orderedTriangleSum_eq_edgeExpectation G w hw hT
    (fun x v ↦ μ.expectation (fun f ↦ if centerIncidenceKeep G w K f x v then 0 else 1)),
    triangleEdgeLaw_expectation_eq_centers G w hw hT
      (fun x v ↦ μ.expectation (fun f ↦ if centerIncidenceKeep G w K f x v then 0 else 1))]
  congr 1
  apply congrArg
  funext x
  apply congrArg
  funext v
  exact centerIncidenceKeep_rejection G w P μ hm K x v

open Classical in
/-- Row variation and rejection bounds control expected triangle loss of the joint split. -/
theorem expected_triangleLabeling_loss_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v) (fallback : V)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (μ : FiniteLaw (TriangleLabeling G w))
    (hm : ∀ x v y, μ.expectation (fun f ↦ if f x v = y then 1 else 0) = (P x v).mass y)
    (hd : ∀ x v z, μ.expectation (fun f ↦ if f x v ≠ f x z then 1 else 0) ≤
      2 * (P x v).totalVariation (P x z))
    (K : ∀ x : triangleCenters G w, G.neighborFinset x.val → G.neighborFinset x.val → Prop)
    {δ ε : ℝ}
    (hnear : (triangleCenterLaw G w hw hT).expectation (fun x ↦
      (triangleStationaryLaw G w hw x
        (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (triangleWalk G w hw x (hC x) v).expectation
            (fun z ↦ (P x v).totalVariation (P x z)))) ≤ δ)
    (hreject : (triangleCenterLaw G w hw hT).expectation (fun x ↦
      (triangleStationaryLaw G w hw x
        (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (P x v).expectation (fun y ↦ if K x v y then 0 else 1))) ≤ ε) :
    μ.expectation (fun f ↦ triangleMass G w - triangleMass
      (splitGraph G (centerIncidenceLabel G w fallback f) (centerIncidenceKeep G w K f))
        (fun a ↦ w a.1)) ≤ (6 * δ + 6 * ε) * triangleMass G w := by
  classical
  have hcorner := centerIncidenceLabel_corner_bound G w hw hT hC fallback P μ hd hnear
  have hincidence := centerIncidenceKeep_aggregate G w hw hT P μ hm K
  have hweighted := mul_le_mul_of_nonneg_left hreject
    (show 0 ≤ 6 * triangleMass G w by positivity)
  have hloss := μ.expected_splitGraph_triangleMass_loss_le G
    (centerIncidenceLabel G w fallback) (centerIncidenceKeep G w K) hw
  rw [hincidence] at hloss
  nlinarith

open Classical in
/-- Local row estimates produce a simultaneous labeling retaining
the required triangle mass. -/
theorem exists_retaining_triangleLabeling (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v) (fallback : V)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (K : ∀ x : triangleCenters G w, G.neighborFinset x.val → G.neighborFinset x.val → Prop)
    {δ ε : ℝ}
    (hnear : (triangleCenterLaw G w hw hT).expectation (fun x ↦
      (triangleStationaryLaw G w hw x
        (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (triangleWalk G w hw x (hC x) v).expectation
            (fun z ↦ (P x v).totalVariation (P x z)))) ≤ δ)
    (hreject : (triangleCenterLaw G w hw hT).expectation (fun x ↦
      (triangleStationaryLaw G w hw x
        (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (P x v).expectation (fun y ↦ if K x v y then 0 else 1))) ≤ ε) :
    ∃ f : TriangleLabeling G w, triangleMass G w - triangleMass
      (splitGraph G (centerIncidenceLabel G w fallback f) (centerIncidenceKeep G w K f))
        (fun a ↦ w a.1) ≤ (6 * δ + 6 * ε) * triangleMass G w := by
  classical
  obtain ⟨μ, hm, hd⟩ := exists_family_grand_coupling P
  have hmean := expected_triangleLabeling_loss_le G w hw hT hC fallback P μ hm hd K hnear hreject
  obtain ⟨f, _, hf⟩ := μ.exists_le_expectation (fun f ↦ triangleMass G w - triangleMass
    (splitGraph G (centerIncidenceLabel G w fallback f) (centerIncidenceKeep G w K f))
      (fun a ↦ w a.1))
  exact ⟨f, hf.trans hmean⟩

end Cliquefree
