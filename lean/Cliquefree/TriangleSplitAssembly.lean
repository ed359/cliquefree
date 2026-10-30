module

public import Cliquefree.TriangleSplitLoad

/-!
# A bounded-load split retaining weighted triangles

The grand coupling, the reversed-row incidence test, and averaging together produce a
finite split with controlled load, budget, and triangle loss.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

open Classical in
/-- Nearby reversible rows give a bounded-load split without increasing the degree budget. -/
theorem exists_bounded_retaining_split (G : SimpleGraph V) [DecidableRel G.Adj]
    (w θ : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hθ : ∀ v, 0 < θ v)
    (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v) (fallback : V)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    {S δ ε : ℝ} (hS : 0 < S)
    (hnear : (triangleCenterLaw G w hw hT).expectation (fun x ↦
      (triangleStationaryLaw G w hw x
        (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (triangleWalk G w hw x (hC x) v).expectation
            (fun z ↦ (P x v).totalVariation (P x z)))) ≤ δ)
    (hreject : (triangleCenterLaw G w hw hT).expectation (fun x ↦
      (triangleStationaryLaw G w hw x
        (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (P x v).expectation (fun y ↦ if (P x y).mass v < (w v / θ x) / S then 1 else 0))) ≤ ε) :
    ∃ f : TriangleLabeling G w,
      let H := splitGraph G (centerIncidenceLabel G w fallback f)
        (centerIncidenceKeep G w (fun x v y ↦ (w v / θ x) / S ≤ (P x y).mass v) f)
      (∀ a : V × V, neighborhoodMass H (fun a ↦ w a.1) a ≤ S * θ a.1) ∧
        scaledDegreeBudget H (fun a ↦ θ a.1) (fun a ↦ w a.1) ≤ scaledDegreeBudget G θ w ∧
        (1 - 6 * δ - 6 * ε) * triangleMass G w ≤ triangleMass H (fun a ↦ w a.1) := by
  classical
  have hr : (triangleCenterLaw G w hw hT).expectation (fun x ↦
      (triangleStationaryLaw G w hw x
        (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (P x v).expectation (fun y ↦
            if (w v / θ x) / S ≤ (P x y).mass v then 0 else 1))) ≤ ε := by
    simpa only [← not_lt, ite_not] using hreject
  obtain ⟨f, hf⟩ := exists_retaining_triangleLabeling G w hw hT hC fallback P
    (fun x v y ↦ (w v / θ x) / S ≤ (P x y).mass v) hnear hr
  refine ⟨f, ?_, ?_, ?_⟩
  · intro a
    exact centerIncidenceSplit_normalized_load_le G w θ hθ hS fallback P f a.1 a.2
  · exact splitGraph_budget_le G _ _ (fun v ↦ (hθ v).le) hw
  · nlinarith

end Cliquefree
