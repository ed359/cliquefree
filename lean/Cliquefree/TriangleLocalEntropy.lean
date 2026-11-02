module

public import Cliquefree.TriangleExceptional
public import Cliquefree.TriangleEntropyConcentration
public import Cliquefree.TriangleCenters
public import Cliquefree.TriangleLeakage

/-! # Entropy of local walks in the triangle reduction -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- The smoothed walk row on the neighborhood of one center. -/
def triangleSmoothedLaw (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (x : V)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (j : ℕ) (v : G.neighborFinset x) : FiniteLaw (G.neighborFinset x) := by
  classical
  exact smoothedLaw (lawKernel (triangleWalk G w hw x hC))
    (lawKernel_stochastic (triangleWalk G w hw x hC)) j v

/-- Every smoothed local row inherits the prepared density bound. -/
theorem triangleSmoothedLaw_density_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (x : V)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t)
    (hCt : ∀ v, G.Adj x v → θ / t ≤ commonNeighborhoodMass G w x v)
    (j : ℕ) (v z : G.neighborFinset x) :
    (triangleSmoothedLaw G w hw x hC j v).mass z ≤ t * (w z / θ) := by
  classical
  have h := smoothedKernel_density_le (lawKernel_stochastic (triangleWalk G w hw x hC))
    (fun v z ↦ triangleWalk_density_le G w hw x hC hθ ht hCt v z) j v z
  simpa only [triangleSmoothedLaw, smoothedLaw, FiniteLaw.ofStochasticRow, mul_div_assoc] using h

/-- Smoothed local rows preserve the same reversible stationary law. -/
theorem triangleSmoothedLaw_detailedBalance (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (x : V)
    (hT : 0 < localTriangleMass G w x)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (j : ℕ) (v z : G.neighborFinset x) :
    (triangleStationaryLaw G w hw x hT).mass v * (triangleSmoothedLaw G w hw x hC j v).mass z =
      (triangleStationaryLaw G w hw x hT).mass z *
        (triangleSmoothedLaw G w hw x hC j z).mass v := by
  classical
  have hr : KernelReversible (triangleStationaryLaw G w hw x hT).mass
      (lawKernel (triangleWalk G w hw x hC)) :=
    triangleWalk_detailedBalance G w hw x hT hC
  simpa only [triangleSmoothedLaw, smoothedLaw, FiniteLaw.ofStochasticRow] using
    hr.smoothedKernel j v z

/-- Choose a triangle-bearing center, then its stationary neighbor. -/
def triangleIncidenceLaw (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w) :
    FiniteLaw (Σ x : triangleCenters G w, G.neighborFinset x.val) :=
  (triangleCenterLaw G w hw hT).sigma (fun x ↦ triangleStationaryLaw G w hw x
    (mem_triangleCenters G w x |>.mp x.property))

/-- The dependent incidence law agrees with the directed-edge law on vertex observables. -/
theorem triangleIncidenceLaw_expectation (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w) (F : V → V → ℝ) :
    (triangleIncidenceLaw G w hw hT).expectation (fun e ↦ F e.1 e.2) =
      (triangleEdgeLaw G w hw hT).expectation (fun e ↦ F e.1 e.2) := by
  rw [triangleIncidenceLaw, FiniteLaw.expectation_sigma _ _
    (fun (x : triangleCenters G w) (v : G.neighborFinset x.val) ↦ F x v)]
  exact (triangleEdgeLaw_expectation_eq_centers G w hw hT F).symm

/-- Mean reference entropy of local smoothed rows over the triangle incidence law. -/
def triangleMeanEntropy (G : SimpleGraph V) [DecidableRel G.Adj]
    (w θ : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v) (j : ℕ) : ℝ :=
  (triangleIncidenceLaw G w hw hT).expectation (fun e ↦
    (triangleSmoothedLaw G w hw e.1 (hC e.1) j e.2).referenceEntropy
      (fun y ↦ w y / θ e.1))

open Classical in
/-- The graph's mean entropy is the stationary family entropy used in the walk estimates. -/
theorem triangleMeanEntropy_eq_family (G : SimpleGraph V) [DecidableRel G.Adj]
    (w θ : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v) (j : ℕ) :
    triangleMeanEntropy G w θ hw hT hC j =
      familyReferenceEntropy (triangleCenterLaw G w hw hT)
        (fun x ↦ triangleStationaryLaw G w hw x (mem_triangleCenters G w x |>.mp x.property))
        (fun x ↦ lawKernel (triangleWalk G w hw x (hC x)))
        (fun x ↦ lawKernel_stochastic (triangleWalk G w hw x (hC x)))
        (fun x y ↦ w y / θ x) j := by
  classical
  rw [triangleMeanEntropy, triangleIncidenceLaw, FiniteLaw.expectation_sigma _ _
    (fun (x : triangleCenters G w) (v : G.neighborFinset x.val) ↦
      (triangleSmoothedLaw G w hw x (hC x) j v).referenceEntropy (fun y ↦ w y / θ x))]
  rfl

/-- Preparation with positive scales gives every local-walk denominator strict positivity. -/
theorem prepared_common_pos (G : SimpleGraph V) {w θ : V → ℝ} {t : ℝ}
    (ht : 0 < t) (hθ : ∀ x, 0 < θ x)
    (hcommon : ∀ x y, G.Adj x y → max (θ x) (θ y) / t ≤
      commonNeighborhoodMass G w x y) (x y : V) (hxy : G.Adj x y) :
    0 < commonNeighborhoodMass G w x y :=
  (div_pos ((hθ x).trans_le (le_max_left _ _)) ht).trans_le (hcommon x y hxy)

/-- The mean reference entropy of every smoothed local walk is bounded below by its density. -/
theorem triangleMeanEntropy_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v)
    (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    {t : ℝ} (ht : 0 < t)
    (hcommon : ∀ x y, G.Adj x y → max (θ x) (θ y) / t ≤
      commonNeighborhoodMass G w x y) (j : ℕ) :
    -Real.log t ≤ triangleMeanEntropy G w θ (fun v ↦ (hw v).le) hT hC j := by
  apply FiniteLaw.expected_referenceEntropy_density_lower
  · intro e y
    exact div_pos (hw y) (hθ e.1)
  · exact ht
  · intro e y
    exact triangleSmoothedLaw_density_le G w (fun v ↦ (hw v).le) e.1 (hC e.1)
      (hθ e.1) ht (fun v hv ↦ (div_le_div_of_nonneg_right (le_max_left _ _) ht.le).trans
        (hcommon e.1 v hv)) j e.2 y

/-- The two successful cross tests give the terminal mean entropy bound for local walks. -/
theorem triangleMeanEntropy_upper (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} {t : ℕ} (ht : 32 ≤ t) (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v)
    (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (hbudget : scaledDegreeBudget G θ w ≤ triangleMass G w)
    (hload : ∀ x, neighborhoodMass G w x ≤ 2 ^ t * θ x)
    (hcommon : ∀ x y, G.Adj x y → max (θ x) (θ y) / (t : ℝ) ≤
      commonNeighborhoodMass G w x y)
    (hfirst : ∀ v, crossMass G w (G.neighborFinset v) (triangleClosure G w θ t v t) ≤
      (witnessC : ℝ) * (30 * (t : ℝ) ^ 3 * scaledMass θ w (G.neighborFinset v) +
        θ v ^ 2 / 2 ^ (30 * t ^ 3)))
    (hsecond : ∀ v,
      crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v) ≤
        (witnessC : ℝ) * (2 * (t : ℝ) * scaledMass θ w (triangleExceptional G w θ t v) +
          θ v ^ 2 / 2 ^ (2 * t))) :
    triangleMeanEntropy G w θ (fun v ↦ (hw v).le) hT hC t ≤
      (witnessA : ℝ) * Real.log t := by
  classical
  let ν := triangleIncidenceLaw G w (fun v ↦ (hw v).le) hT
  let bad := Finset.univ.filter (fun e : Σ x : triangleCenters G w, G.neighborFinset x.val ↦
    e.1.val ∈ triangleExceptional G w θ t e.2)
  let S := fun e : Σ x : triangleCenters G w, G.neighborFinset x.val ↦
    neighborSlice G e.1.val (triangleClosure G w θ t e.2 t)
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  apply ν.expected_referenceEntropy_walk
    (fun e ↦ triangleSmoothedLaw G w (fun v ↦ (hw v).le) e.1 (hC e.1) t e.2)
    (fun e y ↦ w y / θ e.1) (fun e y ↦ div_pos (hw y) (hθ e.1)) bad S (by omega)
  · intro e he
    have hn : e.1.val ∉ triangleExceptional G w θ t e.2 := by simpa [bad] using he
    have hmass := neighborhoodMassOn_le_of_not_exceptional G w θ t
      ((G.mem_neighborFinset e.1 e.2).mp e.2.property).symm hn
    calc
      _ = neighborhoodMassOn G w (triangleClosure G w θ t e.2 t) e.1 / θ e.1 := by
        dsimp only [S]
        rw [sum_neighborSlice G e.1.val _ (fun y ↦ w y / θ e.1)]
        simp only [neighborhoodMassOn, Finset.sum_div, ite_div, zero_div]
      _ ≤ _ := (div_le_iff₀ (hθ e.1)).mpr hmass
  · intro e
    rw [← Finset.sum_div, Finset.sum_coe_sort (G.neighborFinset e.1.val) w,
      ← neighborhoodMass_eq_sum_neighborFinset]
    exact (div_le_iff₀ (hθ e.1)).mpr (hload e.1)
  · intro e _
    have hh := triangleClosure_walk_leakage G w θ (fun v ↦ (hw v).le) hθ
      (by omega) hload hcommon e.1 (hC e.1) e.2 t
    have he : (t : ℝ) / (t : ℝ) ^ 4 = 1 / (t : ℝ) ^ 3 := by field_simp
    simpa only [triangleSmoothedLaw, FiniteLaw.outsideMass, he] using hh
  · have he : (∑ e ∈ bad, ν.mass e) = ν.expectation
        (fun e ↦ if e.1.val ∈ triangleExceptional G w θ t e.2 then 1 else 0) := by
      simp only [bad, Finset.sum_filter, FiniteLaw.expectation, mul_ite, mul_one, mul_zero]
    rw [he, triangleIncidenceLaw_expectation G w (fun v ↦ (hw v).le) hT
      (fun x v ↦ if x ∈ triangleExceptional G w θ t v then 1 else 0)]
    exact triangleExceptional_probability_le G ht (fun v ↦ (hw v).le) (fun v ↦ (hθ v).le)
      (by norm_num [witnessC]) hT hbudget hcommon hfirst hsecond

/-- Smoothing can only increase mean reference entropy. -/
theorem triangleMeanEntropy_mono (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v)
    (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    {i j : ℕ} (hij : i ≤ j) :
    triangleMeanEntropy G w θ (fun v ↦ (hw v).le) hT hC i ≤
      triangleMeanEntropy G w θ (fun v ↦ (hw v).le) hT hC j := by
  classical
  rw [triangleMeanEntropy_eq_family, triangleMeanEntropy_eq_family]
  apply FiniteLaw.expectation_mono_support
  intro x _
  apply averagedReferenceEntropy_monotone
  · exact triangleWalk_stationary G w (fun v ↦ (hw v).le) x
      (mem_triangleCenters G w x |>.mp x.property) (hC x)
  · exact fun y ↦ div_pos (hw y) (hθ x)
  · exact hij

/-- Mean total variation of two smoothed rows at the first two neighbors of an ordered triangle. -/
def triangleNearbyVariation (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v) (j : ℕ) : ℝ := by
  classical
  exact familyNearbyVariation (triangleCenterLaw G w hw hT)
    (fun x ↦ triangleStationaryLaw G w hw x (mem_triangleCenters G w x |>.mp x.property))
    (fun x ↦ lawKernel (triangleWalk G w hw x (hC x)))
    (fun x ↦ lawKernel_stochastic (triangleWalk G w hw x (hC x))) j

/-- Successful tests provide a common time with nearby local rows and bounded mean entropy. -/
theorem exists_triangleNearby_rows (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} {t : ℕ} (ht : 32 ≤ t) (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v)
    (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (hbudget : scaledDegreeBudget G θ w ≤ triangleMass G w)
    (hload : ∀ x, neighborhoodMass G w x ≤ 2 ^ t * θ x)
    (hcommon : ∀ x y, G.Adj x y → max (θ x) (θ y) / (t : ℝ) ≤
      commonNeighborhoodMass G w x y)
    (hfirst : ∀ v, crossMass G w (G.neighborFinset v) (triangleClosure G w θ t v t) ≤
      (witnessC : ℝ) * (30 * (t : ℝ) ^ 3 * scaledMass θ w (G.neighborFinset v) +
        θ v ^ 2 / 2 ^ (30 * t ^ 3)))
    (hsecond : ∀ v,
      crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v) ≤
        (witnessC : ℝ) * (2 * (t : ℝ) * scaledMass θ w (triangleExceptional G w θ t v) +
          θ v ^ 2 / 2 ^ (2 * t))) :
    ∃ j < t, triangleMeanEntropy G w θ (fun v ↦ (hw v).le) hT hC j ≤
        (witnessA : ℝ) * Real.log t ∧
      triangleNearbyVariation G w (fun v ↦ (hw v).le) hT hC j ≤
        2 * Real.sqrt (((witnessA : ℝ) + 1) * Real.log t / t) := by
  classical
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hu := triangleMeanEntropy_upper G ht hw hθ hT hC hbudget hload hcommon hfirst hsecond
  have hl := triangleMeanEntropy_lower G hw hθ hT hC ht' hcommon 0
  have hdiff : triangleMeanEntropy G w θ (fun v ↦ (hw v).le) hT hC t -
      triangleMeanEntropy G w θ (fun v ↦ (hw v).le) hT hC 0 ≤
      ((witnessA : ℝ) + 1) * Real.log t := by linarith
  rw [triangleMeanEntropy_eq_family, triangleMeanEntropy_eq_family] at hdiff
  obtain ⟨j, hj, hnear⟩ := exists_nearby_smoothed_rows _ _ _ _
    (fun (x : triangleCenters G w) ↦ triangleWalk_stationary G w (fun v ↦ (hw v).le) x
      (mem_triangleCenters G w x |>.mp x.property) (hC x))
    (fun (x : triangleCenters G w) (y : G.neighborFinset x.val) ↦
      div_pos (hw y) (hθ x)) (show 0 < t by omega) hdiff
  refine ⟨j, hj, ?_, ?_⟩
  · exact (triangleMeanEntropy_mono G hw hθ hT hC hj.le).trans hu
  · exact hnear

/-- The nearby-row quantity is the center, stationary-neighbor, and local-step average. -/
theorem triangleNearbyVariation_eq_expectation (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v) (j : ℕ) :
    triangleNearbyVariation G w hw hT hC j =
      (triangleCenterLaw G w hw hT).expectation (fun x ↦
        (triangleStationaryLaw G w hw x
          (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
          (triangleWalk G w hw x (hC x) v).expectation (fun z ↦
            (triangleSmoothedLaw G w hw x (hC x) j v).totalVariation
              (triangleSmoothedLaw G w hw x (hC x) j z)))) := by
  classical
  rfl

/-- Mean entropy disintegrates into a center and its stationary neighbor. -/
theorem triangleMeanEntropy_eq_expectation (G : SimpleGraph V) [DecidableRel G.Adj]
    (w θ : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hT : 0 < triangleMass G w)
    (hC : ∀ x v, G.Adj x v → 0 < commonNeighborhoodMass G w x v) (j : ℕ) :
    triangleMeanEntropy G w θ hw hT hC j =
      (triangleCenterLaw G w hw hT).expectation (fun x ↦
        (triangleStationaryLaw G w hw x
          (mem_triangleCenters G w x |>.mp x.property)).expectation (fun v ↦
            (triangleSmoothedLaw G w hw x (hC x) j v).referenceEntropy
              (fun y ↦ w y / θ x))) := by
  classical
  rw [triangleMeanEntropy_eq_family]
  rfl

end Cliquefree
