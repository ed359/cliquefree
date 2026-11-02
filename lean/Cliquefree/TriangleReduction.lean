module

public import Cliquefree.TriangleLocalEntropy
public import Cliquefree.TrianglePruning
public import Cliquefree.TriangleFiniteInduction
public import Cliquefree.TriangleLocalRejection
public import Cliquefree.TriangleSplitAssembly

/-! # The single reduction in the triangle dichotomy -/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u

namespace Cliquefree

/-- The two probabilistic splitting losses fit inside the rational acceptance threshold. -/
theorem triangle_split_loss_coefficient {t : ℕ} (ht : 32 ≤ t) :
    6 * (2 * Real.sqrt (((witnessA : ℝ) + 1) * Real.log t / t)) +
      6 * (2 * ((witnessA : ℝ) + 1) * Real.log t / Real.sqrt t) ≤
        (triangleLossRate t : ℝ) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hlog : 1 ≤ Real.log (t : ℝ) :=
    (Real.le_log_iff_exp_le ht').mpr (Real.exp_one_lt_three.le.trans (by
      exact_mod_cast (show 3 ≤ t by omega)))
  have hB : 1 ≤ ((witnessA : ℝ) + 1) * Real.log t := by
    nlinarith [show (0 : ℝ) ≤ witnessA by positivity]
  have hsqrt : Real.sqrt (((witnessA : ℝ) + 1) * Real.log t / t) ≤
      (((witnessA : ℝ) + 1) * Real.log t) / Real.sqrt t := by
    rw [Real.sqrt_div (by positivity)]
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    exact (Real.sqrt_le_iff).mpr ⟨by positivity, by nlinarith⟩
  have hpsi : 0 ≤ (witnessa : ℝ) * trianglePsi (t : ℝ) :=
    mul_nonneg (Nat.cast_nonneg _) (trianglePsi_nonneg (by exact_mod_cast (show 1 ≤ t by omega)))
  calc
    _ ≤ 24 * (((witnessA : ℝ) + 1) * Real.log t / Real.sqrt t) := by linear_combination 12 * hsqrt
    _ = (witnessa : ℝ) * trianglePsi (t : ℝ) := by
      simp only [witnessa, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, trianglePsi]
      ring
    _ ≤ 2 * (witnessa : ℝ) * trianglePsi (t : ℝ) := by nlinarith
    _ ≤ _ := (triangleLossRate_bounds ht).1

/-- A spanning subgraph projects to its original graph by the identity on vertices. -/
def EdgeProjection.ofSubgraph {V : Type*} {H G : SimpleGraph V} (h : H ≤ G) :
    EdgeProjection H G where
  vertex := id
  map_adj hxy := h hxy
  edge_injective _ _ hx hy := ⟨hx, hy⟩

/-- Successful tests in a prepared graph produce the required lower-load split. -/
theorem exists_prepared_triangle_split {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {w θ : V → ℝ} {t : ℕ} (ht : 32 ≤ t)
    (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v) (hT : 0 < triangleMass G w)
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
    ∃ (H : SimpleGraph (V × V)) (π : EdgeProjection H G),
      (∀ a, neighborhoodMass H (fun z ↦ w (π.vertex z)) a ≤
        2 ^ nextTriangleScale t * θ (π.vertex a)) ∧
      (1 - (triangleLossRate t : ℝ)) * triangleMass G w ≤
        triangleMass H (fun z ↦ w (π.vertex z)) := by
  classical
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  let hC := prepared_common_pos G ht' hθ hcommon
  obtain ⟨j, _, hH, hnear⟩ :=
    exists_triangleNearby_rows G ht hw hθ hT hC hbudget hload hcommon hfirst hsecond
  rw [triangleNearbyVariation_eq_expectation] at hnear
  have hreject := triangleSmoothedLaw_rejection_le G ht hw hθ hT hC hcommon j hH
  obtain ⟨x, _, _⟩ := exists_adj_of_triangleMass_pos G w hT
  let P := fun x : triangleCenters G w ↦ triangleSmoothedLaw G w (fun v ↦ (hw v).le) x (hC x) j
  obtain ⟨f, hload', _, hmass⟩ := exists_bounded_retaining_split G w θ
    (fun v ↦ (hw v).le) hθ hT hC x P (by positivity) hnear hreject
  let label := centerIncidenceLabel G w x f
  let keep := centerIncidenceKeep G w
    (fun x v y ↦ (w v / θ x) / (2 : ℝ) ^ nextTriangleScale t ≤ (P x y).mass v) f
  refine ⟨splitGraph G label keep, splitGraphProjection G label keep, hload', ?_⟩
  apply le_trans _ hmass
  apply mul_le_mul_of_nonneg_right _ hT.le
  have hc := triangle_split_loss_coefficient ht
  linarith only [hc]

/-- The single triangle reduction follows from pruning, the two tests, and the coupled split. -/
theorem triangle_reduction_step : TriangleReductionStep.{u} := by
  intro V inst G θ w t hθ hw htX hload htriangle
  classical
  have ht32 : 32 ≤ t := by have := witnessExponent_ge_256; omega
  have ht1 : 1 ≤ t := by omega
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hDnonneg := scaledDegreeBudget_nonneg G (fun v ↦ (hθ v).le) (fun v ↦ (hw v).le)
  have hTpos : 0 < triangleMass G w := by linarith
  obtain ⟨x, y, hxy⟩ := exists_adj_of_triangleMass_pos G w hTpos
  have hDpos := scaledDegreeBudget_pos_of_adj G hθ hw hxy
  obtain ⟨H, hHG, hcommon, hmass, _, hDHpos, hTH⟩ :=
    exists_prepared_subgraph_positive G hθ hw (t := (t : ℝ))
      (by exact_mod_cast ht1) hDpos htriangle
  let π₀ := EdgeProjection.ofSubgraph hHG
  have hHload : ∀ v, neighborhoodMass H w v ≤ (2 : ℝ) ^ t * θ v := fun v ↦
    (neighborhoodMass_subgraph_le hHG (fun z ↦ (hw z).le) v).trans (hload v)
  have hratio : ∀ x y, H.Adj x y → θ y ≤ ((t : ℝ) * 2 ^ t) * θ x := by
    intro x y hxy
    exact (div_le_iff₀ (hθ x)).mp
      (prepared_adjacent_scale_ratio H hθ (fun v ↦ (hw v).le) ht' hHload hcommon hxy.symm)
  by_cases hfirst : ∀ v,
      crossMass H w (H.neighborFinset v) (triangleClosure H w θ t v t) ≤
        (witnessC : ℝ) * (30 * (t : ℝ) ^ 3 * scaledMass θ w (H.neighborFinset v) +
          θ v ^ 2 / 2 ^ (30 * t ^ 3))
  swap
  · push Not at hfirst
    obtain ⟨v, hv⟩ := hfirst
    let q := triangleWitnessOfFirstTest H ht1 (fun z ↦ (hw z).le) hθ hHload hratio v (by
      simpa only [witnessC, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using hv)
    exact Or.inl ⟨q.project π₀ (fun z ↦ (hθ z).le) (fun z ↦ (hw z).le)⟩
  by_cases hsecond : ∀ v,
      crossMass H w (triangleExceptional H w θ t v) (H.neighborFinset v) ≤
        (witnessC : ℝ) * (2 * (t : ℝ) * scaledMass θ w (triangleExceptional H w θ t v) +
          θ v ^ 2 / 2 ^ (2 * t))
  swap
  · push Not at hsecond
    obtain ⟨v, hv⟩ := hsecond
    let q := triangleWitnessOfSecondTest H ht1 (fun z ↦ (hw z).le) (fun z ↦ (hθ z).le)
      hHload hratio v (triangleExceptional H w θ t v) (triangleExceptional_subset H w θ t v) (by
        simpa only [witnessC, Nat.cast_mul, Nat.cast_ofNat] using hv)
    exact Or.inl ⟨q.project π₀ (fun z ↦ (hθ z).le) (fun z ↦ (hw z).le)⟩
  obtain ⟨K, π, hKload, hKmass⟩ := exists_prepared_triangle_split H ht32 hw hθ
    (hDHpos.trans hTH) hTH.le hHload hcommon hfirst hsecond
  refine Or.inr ⟨V × V, inferInstance, K, π₀.comp π, hKload, ?_⟩
  apply le_trans _ hKmass
  have hδpos : (0 : ℝ) ≤ triangleLossRate t := by
    exact_mod_cast (triangleLossRate_pos ht32).le
  have hδhalf : (triangleLossRate t : ℝ) < 1 / 2 := by
    exact_mod_cast triangleLossRate_lt_half htX.le
  have hh := mul_le_mul_of_nonneg_left hmass (show 0 ≤ 1 - (triangleLossRate t : ℝ) by linarith)
  have hdiv : 0 ≤ scaledDegreeBudget G θ w / (t : ℝ) := div_nonneg hDnonneg ht'.le
  nlinarith only [hh, hδpos, hdiv]

end Cliquefree
