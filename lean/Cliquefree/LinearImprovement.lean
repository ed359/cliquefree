module

public import Cliquefree.ImprovementIdentities
public import Cliquefree.RandomPartition
public import Cliquefree.ScalarCurvature
public import Cliquefree.TriangleClosure
public import Cliquefree.SparseRestriction
public import Cliquefree.LinearAmplification

/-!
# Deterministic improvements with a linear clique-order budget

The existence proof uses a sparse restriction and uniform amplification, with zero residual.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

omit [Fintype V] in
/-- A cross mass is at most the product of its two nonnegative set masses. -/
theorem crossMass_le_weightSum_mul (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (A B : Finset V) :
    crossMass G w A B ≤ weightSum w A * weightSum w B := by
  classical
  rw [crossMass_eq_sum_neighborhoodMassOn]
  have hn (v : V) : neighborhoodMassOn G w B v ≤ weightSum w B := by
    apply Finset.sum_le_sum
    intro y _
    split_ifs
    · exact le_rfl
    · exact hw y
  calc
    _ ≤ ∑ v ∈ A, w v * weightSum w B :=
      Finset.sum_le_sum (fun v _ ↦ mul_le_mul_of_nonneg_left (hn v) (hw v))
    _ = _ := by rw [← Finset.sum_mul]; rfl

omit [Fintype V] in
/-- Removing vertices below a pointwise crossing threshold costs the corresponding budget. -/
theorem crossMass_filter_lower (G : SimpleGraph V) {w θ : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (hθ : ∀ v, 0 ≤ θ v) (A B : Finset V)
    {p δ : ℝ} (hp : 0 ≤ p) (hδ : 0 ≤ δ) :
    crossMass G w A B - p * scaledMass θ w A - δ * weightSum w A ≤
      crossMass G w (A.filter (fun v ↦ p * θ v + δ < neighborhoodMassOn G w B v)) B := by
  classical
  rw [crossMass_eq_sum_neighborhoodMassOn, crossMass_eq_sum_neighborhoodMassOn]
  simp only [scaledMass, weightSum, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_filter]
  apply Finset.sum_le_sum
  intro v hv
  split_ifs with h
  · have hnonneg := add_nonneg (mul_nonneg hp (mul_nonneg (hθ v) (hw v)))
      (mul_nonneg hδ (hw v))
    linarith
  · have hbound := mul_le_mul_of_nonneg_left (le_of_not_gt h) (hw v)
    nlinarith only [hbound]

omit [Fintype V] in
/-- A pointwise crossing threshold gives a strict crossing gain on a nonempty set. -/
theorem crossMass_gt_scaled_threshold (G : SimpleGraph V) {w θ : V → ℝ}
    (hw : ∀ v, 0 < w v) {C B : Finset V} (hC : C.Nonempty) {p δ : ℝ}
    (h : ∀ v ∈ C, p * θ v + δ < neighborhoodMassOn G w B v) :
    p * scaledMass θ w C + δ * weightSum w C < crossMass G w C B := by
  rw [crossMass_eq_sum_neighborhoodMassOn]
  simp only [scaledMass, weightSum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_lt_sum_of_nonempty hC
  intro v hv
  have hm := mul_lt_mul_of_pos_left (h v hv) (hw v)
  nlinarith only [hm]

/-- Uniform lifting and deletion have an exact deterministic quadratic cost. -/
theorem uniform_improvement_edgeMass (G : SimpleGraph V) (w : V → ℝ)
    (C B : Finset V) (hCB : Disjoint C B) (k : ℝ) :
    edgeMass G (fun v ↦ improvedWeights w C B k (fun _ ↦ 1) v - w v) =
      k ^ 2 * edgeMass (G.induce (C : Set V)) (fun v ↦ w v) +
        edgeMass (G.induce (B : Set V)) (fun v ↦ w v) - k * crossMass G w C B := by
  classical
  rw [improvedWeights_sub_eq w C B hCB]
  simp only [mul_one]
  rw [edgeMass_sub_scale, edgeMass_extendByZero, edgeMass_extendByZero]
  congr 1
  rw [sum_extendByZero_neighborhoodMass, crossMass_eq_subtype_sum]

/-- The linear scale budget controls tangent losses under a bounded uniform amplification. -/
theorem uniform_improvement_tangent_loss {u w θ : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) {r p : ℕ} (hr : 2 ≤ r)
    (hb : ∀ v, 24 * (r : ℝ) * scalarXi (u v) (w v) ≤ θ v * w v)
    (C B : Finset V) (hCB : Disjoint C B) {k : ℝ} (hk : 0 ≤ k)
    (hlog : Real.log (1 + k) ≤ 12 * (r : ℝ) * p) :
    (∑ v, (scalarPotential (u v) (w v) + deriv (scalarPotential (u v)) (w v) *
      (improvedWeights w C B k (fun _ ↦ 1) v - w v) -
        scalarPotential (u v) (improvedWeights w C B k (fun _ ↦ 1) v))) ≤
      2 * k * p * scaledMass θ w C + scaledMass θ w B := by
  classical
  have hr' : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hpoint (v : V) :
      scalarPotential (u v) (w v) + deriv (scalarPotential (u v)) (w v) *
        (improvedWeights w C B k (fun _ ↦ 1) v - w v) -
          scalarPotential (u v) (improvedWeights w C B k (fun _ ↦ 1) v) ≤
        (if v ∈ C then 2 * k * p * (θ v * w v) else 0) +
          if v ∈ B then θ v * w v else 0 := by
    have hξ := scalarXi_pos (hu v) (hw v)
    by_cases hvC : v ∈ C
    · have hvB : v ∉ B := fun h ↦ Finset.disjoint_left.mp hCB hvC h
      simp only [improvedWeights, ite_eq_right hvB, ite_eq_left hvC, mul_one, add_zero]
      have hloss := scalarPotential_tangent_loss (hu v) (hw v) (by linarith : 1 ≤ 1 + k)
      have h1 := mul_le_mul_of_nonneg_left hlog
        (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hξ.le) hk)
      have h2 := mul_le_mul_of_nonneg_left (hb v)
        (show 0 ≤ 2 * k * (p : ℝ) by positivity)
      nlinarith only [hloss, h1, h2]
    · by_cases hvB : v ∈ B
      · simp only [improvedWeights, ite_eq_left hvB, ite_eq_right hvC, zero_add,
          scalarPotential_tangent_loss_zero]
        have hK : 1 ≤ 24 * (r : ℝ) := by linarith
        have hmul := mul_le_mul_of_nonneg_right hK hξ.le
        linarith [hb v]
      · simp [improvedWeights, hvC, hvB]
  calc
    _ ≤ ∑ v, ((if v ∈ C then 2 * k * p * (θ v * w v) else 0) +
        if v ∈ B then θ v * w v else 0) := Finset.sum_le_sum (fun v _ ↦ hpoint v)
    _ = _ := by
      simp [Finset.sum_add_distrib, Finset.sum_ite_mem, scaledMass, weightSum, Finset.mul_sum]

/-- A strong triangle witness contradicts stationarity and global maximality at linear scale. -/
theorem exists_stationary_linear_improvement (G : SimpleGraph V) {u w θ : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) (hθ : ∀ v, 0 < θ v)
    {r : ℕ} (hr : 2 ≤ r) (hG : G.CliqueFree r)
    (hz : ∀ v, residual G u w v = 0)
    (hb : ∀ v, 24 * (r : ℝ) * scalarXi (u v) (w v) ≤ θ v * w v)
    (W : TriangleWitness G θ w) :
    ∃ q : V → ℝ, (∀ v, 0 ≤ q v) ∧ graphPotential G u w < graphPotential G u q := by
  classical
  let ρ := θ W.scaleVertex
  let t : ℝ := 2 ^ W.p
  let δ := ρ / t ^ 2
  have hρ : 0 < ρ := hθ W.scaleVertex
  have ht : 0 < t := pow_pos (by norm_num) _
  have ht2 : 2 ≤ t := by
    have h := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) W.p_pos
    simpa only [pow_one] using h
  have hδ : 0 < δ := div_pos hρ (sq_pos_of_pos ht)
  have hw0 : ∀ v, 0 ≤ w v := fun v ↦ (hw v).le
  have hb0 : ∀ v, 0 ≤ θ v * w v := fun v ↦ (mul_pos (hθ v) (hw v)).le
  have hbase : 0 < ρ ^ 2 / t := div_pos (sq_pos_of_pos hρ) ht
  obtain ⟨A, B, hA, hB, hAB, _, _, hmargin⟩ :=
    exists_disjoint_strong_witness G w (fun v ↦ θ v * w v) hb0 W.A W.B
      (Nat.cast_nonneg W.p) hbase W.cross_large
  change 11 / 2 * W.p * scaledMass θ w W.A + 6 * (ρ ^ 2 / t) <
    crossMass G w A B - W.p * scaledMass θ w A at hmargin
  have hwA : weightSum w A ≤ ρ * t :=
    (Finset.sum_le_sum_of_subset_of_nonneg hA (fun v _ _ ↦ hw0 v)).trans W.weight_A
  have hwB : weightSum w B ≤ ρ * t :=
    (Finset.sum_le_sum_of_subset_of_nonneg hB (fun v _ _ ↦ hw0 v)).trans W.weight_B
  have hbB : scaledMass θ w B ≤ ρ ^ 2 * t ^ 2 := by
    have hsub : scaledMass θ w B ≤ scaledMass θ w W.B :=
      Finset.sum_le_sum_of_subset_of_nonneg hB (fun v _ _ ↦ hb0 v)
    have heq : (2 : ℝ) ^ (2 * W.p) = t ^ 2 := by
      dsimp [t]
      rw [← pow_mul]
      congr 1
      omega
    simpa only [heq] using hsub.trans W.scaled_B
  let H := A.filter (fun v ↦ (W.p : ℝ) * θ v + δ < neighborhoodMassOn G w B v)
  have hfilter := crossMass_filter_lower G hw0 (fun v ↦ (hθ v).le) A B
    (Nat.cast_nonneg W.p) hδ.le
  change crossMass G w A B - W.p * scaledMass θ w A - δ * weightSum w A ≤
    crossMass G w H B at hfilter
  have hδA : δ * weightSum w A ≤ ρ ^ 2 / t := by
    calc
      _ ≤ δ * (ρ * t) := mul_le_mul_of_nonneg_left hwA hδ.le
      _ = _ := by dsimp [δ]; field_simp
  have hlarge : 5 * (ρ ^ 2 / t) < crossMass G w H B := by
    have hmass : 0 ≤ 11 / 2 * (W.p : ℝ) * scaledMass θ w W.A := by
      have h := weightSum_nonneg hb0 W.A
      change 0 ≤ scaledMass θ w W.A at h
      positivity
    linarith only [hmargin, hfilter, hδA, hmass]
  have hupper : crossMass G w H B ≤ weightSum w H * (ρ * t) :=
    (crossMass_le_weightSum_mul G hw0 H B).trans
      (mul_le_mul_of_nonneg_left hwB (weightSum_nonneg hw0 H))
  have hHmass : ρ / t ^ 2 < weightSum w H := by
    apply (mul_lt_mul_iff_left₀ (mul_pos hρ ht)).mp
    calc
      _ = ρ ^ 2 / t := by field_simp
      _ < crossMass G w H B := by linarith only [hlarge, hbase]
      _ ≤ _ := hupper
  have hHne : H.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro he
    rw [he, weightSum_empty] at hHmass
    exact (not_lt_of_ge hδ.le) hHmass
  obtain ⟨C, hCH, hCne, hCmass, hsparse⟩ :=
    exists_sparseRestriction G hr hG w hw hHne
      (one_le_pow₀ (show (1 : ℝ) ≤ t by linarith) : 1 ≤ t ^ 12)
  have hCw : 0 < weightSum w C := Finset.sum_pos (fun v _ ↦ hw v) hCne
  have hCA : C ⊆ A := hCH.trans (Finset.filter_subset _ _)
  have hCB : Disjoint C B := Finset.disjoint_left.mpr (fun v hv hB ↦
    Finset.disjoint_left.mp hAB (hCA hv) hB)
  let k := ρ * t ^ 8 / weightSum w C
  have hk : 0 < k := div_pos (mul_pos hρ (pow_pos ht _)) hCw
  have hlog : Real.log (1 + k) ≤ 12 * (r : ℝ) * W.p :=
    linear_amplification_log_le hr W.p_pos hρ hCw hHmass hCmass
  let q := improvedWeights w C B k (fun _ ↦ 1)
  refine ⟨q, improvedWeights_nonneg hw0 C B hk.le (fun _ ↦ zero_le_one), ?_⟩
  have hloss := uniform_improvement_tangent_loss hu hw hr hb C B hCB hk.le hlog
  have hcross := crossMass_gt_scaled_threshold G hw hCne
    (fun v hv ↦ (Finset.mem_filter.mp (hCH hv)).2)
  have hcross' := mul_lt_mul_of_pos_left hcross (show 0 < 2 * k by positivity)
  have heC := two_mul_edgeMass_induce_le_of_sparseRestriction G w hw0 C hsparse
  have heC' := mul_le_mul_of_nonneg_left heC (sq_nonneg k)
  have heB : 2 * edgeMass (G.induce (B : Set V)) (fun v ↦ w v) ≤ ρ ^ 2 * t ^ 2 := by
    have he := two_mul_edgeMass_le_total_sq (G.induce (B : Set V)) (fun v ↦ hw0 v)
    have hsum : (∑ v : (B : Set V), w v) = weightSum w B :=
      sum_restrict_eq_weightSum B w
    rw [hsum] at he
    have hnonneg := weightSum_nonneg hw0 B
    nlinarith [sq_nonneg (ρ * t - weightSum w B)]
  have hchange := graphPotential_change G u w q
  simp only [hz, zero_mul, Finset.sum_const_zero, zero_sub] at hchange
  dsimp only [q] at hchange ⊢
  rw [uniform_improvement_edgeMass G w C B hCB k] at hchange
  have hgain := linear_amplification_gain_pos ht2 hρ hCw
  change 0 < 2 * k * δ * weightSum w C -
    k ^ 2 * weightSum w C ^ 2 / t ^ 12 - 2 * ρ ^ 2 * t ^ 2 at hgain
  have hstep : 2 * k * δ * weightSum w C - scaledMass θ w B -
      2 * k ^ 2 * edgeMass (G.induce (C : Set V)) (fun v ↦ w v) -
        2 * edgeMass (G.induce (B : Set V)) (fun v ↦ w v) <
      graphPotential G u (improvedWeights w C B k (fun _ ↦ 1)) - graphPotential G u w := by
    nlinarith only [hchange, hloss, hcross']
  have heC'' : 2 * k ^ 2 * edgeMass (G.induce (C : Set V)) (fun v ↦ w v) ≤
      k ^ 2 * weightSum w C ^ 2 / t ^ 12 := by
    convert heC' using 1 <;> ring
  linarith only [hstep, heC'', heB, hbB, hgain]

end Cliquefree
