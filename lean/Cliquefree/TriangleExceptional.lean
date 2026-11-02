module

public import Cliquefree.TriangleClosureBounds
public import Cliquefree.TriangleWalks
public import Cliquefree.TriangleAverages

/-! # Exceptional starting pairs in the triangle reduction -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Neighbors whose reference mass in the terminal closure exceeds the prescribed threshold. -/
def triangleExceptional (G : SimpleGraph V) (w θ : V → ℝ) (t : ℕ) (v : V) : Finset V := by
  classical
  exact (G.neighborFinset v).filter (fun x ↦
    (t : ℝ) ^ 10 * θ x < neighborhoodMassOn G w (triangleClosure G w θ t v t) x)

/-- Exceptional vertices are neighbors of the starting vertex. -/
theorem triangleExceptional_subset (G : SimpleGraph V) [DecidableRel G.Adj]
    (w θ : V → ℝ) (t : ℕ) (v : V) : triangleExceptional G w θ t v ⊆ G.neighborFinset v := by
  classical
  intro x hx
  simpa only [SimpleGraph.mem_neighborFinset] using (Finset.mem_filter.mp hx).1

/-- A nonexceptional neighbor sees at most the threshold mass in the terminal closure. -/
theorem neighborhoodMassOn_le_of_not_exceptional (G : SimpleGraph V) (w θ : V → ℝ)
    (t : ℕ) {v x : V} (hx : G.Adj v x) (hn : x ∉ triangleExceptional G w θ t v) :
    neighborhoodMassOn G w (triangleClosure G w θ t v t) x ≤ (t : ℝ) ^ 10 * θ x := by
  classical
  apply le_of_not_gt
  intro h
  exact hn (Finset.mem_filter.mpr ⟨(G.mem_neighborFinset v x).mpr hx, h⟩)

/-- Exceptional scaled mass is bounded by the first cross mass divided by its threshold. -/
theorem triangleExceptional_scaledMass_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} (hw : ∀ x, 0 ≤ w x) (t : ℕ) (v : V) :
    (t : ℝ) ^ 10 * scaledMass θ w (triangleExceptional G w θ t v) ≤
      crossMass G w (G.neighborFinset v) (triangleClosure G w θ t v t) := by
  classical
  let B := triangleExceptional G w θ t v
  let S := triangleClosure G w θ t v t
  calc
    _ ≤ crossMass G w B S := by
      rw [crossMass_eq_sum_neighborhoodMassOn]
      unfold scaledMass weightSum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro x hx
      have hh := (Finset.mem_filter.mp hx).2.le
      change (t : ℝ) ^ 10 * θ x ≤ neighborhoodMassOn G w S x at hh
      simpa only [mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_right hh (hw x)
    _ ≤ _ := by
      rw [crossMass_eq_sum_neighborhoodMassOn, crossMass_eq_sum_neighborhoodMassOn]
      exact Finset.sum_le_sum_of_subset_of_nonneg (triangleExceptional_subset G w θ t v)
        (fun x _ _ ↦ mul_nonneg (hw x) (neighborhoodMassOn_nonneg G hw S x))

/-- Combining the two successful tests bounds the exceptional cross mass. -/
theorem triangleExceptional_cross_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} {t : ℕ} (ht : 1 ≤ t) (hw : ∀ x, 0 ≤ w x)
    {C : ℝ} (hC : 0 ≤ C) (v : V)
    (hfirst : crossMass G w (G.neighborFinset v) (triangleClosure G w θ t v t) ≤
      C * (30 * (t : ℝ) ^ 3 * scaledMass θ w (G.neighborFinset v) +
        θ v ^ 2 / 2 ^ (30 * t ^ 3)))
    (hsecond : crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v) ≤
      C * (2 * (t : ℝ) * scaledMass θ w (triangleExceptional G w θ t v) +
        θ v ^ 2 / 2 ^ (2 * t))) :
    crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v) ≤
      (60 * C ^ 2 / (t : ℝ) ^ 6) * scaledMass θ w (G.neighborFinset v) +
        (2 * C ^ 2 / ((t : ℝ) ^ 9 * 2 ^ (30 * t ^ 3)) + C / 2 ^ (2 * t)) * θ v ^ 2 := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hb : scaledMass θ w (triangleExceptional G w θ t v) ≤
      C * (30 * (t : ℝ) ^ 3 * scaledMass θ w (G.neighborFinset v) +
        θ v ^ 2 / 2 ^ (30 * t ^ 3)) / (t : ℝ) ^ 10 := by
    apply (le_div_iff₀ (pow_pos ht' _)).mpr
    simpa only [mul_comm] using (triangleExceptional_scaledMass_bound G hw t v).trans hfirst
  apply hsecond.trans
  calc
    _ ≤ C * (2 * (t : ℝ) *
        (C * (30 * (t : ℝ) ^ 3 * scaledMass θ w (G.neighborFinset v) +
          θ v ^ 2 / 2 ^ (30 * t ^ 3)) / (t : ℝ) ^ 10) + θ v ^ 2 / 2 ^ (2 * t)) := by
      gcongr
    _ = _ := by field_simp; ring

/-- The exceptional cross bound can charge its scale remainder to the local degree budget. -/
theorem triangleExceptional_cross_budget_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} {t : ℕ} (ht : 1 ≤ t) (hw : ∀ x, 0 ≤ w x) (hθ : ∀ x, 0 ≤ θ x)
    {C : ℝ} (hC : 0 ≤ C) (v : V)
    (hlower : (∃ x, G.Adj v x) → θ v ≤ (t : ℝ) * neighborhoodMass G w v)
    (hfirst : crossMass G w (G.neighborFinset v) (triangleClosure G w θ t v t) ≤
      C * (30 * (t : ℝ) ^ 3 * scaledMass θ w (G.neighborFinset v) +
        θ v ^ 2 / 2 ^ (30 * t ^ 3)))
    (hsecond : crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v) ≤
      C * (2 * (t : ℝ) * scaledMass θ w (triangleExceptional G w θ t v) +
        θ v ^ 2 / 2 ^ (2 * t))) :
    crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v) ≤
      (60 * C ^ 2 / (t : ℝ) ^ 6) * scaledMass θ w (G.neighborFinset v) +
        (2 * C ^ 2 / ((t : ℝ) ^ 9 * 2 ^ (30 * t ^ 3)) + C / 2 ^ (2 * t)) *
          ((t : ℝ) * θ v * neighborhoodMass G w v) := by
  classical
  by_cases hv : ∃ x, G.Adj v x
  · apply (triangleExceptional_cross_bound G ht hw hC v hfirst hsecond).trans
    apply add_le_add_right
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hh := mul_le_mul_of_nonneg_left (hlower hv) (hθ v)
    nlinarith only [hh]
  · have hN : G.neighborFinset v = ∅ := by
      ext x
      simp only [Finset.notMem_empty, iff_false, SimpleGraph.mem_neighborFinset]
      exact fun hx ↦ hv ⟨x, hx⟩
    have hz := neighborhoodMass_eq_zero_of_isolated G w (fun x hx ↦ hv ⟨x, hx⟩)
    simp [hN, hz, crossMass, scaledMass, weightSum]

/-- Summing the two cross-mass tests charges all exceptional pairs to the degree budget. -/
theorem triangleExceptional_weighted_cross_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} {t : ℕ} (ht : 1 ≤ t) (hw : ∀ x, 0 ≤ w x) (hθ : ∀ x, 0 ≤ θ x)
    {C : ℝ} (hC : 0 ≤ C)
    (hlower : ∀ v, (∃ x, G.Adj v x) → θ v ≤ (t : ℝ) * neighborhoodMass G w v)
    (hfirst : ∀ v, crossMass G w (G.neighborFinset v) (triangleClosure G w θ t v t) ≤
      C * (30 * (t : ℝ) ^ 3 * scaledMass θ w (G.neighborFinset v) +
        θ v ^ 2 / 2 ^ (30 * t ^ 3)))
    (hsecond : ∀ v,
      crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v) ≤
        C * (2 * (t : ℝ) * scaledMass θ w (triangleExceptional G w θ t v) +
          θ v ^ 2 / 2 ^ (2 * t))) :
    (∑ v, w v * crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v)) ≤
      (60 * C ^ 2 / (t : ℝ) ^ 6 + 2 * C ^ 2 / ((t : ℝ) ^ 8 * 2 ^ (30 * t ^ 3)) +
        C * (t : ℝ) / 2 ^ (2 * t)) * scaledDegreeBudget G θ w := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ ↦
    mul_le_mul_of_nonneg_left
      (triangleExceptional_cross_budget_bound G ht hw hθ hC v (hlower v)
        (hfirst v) (hsecond v)) (hw v))
  apply hh.trans_eq
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  simp_rw [show ∀ v, w v * (60 * C ^ 2 / (t : ℝ) ^ 6 *
      scaledMass θ w (G.neighborFinset v)) =
      (60 * C ^ 2 / (t : ℝ) ^ 6) * (w v * scaledMass θ w (G.neighborFinset v)) by
    intro v; ring]
  rw [← Finset.mul_sum, sum_weight_scaledMass_neighborhood]
  have he : (∑ v, w v *
      ((2 * C ^ 2 / ((t : ℝ) ^ 9 * 2 ^ (30 * t ^ 3)) + C / 2 ^ (2 * t)) *
        ((t : ℝ) * θ v * neighborhoodMass G w v))) =
      (2 * C ^ 2 / ((t : ℝ) ^ 8 * 2 ^ (30 * t ^ 3)) + C * (t : ℝ) / 2 ^ (2 * t)) *
        scaledDegreeBudget G θ w := by
    unfold scaledDegreeBudget
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    field_simp
  rw [he]
  ring

omit [Fintype V] in
/-- Above the initial cutoff, a seventh power is dominated by the dyadic square. -/
theorem pow_seven_le_two_pow_twice {t : ℕ} (ht : 32 ≤ t) :
    (t : ℝ) ^ 7 ≤ (2 : ℝ) ^ (2 * t) := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have hn' : (32 : ℝ) ≤ n := by exact_mod_cast hn
    have hp : ((n : ℝ) + 1) ^ 7 ≤ 4 * (n : ℝ) ^ 7 := by
      calc
        _ ≤ ((33 / 32 : ℝ) * n) ^ 7 := pow_le_pow_left₀ (by positivity) (by linarith) _
        _ = (33 / 32 : ℝ) ^ 7 * (n : ℝ) ^ 7 := mul_pow _ _ _
        _ ≤ 4 * (n : ℝ) ^ 7 := mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
    calc
      ((n + 1 : ℕ) : ℝ) ^ 7 ≤ 4 * (n : ℝ) ^ 7 := by simpa using hp
      _ ≤ 4 * (2 : ℝ) ^ (2 * n) := mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (2 : ℝ) ^ (2 * (n + 1)) := by rw [Nat.mul_add, pow_add]; norm_num; ring

omit [Fintype V] in
/-- The exceptional-pair coefficient is bounded uniformly at all admissible scales. -/
theorem triangleExceptional_coefficient_le {t : ℕ} (ht : 32 ≤ t) {C : ℝ} (hC : 1 ≤ C) :
    60 * C ^ 2 / (t : ℝ) ^ 6 + 2 * C ^ 2 / ((t : ℝ) ^ 8 * 2 ^ (30 * t ^ 3)) +
      C * (t : ℝ) / 2 ^ (2 * t) ≤ 72 * C ^ 2 / (t : ℝ) ^ 6 := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have htpos : (0 : ℝ) < t := by linarith
  have hcpos : 0 ≤ C := by linarith
  have hd : (t : ℝ) ^ 6 ≤ (t : ℝ) ^ 8 * 2 ^ (30 * t ^ 3) := by
    calc
      _ ≤ (t : ℝ) ^ 8 := pow_le_pow_right₀ ht' (by norm_num)
      _ ≤ _ := le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num))
  have hsecond : 2 * C ^ 2 / ((t : ℝ) ^ 8 * 2 ^ (30 * t ^ 3)) ≤
      2 * C ^ 2 / (t : ℝ) ^ 6 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hd
  have hlast : C * (t : ℝ) / 2 ^ (2 * t) ≤ C ^ 2 / (t : ℝ) ^ 6 := by
    calc
      _ ≤ C / (t : ℝ) ^ 6 := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        calc
          C * (t : ℝ) * (t : ℝ) ^ 6 = C * (t : ℝ) ^ 7 := by ring
          _ ≤ C * 2 ^ (2 * t) :=
            mul_le_mul_of_nonneg_left (pow_seven_le_two_pow_twice ht) hcpos
      _ ≤ _ := div_le_div_of_nonneg_right (by nlinarith) (by positivity)
  have hz : 0 ≤ C ^ 2 / (t : ℝ) ^ 6 := by positivity
  calc
    _ ≤ 60 * C ^ 2 / (t : ℝ) ^ 6 + 2 * C ^ 2 / (t : ℝ) ^ 6 + C ^ 2 / (t : ℝ) ^ 6 :=
      add_le_add (add_le_add_right hsecond _) hlast
    _ ≤ _ := by simp only [mul_div_assoc]; nlinarith only [hz]

/-- A retained edge supplies the lower load needed to charge exceptional scale remainders. -/
theorem prepared_theta_le_load (G : SimpleGraph V) {w θ : V → ℝ} {t : ℝ}
    (ht : 0 < t) (hw : ∀ x, 0 ≤ w x)
    (hcommon : ∀ x y, G.Adj x y → max (θ x) (θ y) / t ≤
      commonNeighborhoodMass G w x y) (v : V) (hv : ∃ x, G.Adj v x) :
    θ v ≤ t * neighborhoodMass G w v := by
  obtain ⟨x, hx⟩ := hv
  have hh := (hcommon v x hx).trans (commonNeighborhoodMass_le_left G hw v x)
  have hm := (div_le_iff₀ ht).mp hh
  nlinarith [le_max_left (θ v) (θ x)]

open Classical in
/-- Successful cross-mass tests make exceptional directed starting pairs rare. -/
theorem triangleExceptional_probability_le (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} {t : ℕ} (ht : 32 ≤ t) (hw : ∀ x, 0 ≤ w x) (hθ : ∀ x, 0 ≤ θ x)
    {C : ℝ} (hC : 1 ≤ C) (hT : 0 < triangleMass G w)
    (hbudget : scaledDegreeBudget G θ w ≤ triangleMass G w)
    (hcommon : ∀ x y, G.Adj x y → max (θ x) (θ y) / (t : ℝ) ≤
      commonNeighborhoodMass G w x y)
    (hfirst : ∀ v, crossMass G w (G.neighborFinset v) (triangleClosure G w θ t v t) ≤
      C * (30 * (t : ℝ) ^ 3 * scaledMass θ w (G.neighborFinset v) +
        θ v ^ 2 / 2 ^ (30 * t ^ 3)))
    (hsecond : ∀ v,
      crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v) ≤
        C * (2 * (t : ℝ) * scaledMass θ w (triangleExceptional G w θ t v) +
          θ v ^ 2 / 2 ^ (2 * t))) :
    (triangleEdgeLaw G w hw hT).expectation
      (fun e ↦ if e.1 ∈ triangleExceptional G w θ t e.2 then 1 else 0) ≤
        12 * C ^ 2 / (t : ℝ) ^ 6 := by
  classical
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hcpos : 0 ≤ C := by linarith
  have hh := triangleExceptional_weighted_cross_bound G (by omega) hw hθ hcpos
    (prepared_theta_le_load G ht' hw hcommon) hfirst hsecond
  have hbound : (∑ v, w v *
      crossMass G w (triangleExceptional G w θ t v) (G.neighborFinset v)) ≤
      (72 * C ^ 2 / (t : ℝ) ^ 6) * triangleMass G w := by
    calc
      _ ≤ _ := hh
      _ ≤ (72 * C ^ 2 / (t : ℝ) ^ 6) * scaledDegreeBudget G θ w :=
        mul_le_mul_of_nonneg_right (triangleExceptional_coefficient_le ht hC)
          (scaledDegreeBudget_nonneg G hθ hw)
      _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (by positivity)
  rw [triangleEdgeLaw_exceptional_probability G w hw hT _ (triangleExceptional_subset G w θ t)]
  calc
    _ ≤ ((72 * C ^ 2 / (t : ℝ) ^ 6) * triangleMass G w) / (6 * triangleMass G w) :=
      div_le_div_of_nonneg_right hbound (by positivity)
    _ = _ := by field_simp; ring

end Cliquefree
