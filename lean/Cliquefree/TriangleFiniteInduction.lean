module

public import Cliquefree.TriangleIterationCap
public import Cliquefree.TriangleProjection

/-!
# Finite induction assembling the triangle dichotomy

Strong induction on the load exponent assembles the triangle dichotomy from a single reduction.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u

namespace Cliquefree

/-- The triangle alternative for real weights used in the stationary-maximizer argument. -/
def TriangleDichotomy : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (θ w : V → ℝ),
    (∀ v, 0 < θ v) → (∀ v, 0 < w v) →
      triangleMass G w ≤ (triangleBoundConstant : ℝ) * scaledDegreeBudget G θ w ∨
        Nonempty (TriangleWitness G θ w)

/-- The graph-specific one-step obligation needed by the finite triangle induction. -/
def TriangleReductionStep : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (θ w : V → ℝ) (t : ℕ),
    (∀ v, 0 < θ v) → (∀ v, 0 < w v) → witnessExponent < t →
    (∀ v, neighborhoodMass G w v ≤ (2 : ℝ) ^ t * θ v) →
    2 * scaledDegreeBudget G θ w < triangleMass G w →
    Nonempty (TriangleWitness G θ w) ∨
      ∃ (W : Type u) (_ : Fintype W) (H : SimpleGraph W) (π : EdgeProjection H G),
        (∀ v, neighborhoodMass H (fun z ↦ w (π.vertex z)) v ≤
          (2 : ℝ) ^ nextTriangleScale t * θ (π.vertex v)) ∧
        (1 - (triangleLossRate t : ℝ)) * triangleMass G w -
          scaledDegreeBudget G θ w / (t : ℝ) ≤
          triangleMass H (fun z ↦ w (π.vertex z))

/-- A terminal load scale directly bounds triangles by the terminal cap. -/
theorem triangle_terminal_cap {V : Type u} [Fintype V]
    (G : SimpleGraph V) {θ w : V → ℝ} (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v)
    {t : ℕ} (ht : t ≤ witnessExponent)
    (hload : ∀ v, neighborhoodMass G w v ≤ (2 : ℝ) ^ t * θ v) :
    triangleMass G w ≤ triangleIterationCap t * scaledDegreeBudget G θ w := by
  have hpow : (2 : ℝ) ^ t ≤ triangleBoundConstant := by
    change (2 : ℝ) ^ t ≤ ((2 : ℚ) ^ witnessExponent : ℚ)
    rw [Rat.cast_pow, Rat.cast_ofNat]
    exact pow_le_pow_right₀ (by norm_num) ht
  have hbudget := scaledDegreeBudget_nonneg G hθ hw
  have htri := triangleMass_le_load_budget G hw hload
  rw [triangleIterationCap, ite_eq_left ht]
  have hmul := mul_le_mul_of_nonneg_right hpow hbudget
  nlinarith only [hmul, htri]

/-- Strong induction in the load exponent either bounds triangles or produces a witness. -/
theorem triangle_alternative_of_reduction (hs : TriangleReductionStep.{u}) (t : ℕ) :
    ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (θ w : V → ℝ),
      (∀ v, 0 < θ v) → (∀ v, 0 < w v) →
      (∀ v, neighborhoodMass G w v ≤ (2 : ℝ) ^ t * θ v) →
      triangleMass G w ≤ triangleIterationCap t * scaledDegreeBudget G θ w ∨
        Nonempty (TriangleWitness G θ w) := by
  induction t using Nat.strong_induction_on with
  | h t ih =>
    intro V inst G θ w hθ hw hload
    classical
    have hD := scaledDegreeBudget_nonneg G (fun v ↦ (hθ v).le) (fun v ↦ (hw v).le)
    by_cases ht : t ≤ witnessExponent
    · exact Or.inl (triangle_terminal_cap G (fun v ↦ (hθ v).le) (fun v ↦ (hw v).le)
        ht hload)
    have htX : witnessExponent < t := by omega
    have ht3 : 3 ≤ t := witnessExponent_ge_three.trans htX.le
    have hB : (8 : ℝ) ≤ triangleBoundConstant := by
      exact_mod_cast triangleBoundConstant_ge_eight
    have hcap := triangleIterationCap_ge_half htX
    by_cases hsmall : triangleMass G w ≤ 2 * scaledDegreeBudget G θ w
    · left
      have hmul := mul_le_mul_of_nonneg_right
        (show (2 : ℝ) ≤ triangleIterationCap t by linarith only [hB, hcap]) hD
      exact hsmall.trans hmul
    rcases hs V G θ w t hθ hw htX hload (lt_of_not_ge hsmall) with hq | hsplit
    · exact Or.inr hq
    obtain ⟨W, instW, H, π, hload', hkeep⟩ := hsplit
    let : Fintype W := instW
    have hn := nextTriangleScale_lt ht3
    have hθ' : ∀ v, 0 < θ (π.vertex v) := fun v ↦ hθ _
    have hw' : ∀ v, 0 < w (π.vertex v) := fun v ↦ hw _
    rcases ih (nextTriangleScale t) hn W H _ _ hθ' hw' hload' with hbound | hq
    · left
      have hD' := π.scaledDegreeBudget_le (fun v ↦ (hθ v).le) (fun v ↦ (hw v).le)
      have hupper := hbound.trans
        (mul_le_mul_of_nonneg_left hD' (triangleIterationCap_bounds _).1)
      have hcoeff := mul_le_mul_of_nonneg_right (triangleIterationCap_step htX) hD
      have hδ : 0 < 1 - (triangleLossRate t : ℝ) := by
        have h := triangleLossRate_lt_half htX.le
        linarith only [h]
      have hscaled :
          (1 - (triangleLossRate t : ℝ)) * triangleMass G w ≤
            (1 - (triangleLossRate t : ℝ)) *
              (triangleIterationCap t * scaledDegreeBudget G θ w) := by
        have hdiv : scaledDegreeBudget G θ w / (t : ℝ) =
            (1 / (t : ℝ)) * scaledDegreeBudget G θ w := by ring
        rw [hdiv] at hkeep
        nlinarith only [hkeep, hupper, hcoeff]
      exact (mul_le_mul_iff_right₀ hδ).mp hscaled
    · right
      obtain ⟨q⟩ := hq
      exact ⟨q.project π (fun v ↦ (hθ v).le) (fun v ↦ (hw v).le)⟩

/-- Finitely many normalized loads admit a common dyadic upper bound. -/
theorem exists_dyadic_load_bound {V : Type u} [Fintype V]
    (G : SimpleGraph V) {θ w : V → ℝ} (hθ : ∀ v, 0 < θ v) (hw : ∀ v, 0 ≤ w v) :
    ∃ t : ℕ, ∀ v, neighborhoodMass G w v ≤ (2 : ℝ) ^ t * θ v := by
  obtain ⟨t, ht⟩ := pow_unbounded_of_one_lt
    (∑ v, neighborhoodMass G w v / θ v) (by norm_num : (1 : ℝ) < 2)
  refine ⟨t, fun v ↦ ?_⟩
  have hv : neighborhoodMass G w v / θ v ≤ ∑ z, neighborhoodMass G w z / θ z :=
    Finset.single_le_sum
      (fun z _ ↦ div_nonneg (neighborhoodMass_nonneg G hw z) (hθ z).le)
      (Finset.mem_univ v)
  exact (div_le_iff₀ (hθ v)).mp (hv.trans ht.le)

/-- The single graph reduction implies the triangle dichotomy. -/
theorem triangle_dichotomy_of_reduction (hs : TriangleReductionStep.{u}) :
    TriangleDichotomy.{u} := by
  intro V inst G θ w hθ hw
  obtain ⟨t, ht⟩ := exists_dyadic_load_bound G hθ (fun v ↦ (hw v).le)
  rcases triangle_alternative_of_reduction hs t V G θ w hθ hw ht with h | hq
  · left
    exact h.trans (mul_le_mul_of_nonneg_right (triangleIterationCap_bounds t).2
      (scaledDegreeBudget_nonneg G (fun v ↦ (hθ v).le) (fun v ↦ (hw v).le)))
  · exact Or.inr hq

end Cliquefree
