module

public import Cliquefree.TriangleEntropy

/-!
# Finite shared-rejection coupling
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

/-- Expectation under a kernel mixture is the iterated expectation. -/
theorem FiniteLaw.expectation_kernelMix {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ξ) (X : Ξ → ℝ) :
    (μ.kernelMix K).expectation X = μ.expectation (fun ω ↦ (K ω).expectation X) := by
  simp only [FiniteLaw.expectation, FiniteLaw.kernelMix, Finset.sum_mul, Finset.mul_sum,
    mul_assoc]
  exact Finset.sum_comm

/-- Push a finite probability law forward along a function of outcomes. -/
def FiniteLaw.map {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) : FiniteLaw Ξ :=
  μ.kernelMix (fun ω ↦ FiniteLaw.pure (f ω))

/-- Pushforward preserves the expectation of a pulled-back observable. -/
theorem FiniteLaw.expectation_map {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ]
    (μ : FiniteLaw Ω) (f : Ω → Ξ) (X : Ξ → ℝ) :
    (μ.map f).expectation X = μ.expectation (fun ω ↦ X (f ω)) := by
  simp only [FiniteLaw.map, FiniteLaw.expectation_kernelMix, FiniteLaw.expectation_pure]

/-- Normalize nonnegative finite weights of positive total mass into a probability law. -/
def FiniteLaw.normalize {Ω : Type*} [Fintype Ω] (w : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) (hW : 0 < ∑ ω, w ω) : FiniteLaw Ω where
  mass ω := w ω / ∑ ξ, w ξ
  nonneg ω := div_nonneg (hw ω) hW.le
  sum_mass := by rw [← Finset.sum_div]; exact div_self hW.ne'

/-- The intensity of atoms accepted by one pending row. -/
def acceptanceMass {I U : Type*} (S : Finset U) (w : U → ℝ)
    (a : I → U → Bool) (i : I) : ℝ := ∑ t ∈ S, if a i t then w t else 0

/-- Accepted atom intensity leading to a specified label. -/
def acceptanceLabelMass {I U Y : Type*} [DecidableEq Y] (S : Finset U) (w : U → ℝ)
    (a : I → U → Bool) (label : U → Y) (i : I) (y : Y) : ℝ :=
  ∑ t ∈ S, if a i t ∧ label t = y then w t else 0

/-- The intensity of atoms accepted by exactly one of two rows. -/
def acceptanceDifference {I U : Type*} (S : Finset U) (w : U → ℝ)
    (a : I → U → Bool) (i j : I) : ℝ := ∑ t ∈ S, if a i t ≠ a j t then w t else 0

/-- Removing an unaccepted atom does not change a row's acceptance intensity. -/
theorem acceptanceMass_erase {I U : Type*} [DecidableEq U] (S : Finset U) (w : U → ℝ)
    (a : I → U → Bool) (i : I) {t : U} (ht : t ∈ S) (ha : a i t = false) :
    acceptanceMass (S.erase t) w a i = acceptanceMass S w a i := by
  simpa only [acceptanceMass, ha, Bool.false_eq_true, ite_false, add_zero] using
    Finset.sum_erase_add S (fun t ↦ if a i t then w t else 0) ht

/-- Removing an unaccepted atom preserves every label intensity of that row. -/
theorem acceptanceLabelMass_erase {I U Y : Type*} [DecidableEq U] [DecidableEq Y]
    (S : Finset U) (w : U → ℝ) (a : I → U → Bool) (label : U → Y)
    (i : I) (y : Y) {t : U} (ht : t ∈ S) (ha : a i t = false) :
    acceptanceLabelMass (S.erase t) w a label i y = acceptanceLabelMass S w a label i y := by
  simpa only [acceptanceLabelMass, ha, Bool.false_eq_true, false_and, ite_false, add_zero] using
    Finset.sum_erase_add S (fun t ↦ if a i t ∧ label t = y then w t else 0) ht

/-- An atom on which two rows agree contributes nothing to their disagreement intensity. -/
theorem acceptanceDifference_erase {I U : Type*} [DecidableEq U]
    (S : Finset U) (w : U → ℝ) (a : I → U → Bool) (i j : I)
    {t : U} (ht : t ∈ S) (ha : a i t = a j t) :
    acceptanceDifference (S.erase t) w a i j = acceptanceDifference S w a i j := by
  simpa only [acceptanceDifference, ha, ne_eq, not_true_eq_false, ite_false, add_zero] using
    Finset.sum_erase_add S (fun t ↦ if a i t ≠ a j t then w t else 0) ht

/-- One shared accepted proposal preserves the prescribed one-row label marginal. -/
theorem acceptance_marginal_step {I U Y : Type*} [DecidableEq Y]
    (S : Finset U) (w : U → ℝ) (a : I → U → Bool) (label : U → Y) (i : I) (y : Y)
    (hrow : acceptanceMass S w a i = 1) (hT : 0 < ∑ t ∈ S, w t) :
    (∑ t ∈ S, w t / (∑ z ∈ S, w z) *
      (if a i t then (if label t = y then 1 else 0)
        else acceptanceLabelMass S w a label i y)) = acceptanceLabelMass S w a label i y := by
  let M := acceptanceLabelMass S w a label i y
  have hpoint (t : U) : w t * (if a i t then (if label t = y then 1 else 0) else M) =
      (if a i t ∧ label t = y then w t else 0) +
        (w t - (if a i t then w t else 0)) * M := by
    cases h : a i t <;> by_cases hy : label t = y <;> simp [hy]
  calc
    _ = (∑ t ∈ S, w t * (if a i t then (if label t = y then 1 else 0) else M)) /
        (∑ t ∈ S, w t) := by
      simp only [div_mul_eq_mul_div, Finset.sum_div, M]
    _ = (M + ((∑ t ∈ S, w t) - acceptanceMass S w a i) * M) / (∑ t ∈ S, w t) := by
      simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.sum_mul, Finset.sum_sub_distrib]
      rfl
    _ = M := by rw [hrow]; field_simp; ring

/-- The shared first proposal and recursive continuation preserve the factor-two coupling bound. -/
theorem acceptance_difference_step {I U : Type*}
    (S : Finset U) (w : U → ℝ) (hw : ∀ t ∈ S, 0 ≤ w t) (a : I → U → Bool) (i j : I)
    (hrow : acceptanceMass S w a i = 1) (hT : 0 < ∑ t ∈ S, w t) :
    (∑ t ∈ S, w t / (∑ z ∈ S, w z) *
      (if a i t ≠ a j t then 1 else if a i t then 0 else acceptanceDifference S w a i j)) ≤
      acceptanceDifference S w a i j := by
  let D := acceptanceDifference S w a i j
  let N : ℝ := ∑ t ∈ S, if a i t = false ∧ a j t = false then w t else 0
  have hD : 0 ≤ D := Finset.sum_nonneg (fun t ht ↦ by
    dsimp [D, acceptanceDifference]
    split_ifs <;> first | exact hw t ht | exact le_rfl)
  have hN : N ≤ (∑ t ∈ S, w t) - 1 := by
    have hsum : N + acceptanceMass S w a i ≤ ∑ t ∈ S, w t := by
      unfold N acceptanceMass
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_le_sum
      intro t ht
      cases hi : a i t <;> cases hj : a j t <;> simp [hw t ht]
    rw [hrow] at hsum
    linarith
  have hpoint (t : U) : w t *
      (if a i t ≠ a j t then 1 else if a i t then 0 else D) =
      (if a i t ≠ a j t then w t else 0) +
        (if a i t = false ∧ a j t = false then w t else 0) * D := by
    cases hi : a i t <;> cases hj : a j t <;> simp
  calc
    _ = (∑ t ∈ S, w t *
        (if a i t ≠ a j t then 1 else if a i t then 0 else D)) / (∑ t ∈ S, w t) := by
      simp only [div_mul_eq_mul_div, Finset.sum_div, D]
    _ = (D + N * D) / (∑ t ∈ S, w t) := by
      simp_rw [hpoint, Finset.sum_add_distrib, ← Finset.sum_mul]
      rfl
    _ ≤ D := by
      apply (div_le_iff₀ hT).mpr
      nlinarith [mul_le_mul_of_nonneg_right hN hD]

/-- Shared weighted proposals couple any normalized finite acceptance system.
Each row keeps its accepted-label marginal, while disagreement costs only the intensity of
atoms accepted by exactly one row. -/
theorem exists_acceptance_coupling {I U Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    (S : Finset U) (w : U → ℝ) (a : I → U → Bool) (label : U → Y) (R : Finset I)
    (hw : ∀ t ∈ S, 0 ≤ w t) (hrow : ∀ i ∈ R, acceptanceMass S w a i = 1) :
    ∃ μ : FiniteLaw (I → Y),
      (∀ i ∈ R, ∀ y, μ.expectation (fun f ↦ if f i = y then 1 else 0) =
        acceptanceLabelMass S w a label i y) ∧
      (∀ i ∈ R, ∀ j ∈ R, μ.expectation (fun f ↦ if f i ≠ f j then 1 else 0) ≤
        acceptanceDifference S w a i j) := by
  classical
  induction S using Finset.strongInductionOn generalizing R with
  | _ S ih =>
    by_cases hR : R.Nonempty
    swap
    · refine ⟨FiniteLaw.pure (fun _ ↦ Classical.choice inferInstance), ?_, ?_⟩ <;>
        intro i hi <;> exact (hR ⟨i, hi⟩).elim
    obtain ⟨i₀, hi₀⟩ := hR
    have hT : 0 < ∑ t ∈ S, w t := by
      have hle : acceptanceMass S w a i₀ ≤ ∑ t ∈ S, w t := by
        apply Finset.sum_le_sum
        intro t ht
        cases h : a i₀ t <;> simp [hw t ht]
      rw [hrow i₀ hi₀] at hle
      linarith
    let R' (t : U) := R.filter (fun i ↦ a i t = false)
    have hchildren (t : S) : ∃ μ : FiniteLaw (I → Y),
        (∀ i ∈ R' t, ∀ y, μ.expectation (fun f ↦ if f i = y then 1 else 0) =
          acceptanceLabelMass (S.erase t) w a label i y) ∧
        (∀ i ∈ R' t, ∀ j ∈ R' t, μ.expectation (fun f ↦ if f i ≠ f j then 1 else 0) ≤
          acceptanceDifference (S.erase t) w a i j) := by
      apply ih (S.erase t) (Finset.erase_ssubset t.property) (R' t)
      · intro x hx
        exact hw x (Finset.mem_erase.mp hx).2
      · intro i hi
        obtain ⟨hiR, hit⟩ := Finset.mem_filter.mp hi
        rw [acceptanceMass_erase S w a i t.property hit]
        exact hrow i hiR
    choose μ hμm hμd using hchildren
    let ν : S → FiniteLaw (I → Y) := fun t ↦
      (μ t).map (fun f i ↦ if a i t then label t else f i)
    have hTS : (∑ t : S, w t) = ∑ t ∈ S, w t := Finset.sum_coe_sort S w
    let p := FiniteLaw.normalize (fun t : S ↦ w t) (fun t ↦ hw t t.property)
      (by rw [hTS]; exact hT)
    refine ⟨p.kernelMix ν, ?_, ?_⟩
    · intro i hi y
      have hcond (t : S) : (ν t).expectation (fun f ↦ if f i = y then 1 else 0) =
          if a i t then (if label t = y then 1 else 0)
            else acceptanceLabelMass S w a label i y := by
        change ((μ t).map _).expectation _ = _
        rw [FiniteLaw.expectation_map]
        cases hit : a i t with
        | true => simp only [hit, ite_true, FiniteLaw.expectation_const]
        | false =>
          simp only [hit]
          have hm := hμm t i (Finset.mem_filter.mpr ⟨hi, hit⟩) y
          rw [acceptanceLabelMass_erase S w a label i y t.property hit] at hm
          exact hm
      rw [FiniteLaw.expectation_kernelMix]
      simp_rw [hcond]
      change (∑ t : S, w t / (∑ z : S, w z) *
        (if a i t then (if label t = y then 1 else 0)
          else acceptanceLabelMass S w a label i y)) = _
      rw [hTS, Finset.sum_coe_sort S (fun t : U ↦ w t / (∑ z ∈ S, w z) *
        (if a i t then (if label t = y then 1 else 0)
          else acceptanceLabelMass S w a label i y))]
      exact acceptance_marginal_step S w a label i y (hrow i hi) hT
    · intro i hi j hj
      have hcond (t : S) : (ν t).expectation (fun f ↦ if f i ≠ f j then 1 else 0) ≤
          if a i t ≠ a j t then 1 else if a i t then 0
            else acceptanceDifference S w a i j := by
        change ((μ t).map _).expectation _ ≤ _
        rw [FiniteLaw.expectation_map]
        cases hit : a i t <;> cases hjt : a j t
        · simp only [hit, hjt, Bool.false_eq_true, ite_false, ne_eq, not_true_eq_false]
          have hd := hμd t i (Finset.mem_filter.mpr ⟨hi, hit⟩)
            j (Finset.mem_filter.mpr ⟨hj, hjt⟩)
          rw [acceptanceDifference_erase S w a i j t.property (hit.trans hjt.symm)] at hd
          exact hd
        · simp only [hit, hjt]
          norm_num
          apply FiniteLaw.expectation_le
          intro f _
          split_ifs <;> norm_num
        · simp only [hit, hjt]
          norm_num
          apply FiniteLaw.expectation_le
          intro f _
          split_ifs <;> norm_num
        · simp [hit, hjt]
      rw [FiniteLaw.expectation_kernelMix]
      change (∑ t : S, w t / (∑ z : S, w z) *
        (ν t).expectation (fun f ↦ if f i ≠ f j then 1 else 0)) ≤ _
      calc
        _ ≤ ∑ t : S, w t / (∑ z : S, w z) *
            (if a i t ≠ a j t then 1 else if a i t then 0
              else acceptanceDifference S w a i j) := by
          apply Finset.sum_le_sum
          intro t _
          exact mul_le_mul_of_nonneg_left (hcond t)
            (div_nonneg (hw t t.property) (by rw [hTS]; exact hT.le))
        _ = ∑ t ∈ S, w t / (∑ z ∈ S, w z) *
            (if a i t ≠ a j t then 1 else if a i t then 0
              else acceptanceDifference S w a i j) := by
          rw [hTS, Finset.sum_coe_sort S (fun t : U ↦ w t / (∑ z ∈ S, w z) *
            (if a i t ≠ a j t then 1 else if a i t then 0
              else acceptanceDifference S w a i j))]
        _ ≤ _ := acceptance_difference_step S w hw a i j (hrow i hi) hT

/-- Summing all accepted-label intensities recovers the acceptance intensity. -/
theorem sum_acceptanceLabelMass {I U Y : Type*} [Fintype Y] [DecidableEq Y]
    (S : Finset U) (w : U → ℝ) (a : I → U → Bool) (label : U → Y) (i : I) :
    (∑ y, acceptanceLabelMass S w a label i y) = acceptanceMass S w a i := by
  unfold acceptanceLabelMass acceptanceMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  cases h : a i t <;> simp

/-- An exact finite threshold-atom representation gives the simultaneous coupling bound. -/
theorem exists_grandCoupling_of_atoms {I U Y : Type*} [Fintype I] [DecidableEq I]
    [Fintype Y] [DecidableEq Y]
    (P : I → FiniteLaw Y) (S : Finset U) (w : U → ℝ) (a : I → U → Bool) (label : U → Y)
    (hw : ∀ t ∈ S, 0 ≤ w t)
    (hm : ∀ i y, acceptanceLabelMass S w a label i y = (P i).mass y)
    (hd : ∀ i j, acceptanceDifference S w a i j = ∑ y, |(P i).mass y - (P j).mass y|) :
    ∃ μ : FiniteLaw (I → Y),
      (∀ i y, μ.expectation (fun f ↦ if f i = y then 1 else 0) = (P i).mass y) ∧
      (∀ i j, μ.expectation (fun f ↦ if f i ≠ f j then 1 else 0) ≤
        2 * (P i).totalVariation (P j)) := by
  classical
  by_cases hY : Nonempty Y
  · let : Nonempty Y := hY
    have hrow (i : I) : acceptanceMass S w a i = 1 := by
      rw [← sum_acceptanceLabelMass S w a label i]
      simp only [hm, FiniteLaw.sum_mass]
    obtain ⟨μ, hμm, hμd⟩ := exists_acceptance_coupling S w a label Finset.univ hw
      (fun i _ ↦ hrow i)
    refine ⟨μ, ?_, ?_⟩
    · intro i y
      exact (hμm i (Finset.mem_univ _) y).trans (hm i y)
    · intro i j
      calc
        _ ≤ acceptanceDifference S w a i j :=
          hμd i (Finset.mem_univ _) j (Finset.mem_univ _)
        _ = ∑ y, |(P i).mass y - (P j).mass y| := hd i j
        _ = 2 * (P i).totalVariation (P j) := by unfold FiniteLaw.totalVariation; ring
  · have hI : IsEmpty I := ⟨fun i ↦ by
      obtain ⟨y, _⟩ := (P i).exists_pos_mass
      exact hY ⟨y⟩⟩
    let : IsEmpty I := hI
    refine ⟨FiniteLaw.pure (fun i ↦ isEmptyElim i), ?_, ?_⟩ <;>
      intro i <;> exact isEmptyElim i

end Cliquefree
