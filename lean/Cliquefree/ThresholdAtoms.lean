module

public import Cliquefree.GrandCoupling
public import Mathlib.Data.Finset.Sort
public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Finite threshold atoms for shared proposals

Consecutive intervals between finitely many probability thresholds realize exact marginals
and the total variation disagreement intensity.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

/-- Consecutive threshold intervals telescope to every threshold in an increasing list. -/
theorem threshold_prefix_sum {n : ℕ} (f : Fin (n + 1) → ℝ)
    (hf : StrictMono f) (h₀ : f 0 = 0) (j : Fin (n + 1)) :
    (∑ i : Fin n, if f i.succ ≤ f j then f i.succ - f i.castSucc else 0) = f j := by
  classical
  refine Fin.cases ?_ (fun k ↦ ?_) j
  · have hn (i : Fin n) : ¬f i.succ ≤ f 0 := not_le.mpr (hf (by simp))
    calc
      _ = 0 := Finset.sum_eq_zero (fun i _ ↦ ite_eq_right (hn i))
      _ = f 0 := h₀.symm
  · simp only [hf.le_iff_le, Fin.succ_le_succ_iff]
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun i : Fin n ↦ i ≤ k) = Finset.Iic k := by
      ext i
      simp
    rw [he, Fin.sum_Iic_sub, h₀, sub_zero]

/-- The interval intensity accepted by exactly one of two thresholds is their distance. -/
theorem threshold_difference_sum {n : ℕ} (f : Fin (n + 1) → ℝ)
    (hf : StrictMono f) (h₀ : f 0 = 0) (j k : Fin (n + 1)) :
    (∑ i : Fin n, if decide (f i.succ ≤ f j) ≠ decide (f i.succ ≤ f k) then
      f i.succ - f i.castSucc else 0) = |f j - f k| := by
  classical
  have hordered (j k : Fin (n + 1)) (hjk : j ≤ k) :
      (∑ i : Fin n, if decide (f i.succ ≤ f j) ≠ decide (f i.succ ≤ f k) then
        f i.succ - f i.castSucc else 0) = f k - f j := by
    have hpoint (i : Fin n) :
        (if decide (f i.succ ≤ f j) ≠ decide (f i.succ ≤ f k) then
          f i.succ - f i.castSucc else 0) =
        (if f i.succ ≤ f k then f i.succ - f i.castSucc else 0) -
          (if f i.succ ≤ f j then f i.succ - f i.castSucc else 0) := by
      by_cases hj : f i.succ ≤ f j
      · have hk := hj.trans (hf.monotone hjk)
        simp [hj, hk]
      · by_cases hk : f i.succ ≤ f k <;> simp [hj, hk]
    simp_rw [hpoint, Finset.sum_sub_distrib, threshold_prefix_sum f hf h₀]
  rcases le_total j k with hjk | hkj
  · rw [hordered j k hjk, abs_of_nonpos (sub_nonpos.mpr (hf.monotone hjk))]
    ring
  · have he : (∑ i : Fin n, if decide (f i.succ ≤ f j) ≠ decide (f i.succ ≤ f k) then
        f i.succ - f i.castSucc else 0) =
        ∑ i : Fin n, if decide (f i.succ ≤ f k) ≠ decide (f i.succ ≤ f j) then
          f i.succ - f i.castSucc else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [ne_comm]
    rw [he, hordered k j hkj, abs_of_nonneg (sub_nonneg.mpr (hf.monotone hkj))]

/-- Any finite family of nonnegative values lies in a strictly increasing threshold list
from zero. -/
theorem exists_threshold_list {I : Type*} [Finite I] (p : I → ℝ)
    (hp : ∀ i, 0 ≤ p i) :
    ∃ (n : ℕ) (f : Fin (n + 1) → ℝ), StrictMono f ∧ f 0 = 0 ∧
      ∀ i, ∃ j, f j = p i := by
  classical
  let := Fintype.ofFinite I
  let S := insert 0 (Finset.univ.image p)
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  let n := S.card - 1
  have hn : S.card = n + 1 := by have := Finset.card_pos.mpr hS; dsimp [n]; omega
  let e := S.orderIsoOfFin hn
  let f : Fin (n + 1) → ℝ := fun j ↦ e j
  have hf : StrictMono f := (S.orderEmbOfFin hn).strictMono
  have hmem : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have h₀ : f 0 = 0 := by
    apply le_antisymm
    · have h := hf.monotone (Fin.zero_le (e.symm ⟨0, hmem⟩))
      simpa only [f, e.apply_symm_apply] using h
    · have h := (e 0).property
      rcases Finset.mem_insert.mp h with heq | hm
      · exact le_of_eq heq.symm
      · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hm
        change 0 ≤ (e 0 : ℝ)
        rw [← hi]
        exact hp i
  refine ⟨n, f, hf, h₀, ?_⟩
  intro i
  have hi : p i ∈ S := Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨i, Finset.mem_univ i, rfl⟩)
  exact ⟨e.symm ⟨p i, hi⟩, congrArg Subtype.val (e.apply_symm_apply ⟨p i, hi⟩)⟩

/-- Every finite family of laws has threshold atoms with exact marginals and differences. -/
theorem exists_finite_threshold_atoms {I Y : Type*} [Finite I] [Fintype Y]
    [DecidableEq Y] (P : I → FiniteLaw Y) :
    ∃ (n : Y → ℕ) (w : (Σ y, Fin (n y)) → ℝ) (a : I → (Σ y, Fin (n y)) → Bool),
      (∀ t, 0 ≤ w t) ∧
      (∀ i y, acceptanceLabelMass Finset.univ w a Sigma.fst i y = (P i).mass y) ∧
      ∀ i j, acceptanceDifference Finset.univ w a i j =
        ∑ y, |(P i).mass y - (P j).mass y| := by
  classical
  choose n f hf h₀ hcover using fun y ↦
    exists_threshold_list (fun i ↦ (P i).mass y) (fun i ↦ (P i).nonneg y)
  let w : (Σ y, Fin (n y)) → ℝ := fun t ↦ f t.1 t.2.succ - f t.1 t.2.castSucc
  let a : I → (Σ y, Fin (n y)) → Bool :=
    fun i t ↦ decide (f t.1 t.2.succ ≤ (P i).mass t.1)
  have hprefix (i : I) (y : Y) :
      (∑ k : Fin (n y), if f y k.succ ≤ (P i).mass y then
        f y k.succ - f y k.castSucc else 0) = (P i).mass y := by
    obtain ⟨j, hj⟩ := hcover y i
    rw [← hj]
    exact threshold_prefix_sum (f y) (hf y) (h₀ y) j
  refine ⟨n, w, a, ?_, ?_, ?_⟩
  · intro t
    exact sub_nonneg.mpr ((hf t.1).monotone (by simp [Fin.le_def]))
  · intro i y
    simp only [acceptanceLabelMass, Fintype.sum_sigma]
    have hpoint (z : Y) :
        (∑ k : Fin (n z), if a i ⟨z, k⟩ ∧ z = y then
          w ⟨z, k⟩ else 0) = if z = y then (P i).mass y else 0 := by
      by_cases hz : z = y
      · subst z
        simp only [a, w, decide_eq_true_eq, and_true]
        exact hprefix i y
      · simp [hz]
    simp_rw [hpoint]
    simp
  · intro i j
    simp only [acceptanceDifference, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro y _
    obtain ⟨ki, hi⟩ := hcover y i
    obtain ⟨kj, hj⟩ := hcover y j
    change (∑ k : Fin (n y), if decide (f y k.succ ≤ (P i).mass y) ≠
      decide (f y k.succ ≤ (P j).mass y) then
        f y k.succ - f y k.castSucc else 0) = _
    rw [← hi, ← hj]
    exact threshold_difference_sum (f y) (hf y) (h₀ y) ki kj

/-- Finite grand couplings have exact marginals and at most twice total variation disagreement. -/
theorem exists_grand_coupling {I Y : Type*} [Fintype I] [Fintype Y]
    [DecidableEq I] [DecidableEq Y] (P : I → FiniteLaw Y) :
    ∃ μ : FiniteLaw (I → Y),
      (∀ i y, μ.expectation (fun f ↦ if f i = y then 1 else 0) = (P i).mass y) ∧
      ∀ i j, μ.expectation (fun f ↦ if f i ≠ f j then 1 else 0) ≤
        2 * (P i).totalVariation (P j) := by
  classical
  obtain ⟨n, w, a, hw, hm, hd⟩ := exists_finite_threshold_atoms P
  exact exists_grandCoupling_of_atoms P Finset.univ w a Sigma.fst (fun t _ ↦ hw t) hm hd

end Cliquefree
