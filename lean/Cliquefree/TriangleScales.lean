module

public import Cliquefree.Constants

/-!
# Numerical scales for the triangle iteration
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

/-- The real decay envelope used to sum triangle losses. -/
def trianglePsi (t : ℝ) : ℝ := Real.log t / Real.sqrt t

/-- The next integer load exponent is the ceiling of its square root. -/
def nextTriangleScale (t : ℕ) : ℕ := ⌈Real.sqrt (t : ℝ)⌉₊

/-- The decay envelope is nonnegative above one. -/
theorem trianglePsi_nonneg {t : ℝ} (ht : 1 ≤ t) : 0 ≤ trianglePsi t :=
  div_nonneg (Real.log_nonneg ht) (Real.sqrt_nonneg t)

/-- The decay envelope decreases on the range used by the iteration. -/
theorem trianglePsi_antitone : AntitoneOn trianglePsi (Set.Ici (256 : ℝ)) := by
  have he : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  intro x hx y hy hxy
  exact Real.log_div_sqrt_antitoneOn (by change Real.exp 2 ≤ x; have hx' : 256 ≤ x := hx; linarith)
    (by change Real.exp 2 ≤ y; have hy' : 256 ≤ y := hy; linarith) hxy

/-- Increasing an argument by its square root cuts the decay envelope by at least half. -/
theorem trianglePsi_contract {s t : ℝ} (ht : 256 ≤ t)
    (hst : t * Real.sqrt t ≤ s) : trianglePsi s ≤ trianglePsi t / 2 := by
  have ht₀ : 0 < t := by linarith
  have hrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht₀
  have hr16 : 16 ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by norm_num; exact ht)
  have hrr4 : 4 ≤ Real.sqrt (Real.sqrt t) :=
    Real.le_sqrt_of_sq_le (by norm_num; exact hr16)
  have hbig : 256 ≤ t * Real.sqrt t := by nlinarith
  have hmono := trianglePsi_antitone hbig (hbig.trans hst) hst
  apply hmono.trans
  have hlog : 0 ≤ Real.log t := Real.log_nonneg (by linarith)
  unfold trianglePsi
  rw [Real.log_mul ht₀.ne' hrt.ne', Real.log_sqrt ht₀.le, Real.sqrt_mul ht₀.le]
  apply (div_le_iff₀ (mul_pos hrt (Real.sqrt_pos.mpr hrt))).mpr
  calc
    _ ≤ Real.log t * Real.sqrt (Real.sqrt t) / 2 := by
      nlinarith [mul_nonneg hlog (show 0 ≤ Real.sqrt (Real.sqrt t) - 3 by linarith)]
    _ = _ := by field_simp [hrt.ne']

/-- A ceiling-square-root step separates exponents by at least a square-root factor. -/
theorem nextTriangleScale_separation (s : ℕ) (ht : 16 ≤ nextTriangleScale s) :
    (nextTriangleScale s : ℝ) * Real.sqrt (nextTriangleScale s : ℝ) < s := by
  let t : ℝ := nextTriangleScale s
  have ht16 : 16 ≤ t := by dsimp [t]; exact_mod_cast ht
  have ht₀ : 0 ≤ t := by linarith
  have hr4 : 4 ≤ Real.sqrt t := Real.le_sqrt_of_sq_le (by norm_num; exact ht16)
  have hsq := Real.sq_sqrt ht₀
  have haux : 0 ≤ t - Real.sqrt t - 2 := by nlinarith
  have hprod := mul_nonneg ht₀ haux
  have hceil := Nat.ceil_lt_add_one (Real.sqrt_nonneg (s : ℝ))
  change t < Real.sqrt (s : ℝ) + 1 at hceil
  have hs := Real.sq_sqrt (Nat.cast_nonneg s : (0 : ℝ) ≤ s)
  have hroot := Real.sqrt_nonneg (s : ℝ)
  nlinarith [mul_pos (show 0 < Real.sqrt (s : ℝ) - (t - 1) by linarith)
      (show 0 < Real.sqrt (s : ℝ) + (t - 1) by linarith)]

/-- A logarithmic bound for the explicit cutoff. -/
theorem log_le_half_self {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / 2 := by
  have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.mpr hx)
  rw [Real.log_sqrt hx.le] at h
  nlinarith [Real.sq_sqrt hx.le, sq_nonneg (Real.sqrt x - 2)]

/-- The total relative loss at the fixed fourth-power cutoff is below one half. -/
theorem trianglePsi_cutoff_bound {a : ℝ} (ha : 0 < a) :
    16 * a * trianglePsi ((100 * a) ^ 4) ≤ 8 / 25 := by
  have hx : 0 < 100 * a := by positivity
  have hs : Real.sqrt ((100 * a) ^ 4) = (100 * a) ^ 2 := by
    rw [show (100 * a) ^ 4 = ((100 * a) ^ 2) ^ 2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  unfold trianglePsi
  rw [Real.log_pow, hs, ← mul_div_assoc]
  have hlog := log_le_half_self hx
  apply (div_le_iff₀ (sq_pos_of_pos hx)).mpr
  norm_num only [Nat.cast_ofNat]
  nlinarith [mul_le_mul_of_nonneg_left hlog ha.le]

/-- Ceiling-square-root load exponents strictly decrease above two. -/
theorem nextTriangleScale_lt {s : ℕ} (hs : 3 ≤ s) : nextTriangleScale s < s := by
  have hs' : (3 : ℝ) ≤ s := by exact_mod_cast hs
  have hceil : nextTriangleScale s ≤ s - 1 := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  omega

/-- Each nonterminal scale contracts the loss envelope when the next scale is above the cutoff. -/
theorem trianglePsi_nextScale {s : ℕ} (ht : 256 ≤ nextTriangleScale s) :
    trianglePsi (s : ℝ) ≤ trianglePsi (nextTriangleScale s : ℝ) / 2 := by
  apply trianglePsi_contract (by exact_mod_cast ht)
  exact (nextTriangleScale_separation s (by omega)).le

/-- The fixed cutoff lies within the decay-envelope monotonicity range. -/
theorem witnessExponent_ge_256 : 256 ≤ witnessExponent := by
  norm_num [witnessExponent, witnessa, witnessA, witnessC]

/-- The explicit absolute loss coefficient is positive. -/
theorem witnessa_pos : 0 < witnessa := by
  norm_num [witnessa, witnessA, witnessC]

/-- The fixed cutoff leaves a total relative-loss budget below one half. -/
theorem trianglePsi_witness_cutoff :
    16 * (witnessa : ℝ) * trianglePsi (witnessExponent : ℝ) ≤ 1 / 2 := by
  have ha : (0 : ℝ) < witnessa := by exact_mod_cast witnessa_pos
  have he : (witnessExponent : ℝ) = ((100 : ℝ) * witnessa) ^ 4 := by
    simp [witnessExponent]
  rw [he]
  exact (trianglePsi_cutoff_bound ha).trans (by norm_num)

end Cliquefree
