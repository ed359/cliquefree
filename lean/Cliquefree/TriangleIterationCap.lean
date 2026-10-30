module

public import Cliquefree.TriangleLossRates

/-!
# An invariant for the finite triangle-reduction induction

The cap below packages the geometric loss budget into a single scale-dependent bound.
-/

@[expose] public section

noncomputable section

namespace Cliquefree

/-- The inductive triangle-to-budget cap leaves room for all subsequent reduction losses. -/
def triangleIterationCap (t : ℕ) : ℝ :=
  if t ≤ witnessExponent then (triangleBoundConstant : ℝ) / 6
  else (triangleBoundConstant : ℝ) * (1 - 16 * witnessa * trianglePsi (t : ℝ))

/-- The decay envelope stays within the cutoff budget at every later reduction scale. -/
theorem trianglePsi_above_cutoff {t : ℕ} (ht : witnessExponent ≤ t) :
    16 * (witnessa : ℝ) * trianglePsi (t : ℝ) ≤ 1 / 2 := by
  have hm : trianglePsi (t : ℝ) ≤ trianglePsi (witnessExponent : ℝ) := by
    apply trianglePsi_antitone
    · change (256 : ℝ) ≤ witnessExponent
      exact_mod_cast witnessExponent_ge_256
    · change (256 : ℝ) ≤ t
      exact_mod_cast witnessExponent_ge_256.trans ht
    · exact_mod_cast ht
  exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans trianglePsi_witness_cutoff

/-- The cap is nonnegative and never exceeds the absolute triangle constant. -/
theorem triangleIterationCap_bounds (t : ℕ) :
    0 ≤ triangleIterationCap t ∧ triangleIterationCap t ≤ triangleBoundConstant := by
  have hB : (0 : ℝ) < triangleBoundConstant := by
    exact_mod_cast triangleBoundConstant_pos
  unfold triangleIterationCap
  split_ifs with ht
  · constructor <;> linarith
  · have hX : witnessExponent ≤ t := by omega
    have hcut := trianglePsi_above_cutoff hX
    have hψ : 0 ≤ trianglePsi (t : ℝ) :=
      trianglePsi_nonneg (by
        have ht1 : 1 ≤ t := by have := witnessExponent_ge_three.trans hX; omega
        exact_mod_cast ht1)
    have ha : (0 : ℝ) ≤ witnessa := Nat.cast_nonneg _
    have hm : 0 ≤ 16 * (witnessa : ℝ) * trianglePsi (t : ℝ) :=
      mul_nonneg (mul_nonneg (by norm_num) ha) hψ
    constructor
    · exact mul_nonneg hB.le (by linarith)
    · nlinarith

/-- At an active scale, the cap is at least half the absolute triangle constant. -/
theorem triangleIterationCap_ge_half {t : ℕ} (ht : witnessExponent < t) :
    (triangleBoundConstant : ℝ) / 2 ≤ triangleIterationCap t := by
  rw [triangleIterationCap, ite_eq_right (by omega)]
  have h := trianglePsi_above_cutoff ht.le
  have hB : (0 : ℝ) ≤ triangleBoundConstant := by
    exact_mod_cast triangleBoundConstant_pos.le
  nlinarith

/-- The decay envelope absorbs a reciprocal pruning loss. -/
theorem reciprocal_le_trianglePsi {t : ℕ} (ht : 32 ≤ t) :
    1 / (t : ℝ) ≤ trianglePsi (t : ℝ) := by
  have ht' : (32 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hspos := Real.sqrt_pos.mpr htpos
  have hsq := Real.sq_sqrt htpos.le
  have hs := Real.sqrt_nonneg (t : ℝ)
  have hst : Real.sqrt (t : ℝ) ≤ t := by nlinarith
  have hlog : 1 ≤ Real.log (t : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 32) ht'
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_gt_d9]
  calc
    _ ≤ 1 / Real.sqrt (t : ℝ) := one_div_le_one_div_of_le hspos hst
    _ ≤ _ := div_le_div_of_nonneg_right hlog hspos.le

/-- The cap at the next scale pays both the multiplicative and additive reduction losses. -/
theorem triangleIterationCap_step {t : ℕ} (ht : witnessExponent < t) :
    triangleIterationCap (nextTriangleScale t) + 1 / (t : ℝ) ≤
      (1 - (triangleLossRate t : ℝ)) * triangleIterationCap t := by
  have ht32 : 32 ≤ t := by have := witnessExponent_ge_256; omega
  have ht' : (32 : ℝ) ≤ t := by exact_mod_cast ht32
  have hB : (8 : ℝ) ≤ triangleBoundConstant := by
    exact_mod_cast triangleBoundConstant_ge_eight
  have hB₀ : (0 : ℝ) ≤ triangleBoundConstant := by linarith
  have hδ : (0 : ℝ) ≤ triangleLossRate t := by
    exact_mod_cast (triangleLossRate_pos ht32).le
  have hδhalf := (triangleLossRate_lt_half ht.le).le
  have hcap := triangleIterationCap_ge_half ht
  by_cases hn : nextTriangleScale t ≤ witnessExponent
  · rw [triangleIterationCap, ite_eq_left hn]
    have hrec : 1 / (t : ℝ) ≤ 1 / 32 :=
      one_div_le_one_div_of_le (by norm_num) ht'
    have hmul := mul_le_mul_of_nonneg_left hcap
      (show 0 ≤ 1 - (triangleLossRate t : ℝ) by linarith)
    have hmul₂ := mul_le_mul_of_nonneg_right hδhalf hB₀
    nlinarith only [hmul, hmul₂, hrec, hB]
  · have hnX : witnessExponent ≤ nextTriangleScale t := by omega
    have hcontract := trianglePsi_nextScale (witnessExponent_ge_256.trans hnX)
    have hψ := trianglePsi_nonneg (by linarith : (1 : ℝ) ≤ t)
    have ha : (1 : ℝ) ≤ witnessa := by
      exact_mod_cast witnessa_pos
    have hrec := reciprocal_le_trianglePsi ht32
    have hupper := (triangleLossRate_bounds ht32).2
    let e := 16 * (witnessa : ℝ) * trianglePsi (t : ℝ)
    let e' := 16 * (witnessa : ℝ) * trianglePsi (nextTriangleScale t : ℝ)
    have he : 0 ≤ e := mul_nonneg (mul_nonneg (by norm_num) (by linarith)) hψ
    have hrec' : 1 / (t : ℝ) ≤ e := by
      dsimp only [e]
      nlinarith only [hrec, mul_nonneg (show (0 : ℝ) ≤ 16 * witnessa - 1 by linarith) hψ]
    have he' : 2 * e ≤ e' := by
      have hm := mul_le_mul_of_nonneg_left hcontract
        (show (0 : ℝ) ≤ 16 * witnessa by linarith)
      dsimp only [e, e']
      linarith only [hm]
    have hδe : (triangleLossRate t : ℝ) ≤ e / 2 := by
      dsimp only [e]
      linarith only [hupper]
    have hrecB : 1 / (t : ℝ) ≤ (triangleBoundConstant : ℝ) * e / 2 := by
      nlinarith only [hrec', mul_nonneg (show (0 : ℝ) ≤ triangleBoundConstant / 2 - 1
        by linarith only [hB]) he]
    have hmulδ := mul_le_mul_of_nonneg_left hδe hB₀
    have hmulnext := mul_le_mul_of_nonneg_left he' hB₀
    have hcross := mul_nonneg hB₀ (mul_nonneg hδ he)
    rw [triangleIterationCap, ite_eq_right hn, triangleIterationCap, ite_eq_right (by omega)]
    change (triangleBoundConstant : ℝ) * (1 - e') + 1 / (t : ℝ) ≤
      (1 - (triangleLossRate t : ℝ)) * ((triangleBoundConstant : ℝ) * (1 - e))
    nlinarith only [hmulδ, hmulnext, hcross, hrecB]

end Cliquefree
