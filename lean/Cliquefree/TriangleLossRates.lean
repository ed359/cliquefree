module

public import Cliquefree.TriangleScales

/-!
# Rational loss thresholds for accepted triangle reductions
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

/-- The rational acceptance threshold uses an integer binary ceiling logarithm. -/
def triangleLossRate (t : ℕ) : ℚ :=
  2 * (witnessa : ℚ) * Nat.clog 2 t / Nat.sqrt t

/-- Casting the rational threshold preserves its explicit arithmetic expression. -/
theorem triangleLossRate_cast (t : ℕ) :
    (triangleLossRate t : ℝ) =
      2 * (witnessa : ℝ) * (Nat.clog 2 t : ℝ) / (Nat.sqrt t : ℝ) := by
  simp [triangleLossRate]

/-- Above thirty-two, the integer ceiling logarithm lies between the natural logarithm
and twice it. -/
theorem natClog_log_bounds {t : ℕ} (ht : 32 ≤ t) :
    Real.log (t : ℝ) ≤ (Nat.clog 2 t : ℝ) ∧
      (Nat.clog 2 t : ℝ) ≤ 2 * Real.log (t : ℝ) := by
  have ht' : (32 : ℝ) ≤ t := by exact_mod_cast ht
  have htpos : (0 : ℝ) < t := by linarith
  have hk : 0 < Nat.clog 2 t := Nat.clog_pos (by norm_num) (by omega)
  have hk' : (1 : ℝ) ≤ Nat.clog 2 t := by exact_mod_cast hk
  have hlog₂ : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at this ⊢
    exact this
  have hlogt : 2 ≤ Real.log (t : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 32) ht'
    rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith [Real.log_two_gt_d9]
  constructor
  · have hpow : (t : ℝ) ≤ 2 ^ Nat.clog 2 t := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) t
    have h := Real.log_le_log htpos hpow
    rw [Real.log_pow] at h
    have hm := mul_le_mul_of_nonneg_left hlog₂ (Nat.cast_nonneg (Nat.clog 2 t) : (0 : ℝ) ≤ _)
    linarith
  · have hpow : (2 : ℝ) ^ (Nat.clog 2 t - 1) < t := by
      exact_mod_cast Nat.pow_pred_clog_lt_self (by norm_num : 1 < 2) (by omega : 1 < t)
    have h := Real.log_lt_log (pow_pos (by norm_num) _) hpow
    rw [Real.log_pow, Nat.cast_sub (by omega : 1 ≤ Nat.clog 2 t), Nat.cast_one] at h
    have hlo : (2 / 3 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
    have hm := mul_le_mul_of_nonneg_left hlo (show (0 : ℝ) ≤ Nat.clog 2 t - 1 by linarith)
    nlinarith

/-- The integer square root lies between half the real square root and the real square root. -/
theorem natSqrt_real_bounds {t : ℕ} (ht : 1 ≤ t) :
    Real.sqrt (t : ℝ) / 2 ≤ (Nat.sqrt t : ℝ) ∧
      (Nat.sqrt t : ℝ) ≤ Real.sqrt (t : ℝ) := by
  have hq : 0 < Nat.sqrt t := Nat.sqrt_pos.mpr (by omega)
  have hq' : (1 : ℝ) ≤ Nat.sqrt t := by exact_mod_cast hq
  have h : Real.sqrt (t : ℝ) < (Nat.sqrt t : ℝ) + 1 :=
    Real.real_sqrt_lt_nat_sqrt_succ
  exact ⟨by linarith, Real.nat_sqrt_le_real_sqrt⟩

/-- The rational threshold lies between two and eight times the scaled real decay envelope. -/
theorem triangleLossRate_bounds {t : ℕ} (ht : 32 ≤ t) :
    2 * (witnessa : ℝ) * trianglePsi (t : ℝ) ≤ (triangleLossRate t : ℝ) ∧
      (triangleLossRate t : ℝ) ≤ 8 * (witnessa : ℝ) * trianglePsi (t : ℝ) := by
  have htpos : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have ha : (0 : ℝ) < witnessa := by exact_mod_cast witnessa_pos
  have hq : (0 : ℝ) < Nat.sqrt t := by
    exact_mod_cast Nat.sqrt_pos.mpr (show 0 < t by omega)
  have hr : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.mpr htpos
  obtain ⟨hloglo, hloghi⟩ := natClog_log_bounds ht
  obtain ⟨hsqrtlo, hsqrthi⟩ := natSqrt_real_bounds (by omega : 1 ≤ t)
  have hlog : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ t by omega))
  rw [triangleLossRate_cast]
  constructor
  · calc
      _ = 2 * (witnessa : ℝ) * Real.log (t : ℝ) / Real.sqrt (t : ℝ) := by
        unfold trianglePsi
        ring
      _ ≤ 2 * (witnessa : ℝ) * (Nat.clog 2 t : ℝ) / Real.sqrt (t : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hloglo (by positivity)) hr.le
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hq hsqrthi
  · calc
      _ ≤ 2 * (witnessa : ℝ) * (2 * Real.log (t : ℝ)) / (Nat.sqrt t : ℝ) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hloghi (by positivity)) hq.le
      _ ≤ 2 * (witnessa : ℝ) * (2 * Real.log (t : ℝ)) / (Real.sqrt (t : ℝ) / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hsqrtlo
      _ = _ := by unfold trianglePsi; ring

/-- The rational acceptance threshold is positive in the range where reductions are made. -/
theorem triangleLossRate_pos {t : ℕ} (ht : 32 ≤ t) : 0 < triangleLossRate t := by
  have ha : (0 : ℚ) < witnessa := by exact_mod_cast witnessa_pos
  have hk : (0 : ℚ) < Nat.clog 2 t := by
    exact_mod_cast Nat.clog_pos (by norm_num : 1 < 2) (by omega : 1 < t)
  have hq : (0 : ℚ) < Nat.sqrt t := by
    exact_mod_cast Nat.sqrt_pos.mpr (show 0 < t by omega)
  unfold triangleLossRate
  positivity

/-- At the absolute cutoff, the rational acceptance threshold is strictly smaller than one half. -/
theorem triangleLossRate_lt_half {t : ℕ} (ht : witnessExponent ≤ t) :
    (triangleLossRate t : ℝ) < 1 / 2 := by
  have ht32 : 32 ≤ t := by have := witnessExponent_ge_256; omega
  have h := (triangleLossRate_bounds ht32).2
  have ha : (0 : ℝ) ≤ witnessa := Nat.cast_nonneg _
  have hm : trianglePsi (t : ℝ) ≤ trianglePsi (witnessExponent : ℝ) := by
    apply trianglePsi_antitone
    · change (256 : ℝ) ≤ witnessExponent
      exact_mod_cast witnessExponent_ge_256
    · change (256 : ℝ) ≤ t
      exact_mod_cast witnessExponent_ge_256.trans ht
    · exact_mod_cast ht
  have hmul := mul_le_mul_of_nonneg_left hm (show (0 : ℝ) ≤ 8 * witnessa by positivity)
  have hb := trianglePsi_witness_cutoff
  linarith only [h, hmul, hb]

end Cliquefree
