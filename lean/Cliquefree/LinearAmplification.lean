module

public import Mathlib

/-!
# Numerical bounds for deterministic sparse amplification
-/

@[expose] public section

noncomputable section

namespace Cliquefree

/-- The sparse restriction loses only linearly many powers in the clique order. -/
theorem linear_amplification_log_le {r p : ℕ} (hr : 2 ≤ r) (hp : 1 ≤ p)
    {ρ H C : ℝ} (hρ : 0 < ρ) (hC : 0 < C)
    (hH : ρ / ((2 : ℝ) ^ p) ^ 2 < H)
    (hMass : H / (((2 : ℝ) ^ p) ^ 12) ^ (r - 2) ≤ C) :
    Real.log (1 + ρ * ((2 : ℝ) ^ p) ^ 8 / C) ≤ 12 * (r : ℝ) * p := by
  let t : ℝ := 2 ^ p
  let A : ℝ := (t ^ 12) ^ (r - 2)
  let N : ℕ := 12 * (r - 2) + 10
  have ht : 2 ≤ t := by
    dsimp [t]
    simpa using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hp
  have htpos : 0 < t := by linarith
  have hA : 0 < A := by dsimp [A]; positivity
  have hH' : ρ < H * t ^ 2 := (div_lt_iff₀ (pow_pos htpos 2)).mp hH
  have hMass' : H ≤ C * A := (div_le_iff₀ hA).mp hMass
  have hρbound : ρ < C * A * t ^ 2 :=
    hH'.trans_le (mul_le_mul_of_nonneg_right hMass' (sq_nonneg t))
  have hk : ρ * t ^ 8 / C < t ^ N := by
    apply (div_lt_iff₀ hC).mpr
    calc
      ρ * t ^ 8 < (C * A * t ^ 2) * t ^ 8 :=
        mul_lt_mul_of_pos_right hρbound (pow_pos htpos 8)
      _ = C * (A * (t ^ 2 * t ^ 8)) := by ring
      _ = t ^ N * C := by
        dsimp [A, N]
        rw [← pow_add, ← pow_mul, ← pow_add]
        ring
  have htN : 1 ≤ t ^ N := one_le_pow₀ (by linarith)
  have hsum : 1 + ρ * t ^ 8 / C ≤ t ^ (N + 1) := by
    rw [show t ^ (N + 1) = t ^ N * t from pow_succ t N]
    nlinarith
  have hlog := Real.log_le_log (show 0 < 1 + ρ * t ^ 8 / C by positivity) hsum
  rw [Real.log_pow] at hlog
  have hlogt : Real.log t ≤ p := by
    dsimp [t]
    rw [Real.log_pow]
    have htwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      linarith
    simpa using mul_le_mul_of_nonneg_left htwo (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  have hN : (N + 1 : ℕ) ≤ 12 * r := by dsimp [N]; omega
  calc
    Real.log (1 + ρ * t ^ 8 / C) ≤ ((N + 1 : ℕ) : ℝ) * Real.log t := hlog
    _ ≤ ((N + 1 : ℕ) : ℝ) * p :=
      mul_le_mul_of_nonneg_left hlogt (Nat.cast_nonneg _)
    _ ≤ 12 * (r : ℝ) * p := by
      gcongr
      exact_mod_cast hN

/-- The deterministic amplification's quadratic gain is strictly positive. -/
theorem linear_amplification_gain_pos {t ρ C : ℝ} (ht : 2 ≤ t) (hρ : 0 < ρ)
    (hC : 0 < C) :
    0 < 2 * (ρ * t ^ 8 / C) * (ρ / t ^ 2) * C -
      (ρ * t ^ 8 / C) ^ 2 * C ^ 2 / t ^ 12 - 2 * ρ ^ 2 * t ^ 2 := by
  have htpos : 0 < t := by linarith
  have hident : 2 * (ρ * t ^ 8 / C) * (ρ / t ^ 2) * C -
      (ρ * t ^ 8 / C) ^ 2 * C ^ 2 / t ^ 12 - 2 * ρ ^ 2 * t ^ 2 =
      ρ ^ 2 * t ^ 2 * (2 * (t ^ 2) ^ 2 - t ^ 2 - 2) := by
    field_simp
  rw [hident]
  have ht2 : 4 ≤ t ^ 2 := by nlinarith
  have hpoly : 0 < 2 * (t ^ 2) ^ 2 - t ^ 2 - 2 := by nlinarith
  exact mul_pos (mul_pos (sq_pos_of_pos hρ) (sq_pos_of_pos htpos)) hpoly

end Cliquefree
