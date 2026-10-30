module

public import Cliquefree.Constants

/-!
# Constants with linear dependence on the excluded clique order

The neighborhood restriction argument permits the scale `linearCliqueScale r = 24 * r`.
Its existence coefficient is consequently of order `1 / r`.
-/

@[expose] public section

namespace Cliquefree

/-- The scale coefficient $K=24r$. -/
def linearCliqueScale (r : ℕ) : ℚ := 24 * (r : ℚ)

/-- The rational existence coefficient $c_r=1/(1+48B_0K)$. -/
def linearExistenceConstant (r : ℕ) : ℚ :=
  1 / (1 + 48 * triangleBoundConstant * linearCliqueScale r)

/-- The scale is nonnegative for every clique order. -/
theorem linearCliqueScale_nonneg (r : ℕ) : 0 ≤ linearCliqueScale r := by
  unfold linearCliqueScale
  positivity

/-- The scale is positive for positive clique orders. -/
theorem linearCliqueScale_pos {r : ℕ} (hr : 1 ≤ r) : 0 < linearCliqueScale r := by
  have hr' : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  unfold linearCliqueScale
  positivity

/-- The defining denominator is positive. -/
theorem linearExistenceConstant_denominator_pos (r : ℕ) :
    0 < 1 + 48 * triangleBoundConstant * linearCliqueScale r := by
  have hB := triangleBoundConstant_pos
  have hK := linearCliqueScale_nonneg r
  positivity

/-- The existence coefficient is positive. -/
theorem linearExistenceConstant_pos (r : ℕ) : 0 < linearExistenceConstant r := by
  exact one_div_pos.mpr (linearExistenceConstant_denominator_pos r)

/-- The existence coefficient is at most one. -/
theorem linearExistenceConstant_le_one (r : ℕ) : linearExistenceConstant r ≤ 1 := by
  apply (div_le_one (linearExistenceConstant_denominator_pos r)).mpr
  have h := mul_nonneg (le_of_lt triangleBoundConstant_pos) (linearCliqueScale_nonneg r)
  linarith

/-- Expanding the scale exhibits the linear denominator. -/
theorem linearExistenceConstant_formula (r : ℕ) :
    linearExistenceConstant r = 1 / (1 + 1152 * triangleBoundConstant * (r : ℚ)) := by
  unfold linearExistenceConstant linearCliqueScale
  congr 1
  ring

/-- The denominator identity supplies the slack in the existence deletion argument. -/
theorem linearExistenceConstant_balance (r : ℕ) :
    linearExistenceConstant r +
      48 * linearExistenceConstant r * triangleBoundConstant * linearCliqueScale r = 1 := by
  have h := div_mul_cancel₀ (1 : ℚ) (ne_of_gt (linearExistenceConstant_denominator_pos r))
  change linearExistenceConstant r * (1 + 48 * triangleBoundConstant * linearCliqueScale r) = 1
    at h
  nlinarith only [h]

/-- The coefficient of the objective mass in the existence argument is nonnegative. -/
theorem linearExistenceConstant_existence_slack (r : ℕ) :
    0 ≤ 1 - linearExistenceConstant r -
      6 * linearExistenceConstant r * triangleBoundConstant * linearCliqueScale r := by
  have hc := linearExistenceConstant_le_one r
  nlinarith only [hc, linearExistenceConstant_balance r]

/-- An explicit inverse-linear lower bound for the existence coefficient. -/
theorem linearExistenceConstant_inverse_lower {r : ℕ} (hr : 1 ≤ r) :
    1 / ((1 + 1152 * triangleBoundConstant) * (r : ℚ)) ≤
      linearExistenceConstant r := by
  rw [linearExistenceConstant_formula]
  have hr' : (1 : ℚ) ≤ r := by exact_mod_cast hr
  have hB := triangleBoundConstant_pos
  have hden : 0 < 1 + 1152 * triangleBoundConstant * (r : ℚ) :=
    add_pos_of_pos_of_nonneg (by norm_num)
      (mul_nonneg (mul_nonneg (by norm_num) hB.le) (Nat.cast_nonneg r))
  apply one_div_le_one_div_of_le hden
  nlinarith only [hr']

/-- An explicit inverse-linear upper bound for the existence coefficient. -/
theorem linearExistenceConstant_inverse_upper {r : ℕ} (hr : 1 ≤ r) :
    linearExistenceConstant r ≤ 1 / (1152 * triangleBoundConstant * (r : ℚ)) := by
  rw [linearExistenceConstant_formula]
  have hr' : (0 : ℚ) < r := by exact_mod_cast (Nat.zero_lt_of_lt hr)
  have hden : 0 < 1152 * triangleBoundConstant * (r : ℚ) :=
    mul_pos (mul_pos (by norm_num) triangleBoundConstant_pos) hr'
  apply one_div_le_one_div_of_le hden
  linarith

/-- The real existence coefficient is at most one. -/
theorem linearExistenceConstant_real_le_one (r : ℕ) :
    (linearExistenceConstant r : ℝ) ≤ 1 := by
  exact_mod_cast linearExistenceConstant_le_one r

/-- Real form of the nonnegative slack at a potential maximizer. -/
theorem linearExistenceConstant_real_existence_slack (r : ℕ) :
    0 ≤ 1 - (linearExistenceConstant r : ℝ) -
      6 * (linearExistenceConstant r : ℝ) * triangleBoundConstant * linearCliqueScale r := by
  exact_mod_cast linearExistenceConstant_existence_slack r

/-- Explicit real bounds certifying inverse-linear dependence on the clique order. -/
theorem linearExistenceConstant_real_inverse_bounds {r : ℕ} (hr : 4 ≤ r) :
    1 / ((1 + 1152 * (triangleBoundConstant : ℝ)) * (r : ℝ)) ≤
      (linearExistenceConstant r : ℝ) ∧
    (linearExistenceConstant r : ℝ) ≤
      1 / (1152 * (triangleBoundConstant : ℝ) * (r : ℝ)) := by
  have hr' : 1 ≤ r := by omega
  constructor
  · exact_mod_cast linearExistenceConstant_inverse_lower hr'
  · exact_mod_cast linearExistenceConstant_inverse_upper hr'

/-- Positive absolute constants bound the existence coefficient above and below by $1/r$. -/
theorem linearExistenceConstant_order_inverse :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ ∀ r : ℕ, 4 ≤ r →
      a / (r : ℝ) ≤ (linearExistenceConstant r : ℝ) ∧
      (linearExistenceConstant r : ℝ) ≤ b / (r : ℝ) := by
  have hB : 0 < (triangleBoundConstant : ℝ) := by exact_mod_cast triangleBoundConstant_pos
  refine ⟨1 / (1 + 1152 * (triangleBoundConstant : ℝ)),
    1 / (1152 * (triangleBoundConstant : ℝ)), ?_, ?_, ?_⟩
  · exact one_div_pos.mpr (add_pos (by norm_num) (mul_pos (by norm_num) hB))
  · exact one_div_pos.mpr (mul_pos (by norm_num) hB)
  · intro r hr
    simpa only [div_div] using linearExistenceConstant_real_inverse_bounds hr

end Cliquefree
