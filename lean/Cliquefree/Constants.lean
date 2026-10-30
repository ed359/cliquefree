module

public import Mathlib

/-!
# Constants in the clique-free independence bound

These absolute constants fix the witness bounds and cutoff in the triangle dichotomy.
`LinearConstants` supplies the inverse-linear coefficient in the existence theorem.
-/

@[expose] public section

namespace Cliquefree

/-- The absolute witness constant $C_*=24$. -/
def witnessC : ℕ := 24

/-- The absolute entropy coefficient $A_*=20+12C_*^2$. -/
def witnessA : ℕ := 20 + 12 * witnessC ^ 2

/-- The absolute triangle-loss coefficient $a_*=24(A_*+1)$. -/
def witnessa : ℕ := 24 * (witnessA + 1)

/-- The fixed exponent $X=(100a_*)^4$ in the triangle dichotomy. -/
def witnessExponent : ℕ := (100 * witnessa) ^ 4

/-- The rational absolute triangle constant $B_0=2^X$. -/
def triangleBoundConstant : ℚ := 2 ^ witnessExponent

/-- The absolute exponent is at least three. -/
theorem witnessExponent_ge_three : 3 ≤ witnessExponent := by
  norm_num [witnessExponent, witnessa, witnessA, witnessC]

/-- The triangle constant is at least eight. -/
theorem triangleBoundConstant_ge_eight : 8 ≤ triangleBoundConstant := by
  have h := pow_le_pow_right₀ (show (1 : ℚ) ≤ 2 by norm_num) witnessExponent_ge_three
  norm_num only [show (2 : ℚ) ^ 3 = 8 by norm_num] at h
  exact h

/-- The triangle constant is strictly positive. -/
theorem triangleBoundConstant_pos : 0 < triangleBoundConstant := by
  linarith [triangleBoundConstant_ge_eight]


end Cliquefree
