module

public import Cliquefree.FiniteLaw

/-!
# Lazy finite kernels

Stochastic matrix powers encode one local step followed by lazy steps. Their row laws,
uniform density bounds, and reversibility give the triangle entropy estimates.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The transition matrix of a family of finite row laws. -/
def lawKernel (P : Ω → FiniteLaw Ω) : Matrix Ω Ω ℝ := fun x y ↦ (P x).mass y

/-- A family of finite row laws gives a row-stochastic transition matrix. -/
theorem lawKernel_stochastic (P : Ω → FiniteLaw Ω) :
    lawKernel P ∈ Matrix.rowStochastic ℝ Ω :=
  Matrix.mem_rowStochastic_iff_sum.mpr ⟨fun x y ↦ (P x).nonneg y, fun x ↦ (P x).sum_mass⟩

/-- A row of a row-stochastic matrix is a finite probability law. -/
def FiniteLaw.ofStochasticRow (P : Matrix Ω Ω ℝ) (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (x : Ω) : FiniteLaw Ω where
  mass y := P x y
  nonneg _ := Matrix.nonneg_of_mem_rowStochastic hP
  sum_mass := Matrix.sum_row_of_mem_rowStochastic hP x

/-- The lazy kernel holds with probability one half and otherwise takes a kernel step. -/
def lazyKernel (P : Matrix Ω Ω ℝ) : Matrix Ω Ω ℝ := (1 / 2 : ℝ) • (1 + P)

/-- Laziness preserves row stochasticity. -/
theorem lazyKernel_stochastic {P : Matrix Ω Ω ℝ} (hP : P ∈ Matrix.rowStochastic ℝ Ω) :
    lazyKernel P ∈ Matrix.rowStochastic ℝ Ω := by
  apply Matrix.mem_rowStochastic_iff_sum.mpr
  constructor
  · intro x y
    simp only [lazyKernel, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply]
    apply mul_nonneg (by norm_num)
    exact add_nonneg (by split_ifs <;> norm_num) (Matrix.nonneg_of_mem_rowStochastic hP)
  · intro x
    simp only [lazyKernel, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
      Matrix.one_apply, ← Finset.mul_sum, Finset.sum_add_distrib]
    rw [Matrix.sum_row_of_mem_rowStochastic hP]
    norm_num

/-- A transition kernel commutes with its lazy version. -/
theorem commute_lazyKernel (P : Matrix Ω Ω ℝ) : Commute P (lazyKernel P) := by
  change P * lazyKernel P = lazyKernel P * P
  simp only [lazyKernel, Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul,
    mul_one, one_mul]

/-- One genuine transition followed by `j` lazy steps. -/
def smoothedKernel (P : Matrix Ω Ω ℝ) (j : ℕ) : Matrix Ω Ω ℝ := P * lazyKernel P ^ j

/-- Every smoothed kernel is row stochastic. -/
theorem smoothedKernel_stochastic {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) (j : ℕ) :
    smoothedKernel P j ∈ Matrix.rowStochastic ℝ Ω :=
  (Matrix.rowStochastic ℝ Ω).mul_mem hP
    ((Matrix.rowStochastic ℝ Ω).pow_mem (lazyKernel_stochastic hP) j)

/-- The next smoothed row is the mixture of current rows prescribed by the lazy kernel. -/
theorem smoothedKernel_succ (P : Matrix Ω Ω ℝ) (j : ℕ) :
    smoothedKernel P (j + 1) = lazyKernel P * smoothedKernel P j := by
  unfold smoothedKernel
  rw [pow_succ', ← mul_assoc, (commute_lazyKernel P).eq, mul_assoc]

/-- Uniform column-density bounds survive every number of lazy smoothing steps. -/
theorem smoothedKernel_density_le {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) {M : Ω → ℝ}
    (hM : ∀ x y, P x y ≤ M y) (j : ℕ) (x y : Ω) : smoothedKernel P j x y ≤ M y := by
  have hQ := (Matrix.rowStochastic ℝ Ω).pow_mem (lazyKernel_stochastic hP) j
  rw [smoothedKernel, ((commute_lazyKernel P).pow_right j).eq, Matrix.mul_apply]
  calc
    _ ≤ ∑ z, (lazyKernel P ^ j) x z * M y := by
      apply Finset.sum_le_sum
      intro z _
      exact mul_le_mul_of_nonneg_left (hM z y) (Matrix.nonneg_of_mem_rowStochastic hQ)
    _ = M y := by rw [← Finset.sum_mul, Matrix.sum_row_of_mem_rowStochastic hQ, one_mul]

/-- Detailed balance for a finite transition matrix and reference vertex masses. -/
def KernelReversible (π : Ω → ℝ) (P : Matrix Ω Ω ℝ) : Prop :=
  ∀ x y, π x * P x y = π y * P y x

omit [DecidableEq Ω] in
/-- Reversing a product of reversible kernels reverses the order of its factors. -/
theorem KernelReversible.product_reverse {π : Ω → ℝ} {P Q : Matrix Ω Ω ℝ}
    (hP : KernelReversible π P) (hQ : KernelReversible π Q) (x y : Ω) :
    π x * (P * Q) x y = π y * (Q * P) y x := by
  simp only [Matrix.mul_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  calc
    π x * (P x z * Q z y) = (π x * P x z) * Q z y := by ring
    _ = (π z * P z x) * Q z y := by rw [hP x z]
    _ = (π z * Q z y) * P z x := by ring
    _ = (π y * Q y z) * P z x := by rw [hQ z y]
    _ = π y * (Q y z * P z x) := by ring

omit [DecidableEq Ω] in
/-- Commuting reversible kernels have a reversible product. -/
theorem KernelReversible.mul {π : Ω → ℝ} {P Q : Matrix Ω Ω ℝ}
    (hP : KernelReversible π P) (hQ : KernelReversible π Q) (hPQ : Commute P Q) :
    KernelReversible π (P * Q) := by
  intro x y
  rw [hP.product_reverse hQ x y, hPQ.eq]

/-- Every natural power of a reversible kernel is reversible with the same masses. -/
theorem KernelReversible.pow {π : Ω → ℝ} {P : Matrix Ω Ω ℝ}
    (hP : KernelReversible π P) (j : ℕ) : KernelReversible π (P ^ j) := by
  induction j with
  | zero =>
    intro x y
    by_cases hxy : x = y
    · subst y
      rfl
    · simp [hxy, Ne.symm hxy]
  | succ j ih =>
    rw [pow_succ]
    exact ih.mul hP ((Commute.refl P).pow_left j)

omit [Fintype Ω] in
/-- Adding holding probability preserves detailed balance. -/
theorem KernelReversible.lazyKernel {π : Ω → ℝ} {P : Matrix Ω Ω ℝ}
    (hP : KernelReversible π P) : KernelReversible π (lazyKernel P) := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  · simp only [Cliquefree.lazyKernel, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply,
      Matrix.one_apply, hxy, Ne.symm hxy, ite_false, zero_add]
    nlinarith [hP x y]

/-- One transition followed by any number of lazy steps remains reversible. -/
theorem KernelReversible.smoothedKernel {π : Ω → ℝ} {P : Matrix Ω Ω ℝ}
    (hP : KernelReversible π P) (j : ℕ) : KernelReversible π (smoothedKernel P j) :=
  hP.mul (hP.lazyKernel.pow j) ((commute_lazyKernel P).pow_right j)

end Cliquefree
