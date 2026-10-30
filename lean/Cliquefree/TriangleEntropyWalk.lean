module

public import Cliquefree.TrianglePinsker
public import Cliquefree.TriangleKernels

/-! # Entropy increments along lazy finite walks -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

omit [DecidableEq Ω] in
/-- Jensen's square-root bound for a nonnegative finite observable. -/
theorem FiniteLaw.expectation_sqrt_le (μ : FiniteLaw Ω) {X : Ω → ℝ}
    (hX : ∀ x, 0 ≤ X x) :
    μ.expectation (fun x ↦ Real.sqrt (X x)) ≤ Real.sqrt (μ.expectation X) := by
  apply Real.le_sqrt_of_sq_le
  simpa only [Real.sq_sqrt (hX _)] using μ.sq_expectation_le (fun x ↦ Real.sqrt (X x))

/-- A stationary transition does not change the expectation of a vertex observable. -/
theorem FiniteLaw.expectation_stationary (π : FiniteLaw Ω) {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (hπ : ∀ y, (∑ x, π.mass x * P x y) = π.mass y) (X : Ω → ℝ) :
    π.expectation (fun x ↦ (FiniteLaw.ofStochasticRow P hP x).expectation X) =
      π.expectation X := by
  simp only [FiniteLaw.expectation, FiniteLaw.ofStochasticRow, Finset.mul_sum]
  simp_rw [← mul_assoc]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_mul, hπ]

/-- Adding holding probability preserves every stationary finite law. -/
theorem lazyKernel_stationary (π : FiniteLaw Ω) {P : Matrix Ω Ω ℝ}
    (hπ : ∀ y, (∑ x, π.mass x * P x y) = π.mass y) (y : Ω) :
    (∑ x, π.mass x * lazyKernel P x y) = π.mass y := by
  simp only [lazyKernel, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply]
  calc
    _ = (1 / 2 : ℝ) * ((∑ x, π.mass x * (if x = y then 1 else 0)) +
        ∑ x, π.mass x * P x y) := by
      simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = π.mass y := by simp [hπ]; ring

omit [DecidableEq Ω] in
/-- Finite laws with identical point masses are equal. -/
@[ext] theorem FiniteLaw.ext_mass {μ ν : FiniteLaw Ω} (h : ∀ x, μ.mass x = ν.mass x) :
    μ = ν := by
  cases μ
  cases ν
  congr
  exact funext h

/-- A smoothed transition row as a finite probability law. -/
def smoothedLaw (P : Matrix Ω Ω ℝ) (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (j : ℕ) (x : Ω) : FiniteLaw Ω :=
  FiniteLaw.ofStochasticRow (smoothedKernel P j) (smoothedKernel_stochastic hP j) x

/-- A smoothed row at the next time is the lazy mixture of the current rows. -/
theorem smoothedLaw_succ (P : Matrix Ω Ω ℝ) (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (j : ℕ) (x : Ω) :
    smoothedLaw P hP (j + 1) x =
      (FiniteLaw.ofStochasticRow (lazyKernel P) (lazyKernel_stochastic hP) x).kernelMix
        (smoothedLaw P hP j) := by
  apply FiniteLaw.ext_mass
  intro y
  change smoothedKernel P (j + 1) x y = ∑ z, lazyKernel P x z * smoothedKernel P j z y
  rw [smoothedKernel_succ, Matrix.mul_apply]

/-- Lazy expectation is the average of holding and moving. -/
theorem FiniteLaw.lazy_expectation {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) (x : Ω) (X : Ω → ℝ) :
    (FiniteLaw.ofStochasticRow (lazyKernel P) (lazyKernel_stochastic hP) x).expectation X =
      (X x + (FiniteLaw.ofStochasticRow P hP x).expectation X) / 2 := by
  simp only [FiniteLaw.expectation, FiniteLaw.ofStochasticRow, lazyKernel, Matrix.smul_apply,
    smul_eq_mul, Matrix.add_apply, Matrix.one_apply]
  calc
    _ = ((∑ y, (if x = y then 1 else 0) * X y) + ∑ y, P x y * X y) / 2 := by
      simp only [Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    _ = _ := by simp

/-- Both a held row and every row reached by a positive transition are dominated by the mixture. -/
theorem smoothedLaw_dom {P : Matrix Ω Ω ℝ} (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (j : ℕ) (x z : Ω) (hxz : z = x ∨ 0 < P x z) (y : Ω)
    (hy : 0 < (smoothedLaw P hP j z).mass y) :
    0 < (smoothedLaw P hP (j + 1) x).mass y := by
  rw [smoothedLaw_succ]
  apply FiniteLaw.kernelMix_pos _ _ (z := z) _ hy
  change 0 < lazyKernel P x z
  simp only [lazyKernel, Matrix.smul_apply, smul_eq_mul, Matrix.add_apply, Matrix.one_apply]
  apply mul_pos (by norm_num)
  rcases hxz with rfl | hxz
  · simp only [ite_true]
    linarith [Matrix.nonneg_of_mem_rowStochastic hP (i := z) (j := z)]
  · exact add_pos_of_nonneg_of_pos (by split_ifs <;> norm_num) hxz

/-- Entropy gained when a lazy step mixes the current rows at one starting vertex. -/
def rowEntropyIncrement (P : Matrix Ω Ω ℝ) (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (r : Ω → ℝ) (j : ℕ) (x : Ω) : ℝ :=
  (smoothedLaw P hP (j + 1) x).referenceEntropy r -
    (FiniteLaw.ofStochasticRow (lazyKernel P) (lazyKernel_stochastic hP) x).expectation
      (fun z ↦ (smoothedLaw P hP j z).referenceEntropy r)

/-- The row entropy increment is exactly its average relative entropy to the mixture. -/
theorem rowEntropyIncrement_eq_kl {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) {r : Ω → ℝ} (hr : ∀ y, 0 < r y)
    (j : ℕ) (x : Ω) :
    rowEntropyIncrement P hP r j x =
      (FiniteLaw.ofStochasticRow (lazyKernel P) (lazyKernel_stochastic hP) x).expectation
        (fun z ↦ (smoothedLaw P hP j z).relativeEntropy (smoothedLaw P hP (j + 1) x)) := by
  unfold rowEntropyIncrement
  rw [smoothedLaw_succ]
  exact FiniteLaw.referenceEntropy_increment _ _ hr

/-- Mixing rows can only increase their average reference entropy. -/
theorem rowEntropyIncrement_nonneg {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) {r : Ω → ℝ} (hr : ∀ y, 0 < r y)
    (j : ℕ) (x : Ω) : 0 ≤ rowEntropyIncrement P hP r j x := by
  unfold rowEntropyIncrement
  rw [sub_nonneg, smoothedLaw_succ]
  exact FiniteLaw.referenceEntropy_kernelMix_ge _ _ hr

/-- Nearby current rows are close on average when the local lazy entropy increment is small. -/
theorem smoothedLaw_nearby_row {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) {r : Ω → ℝ} (hr : ∀ y, 0 < r y)
    (j : ℕ) (x : Ω) :
    (FiniteLaw.ofStochasticRow P hP x).expectation
      (fun z ↦ (smoothedLaw P hP j x).totalVariation (smoothedLaw P hP j z)) ≤
      2 * Real.sqrt (rowEntropyIncrement P hP r j x) := by
  let μ := FiniteLaw.ofStochasticRow P hP x
  let R := smoothedLaw P hP (j + 1) x
  have hhold : ∀ y, 0 < (smoothedLaw P hP j x).mass y → 0 < R.mass y :=
    smoothedLaw_dom hP j x x (Or.inl rfl)
  have hmove : ∀ z, 0 < μ.mass z →
      ∀ y, 0 < (smoothedLaw P hP j z).mass y → 0 < R.mass y := by
    intro z hz
    exact smoothedLaw_dom hP j x z (Or.inr hz)
  have hh := (smoothedLaw P hP j x).relativeEntropy_nonneg R hhold
  have hm : 0 ≤ μ.expectation (fun z ↦ (smoothedLaw P hP j z).relativeEntropy R) := by
    have h := μ.expectation_mono_support (X := fun _ ↦ 0)
      (fun z hz ↦ (smoothedLaw P hP j z).relativeEntropy_nonneg R (hmove z hz))
    simpa using h
  have hi := rowEntropyIncrement_eq_kl hP hr j x
  rw [FiniteLaw.lazy_expectation] at hi
  change rowEntropyIncrement P hP r j x =
    ((smoothedLaw P hP j x).relativeEntropy R +
      μ.expectation (fun z ↦ (smoothedLaw P hP j z).relativeEntropy R)) / 2 at hi
  apply μ.nearby_rows_of_entropy_bounds (fun _ ↦ smoothedLaw P hP j x)
    (smoothedLaw P hP j) (fun _ ↦ R)
  · intro z _
    exact hhold
  · exact hmove
  · rw [μ.expectation_const]
    linarith only [hi, hm]
  · linarith only [hi, hh]

/-- Reference entropy of smoothed rows averaged against a vertex law. -/
def averagedReferenceEntropy (π : FiniteLaw Ω) (P : Matrix Ω Ω ℝ)
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) (r : Ω → ℝ) (j : ℕ) : ℝ :=
  π.expectation (fun x ↦ (smoothedLaw P hP j x).referenceEntropy r)

/-- Stationarity turns the average local mixing increment into the entropy time difference. -/
theorem averagedReferenceEntropy_increment (π : FiniteLaw Ω) {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (hπ : ∀ y, (∑ x, π.mass x * P x y) = π.mass y) (r : Ω → ℝ) (j : ℕ) :
    averagedReferenceEntropy π P hP r (j + 1) - averagedReferenceEntropy π P hP r j =
      π.expectation (rowEntropyIncrement P hP r j) := by
  unfold rowEntropyIncrement
  rw [π.expectation_sub,
    π.expectation_stationary (lazyKernel_stochastic hP) (lazyKernel_stationary π hπ)]
  rfl

/-- Stationary mean reference entropy is nondecreasing under lazy smoothing. -/
theorem averagedReferenceEntropy_monotone (π : FiniteLaw Ω) {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (hπ : ∀ y, (∑ x, π.mass x * P x y) = π.mass y)
    {r : Ω → ℝ} (hr : ∀ y, 0 < r y) : Monotone (averagedReferenceEntropy π P hP r) := by
  apply monotone_nat_of_le_succ
  intro j
  apply sub_nonneg.mp
  rw [averagedReferenceEntropy_increment π hP hπ]
  exact π.expectation_nonneg (rowEntropyIncrement_nonneg hP hr j)

/-- Nearby smoothed rows are close when the stationary mean entropy increment is small. -/
theorem averagedReferenceEntropy_nearby (π : FiniteLaw Ω) {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (hπ : ∀ y, (∑ x, π.mass x * P x y) = π.mass y)
    {r : Ω → ℝ} (hr : ∀ y, 0 < r y) (j : ℕ) :
    π.expectation (fun x ↦ (FiniteLaw.ofStochasticRow P hP x).expectation
      (fun z ↦ (smoothedLaw P hP j x).totalVariation (smoothedLaw P hP j z))) ≤
      2 * Real.sqrt (averagedReferenceEntropy π P hP r (j + 1) -
        averagedReferenceEntropy π P hP r j) := by
  rw [averagedReferenceEntropy_increment π hP hπ]
  calc
    _ ≤ π.expectation (fun x ↦ 2 * Real.sqrt (rowEntropyIncrement P hP r j x)) :=
      π.expectation_mono_support (fun x _ ↦ smoothedLaw_nearby_row hP hr j x)
    _ = 2 * π.expectation (fun x ↦ Real.sqrt (rowEntropyIncrement P hP r j x)) :=
      π.expectation_smul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (π.expectation_sqrt_le (rowEntropyIncrement_nonneg hP hr j)) (by norm_num)

/-- Telescoping entropy differences gives an index no larger than the mean increment. -/
theorem exists_small_entropy_increment {H : ℕ → ℝ} {t : ℕ} (ht : 0 < t)
    {D : ℝ} (hD : H t - H 0 ≤ D) : ∃ j < t, H (j + 1) - H j ≤ D / t := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  have hsum : (∑ j ∈ Finset.range t, (H (j + 1) - H j)) ≤
      ∑ _j ∈ Finset.range t, D / t := by
    rw [Finset.sum_range_sub]
    convert hD using 1
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  obtain ⟨j, hj, hle⟩ := Finset.exists_le_of_sum_le
    (Finset.nonempty_range_iff.mpr ht.ne') hsum
  exact ⟨j, Finset.mem_range.mp hj, hle⟩

variable {I : Type*} [Fintype I] {E : I → Type*}
  [∀ i, Fintype (E i)] [∀ i, DecidableEq (E i)]

/-- Mean entropy for a family of finite walks, allowing a different state space at each center. -/
def familyReferenceEntropy (μ : FiniteLaw I) (π : ∀ i, FiniteLaw (E i))
    (P : ∀ i, Matrix (E i) (E i) ℝ)
    (hP : ∀ i, P i ∈ Matrix.rowStochastic ℝ (E i)) (r : ∀ i, E i → ℝ) (j : ℕ) : ℝ :=
  μ.expectation (fun i ↦ averagedReferenceEntropy (π i) (P i) (hP i) (r i) j)

/-- Mean variation of neighboring rows, first sampling a center and then a stationary transition. -/
def familyNearbyVariation (μ : FiniteLaw I) (π : ∀ i, FiniteLaw (E i))
    (P : ∀ i, Matrix (E i) (E i) ℝ)
    (hP : ∀ i, P i ∈ Matrix.rowStochastic ℝ (E i)) (j : ℕ) : ℝ :=
  μ.expectation (fun i ↦ (π i).expectation
    (fun x ↦ (FiniteLaw.ofStochasticRow (P i) (hP i) x).expectation
      (fun z ↦ (smoothedLaw (P i) (hP i) j x).totalVariation
        (smoothedLaw (P i) (hP i) j z))))

/-- Averaging over centers preserves the nearby-row entropy estimate. -/
theorem familyReferenceEntropy_nearby (μ : FiniteLaw I) (π : ∀ i, FiniteLaw (E i))
    (P : ∀ i, Matrix (E i) (E i) ℝ)
    (hP : ∀ i, P i ∈ Matrix.rowStochastic ℝ (E i))
    (hπ : ∀ i y, (∑ x, (π i).mass x * P i x y) = (π i).mass y)
    {r : ∀ i, E i → ℝ} (hr : ∀ i y, 0 < r i y) (j : ℕ) :
    familyNearbyVariation μ π P hP j ≤
      2 * Real.sqrt (familyReferenceEntropy μ π P hP r (j + 1) -
        familyReferenceEntropy μ π P hP r j) := by
  let Δ : I → ℝ := fun i ↦ averagedReferenceEntropy (π i) (P i) (hP i) (r i) (j + 1) -
    averagedReferenceEntropy (π i) (P i) (hP i) (r i) j
  have hΔ (i : I) : 0 ≤ Δ i := by
    apply sub_nonneg.mpr
    exact averagedReferenceEntropy_monotone (π i) (hP i) (hπ i) (hr i) (by omega)
  calc
    _ ≤ μ.expectation (fun i ↦ 2 * Real.sqrt (Δ i)) :=
      μ.expectation_mono_support (fun i _ ↦
        averagedReferenceEntropy_nearby (π i) (hP i) (hπ i) (hr i) j)
    _ = 2 * μ.expectation (fun i ↦ Real.sqrt (Δ i)) := μ.expectation_smul _ _
    _ ≤ 2 * Real.sqrt (μ.expectation Δ) :=
      mul_le_mul_of_nonneg_left (μ.expectation_sqrt_le hΔ) (by norm_num)
    _ = _ := by rw [show μ.expectation Δ = _ from μ.expectation_sub _ _]; rfl

/-- An entropy budget gives one common good time for all centers in the finite family. -/
theorem exists_nearby_smoothed_rows (μ : FiniteLaw I) (π : ∀ i, FiniteLaw (E i))
    (P : ∀ i, Matrix (E i) (E i) ℝ)
    (hP : ∀ i, P i ∈ Matrix.rowStochastic ℝ (E i))
    (hπ : ∀ i y, (∑ x, (π i).mass x * P i x y) = (π i).mass y)
    {r : ∀ i, E i → ℝ} (hr : ∀ i y, 0 < r i y) {t : ℕ} (ht : 0 < t)
    {D : ℝ} (hD : familyReferenceEntropy μ π P hP r t -
      familyReferenceEntropy μ π P hP r 0 ≤ D) :
    ∃ j < t, familyNearbyVariation μ π P hP j ≤ 2 * Real.sqrt (D / t) := by
  obtain ⟨j, hj, hle⟩ := exists_small_entropy_increment ht hD
  refine ⟨j, hj, (familyReferenceEntropy_nearby μ π P hP hπ hr j).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hle) (by norm_num)

end Cliquefree
