module

public import Cliquefree.TriangleEntropyWalk
public import Cliquefree.TriangleClosureBounds
public import Cliquefree.TriangleWalks

/-! # Leakage of local triangle walks outside the growing closure -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The probability mass outside a finite set. -/
def FiniteLaw.outsideMass (μ : FiniteLaw Ω) (A : Finset Ω) : ℝ :=
  ∑ y ∈ Aᶜ, μ.mass y

/-- Probability outside a set is the expectation of its complement indicator. -/
theorem FiniteLaw.outsideMass_eq_expectation (μ : FiniteLaw Ω) (A : Finset Ω) :
    μ.outsideMass A = μ.expectation (fun y ↦ if y ∈ A then 0 else 1) := by
  simp only [outsideMass, expectation, mul_ite, mul_zero, mul_one]
  rw [← Finset.sum_ite_mem_eq Aᶜ μ.mass]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y ∈ A <;> simp [hy]

/-- A probability of leaving a set is at most one. -/
theorem FiniteLaw.outsideMass_le_one (μ : FiniteLaw Ω) (A : Finset Ω) :
    μ.outsideMass A ≤ 1 := by
  rw [outsideMass, ← μ.sum_mass]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun y _ _ ↦ μ.nonneg y)

/-- Leakage from a mixture is the mean leakage from its rows. -/
theorem FiniteLaw.outsideMass_kernelMix (μ : FiniteLaw Ω) (K : Ω → FiniteLaw Ω)
    (A : Finset Ω) :
    (μ.kernelMix K).outsideMass A = μ.expectation (fun z ↦ (K z).outsideMass A) := by
  simp only [outsideMass, kernelMix, expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- From within the target set, holding only reduces leakage. -/
theorem FiniteLaw.outsideMass_lazy_le {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) (A : Finset Ω) {x : Ω} (hx : x ∈ A) :
    (FiniteLaw.ofStochasticRow (lazyKernel P) (lazyKernel_stochastic hP) x).outsideMass A ≤
      (FiniteLaw.ofStochasticRow P hP x).outsideMass A := by
  rw [outsideMass_eq_expectation, lazy_expectation hP x, ite_eq_left hx, zero_add,
    ← outsideMass_eq_expectation]
  have hn : 0 ≤ (FiniteLaw.ofStochasticRow P hP x).outsideMass A :=
    Finset.sum_nonneg (fun y _ ↦ (FiniteLaw.ofStochasticRow P hP x).nonneg y)
  linarith only [hn]

/-- Old leakage plus transitions from the previous set bounds leakage after a lazy step. -/
theorem FiniteLaw.outsideMass_lazy_kernelMix_le (μ : FiniteLaw Ω) {P : Matrix Ω Ω ℝ}
    (hP : P ∈ Matrix.rowStochastic ℝ Ω) {A B : Finset Ω} (hAB : A ⊆ B) :
    (μ.kernelMix (FiniteLaw.ofStochasticRow (lazyKernel P)
      (lazyKernel_stochastic hP))).outsideMass B ≤
      μ.outsideMass A +
        ∑ z ∈ A, μ.mass z * (FiniteLaw.ofStochasticRow P hP z).outsideMass B := by
  rw [outsideMass_kernelMix]
  calc
    _ ≤ μ.expectation (fun z ↦ if z ∈ A then
        (FiniteLaw.ofStochasticRow P hP z).outsideMass B else 1) := by
      apply μ.expectation_mono_support
      intro z _
      by_cases hz : z ∈ A
      · simp only [hz, ite_true]
        exact outsideMass_lazy_le hP B (hAB hz)
      · simp only [hz, ite_false]
        exact outsideMass_le_one _ _
    _ = _ := by
      rw [outsideMass_eq_expectation]
      simp only [expectation, mul_ite, mul_zero, mul_one]
      rw [← Finset.sum_ite_mem_eq A
        (fun z ↦ μ.mass z * (FiniteLaw.ofStochasticRow P hP z).outsideMass B)]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      by_cases hz : z ∈ A <;> simp [hz]

/-- Smoothing can equivalently append a lazy step after the current walk. -/
theorem smoothedLaw_succ_right (P : Matrix Ω Ω ℝ) (hP : P ∈ Matrix.rowStochastic ℝ Ω)
    (j : ℕ) (x : Ω) :
    smoothedLaw P hP (j + 1) x = (smoothedLaw P hP j x).kernelMix
      (FiniteLaw.ofStochasticRow (lazyKernel P) (lazyKernel_stochastic hP)) := by
  apply FiniteLaw.ext_mass
  intro y
  change (P * lazyKernel P ^ (j + 1)) x y =
    ∑ z, (P * lazyKernel P ^ j) x z * lazyKernel P z y
  rw [pow_succ, ← mul_assoc, Matrix.mul_apply]

variable {V : Type*} [Fintype V]

/-- Vertices of a set that belong to a fixed neighborhood, indexed by that neighborhood. -/
def neighborSlice (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) (A : Finset V) :
    Finset (G.neighborFinset x) := by
  classical
  exact Finset.univ.filter (fun z ↦ (z : V) ∈ A)

/-- Membership in a neighborhood slice is membership in the original target set. -/
@[simp] theorem mem_neighborSlice (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (A : Finset V) (z : G.neighborFinset x) : z ∈ neighborSlice G x A ↔ (z : V) ∈ A := by
  classical
  simp [neighborSlice]

/-- Summing on a neighborhood slice inserts only the corresponding adjacency indicator. -/
theorem sum_neighborSlice (G : SimpleGraph V) [DecidableRel G.Adj] (x : V)
    (A : Finset V) (f : V → ℝ) :
    (∑ z ∈ neighborSlice G x A, f z) = ∑ z ∈ A, if G.Adj x z then f z else 0 := by
  classical
  simp only [neighborSlice, Finset.sum_filter]
  rw [Finset.sum_coe_sort (G.neighborFinset x) (fun z ↦ if z ∈ A then f z else 0)]
  rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  rw [← Finset.sum_ite_mem_eq A (fun z ↦ if G.Adj x z then f z else 0)]
  apply Finset.sum_congr rfl
  intro z _
  by_cases h₁ : G.Adj x z <;> by_cases h₂ : z ∈ A <;> simp [h₁, h₂]

/-- Density and common-neighbor bounds control newly arriving mass through a source set. -/
theorem triangleWalk_incoming_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (x : V)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    {θ t : ℝ} (hθ : 0 < θ) (ht : 0 < t)
    (hCt : ∀ v, G.Adj x v → θ / t ≤ commonNeighborhoodMass G w x v)
    (μ : FiniteLaw (G.neighborFinset x)) (hd : ∀ z, μ.mass z ≤ t * w z / θ)
    (A : Finset V) (y : G.neighborFinset x) :
    (∑ z ∈ neighborSlice G x A, μ.mass z * (triangleWalk G w hw x hC z).mass y) ≤
      (t ^ 2 * w y / θ ^ 2) * neighborhoodMassOn G w A y := by
  classical
  have hc : 0 ≤ t ^ 2 * w y / θ ^ 2 :=
    div_nonneg (mul_nonneg (sq_nonneg t) (hw y)) (sq_nonneg θ)
  calc
    _ ≤ ∑ z ∈ neighborSlice G x A,
        (t ^ 2 * w y / θ ^ 2) * (if G.Adj y z then w z else 0) := by
      apply Finset.sum_le_sum
      intro z _
      by_cases hzy : G.Adj z y
      · rw [ite_eq_left hzy.symm]
        calc
          _ ≤ (t * w z / θ) * (t * w y / θ) :=
            mul_le_mul (hd z) (triangleWalk_density_le G w hw x hC hθ ht hCt z y)
              ((triangleWalk G w hw x hC z).nonneg y)
              (div_nonneg (mul_nonneg ht.le (hw z)) hθ.le)
          _ = _ := by ring
      · have hyz : ¬G.Adj y z := fun h ↦ hzy h.symm
        simp [triangleWalk, hzy, hyz]
    _ = (t ^ 2 * w y / θ ^ 2) *
        ∑ z ∈ neighborSlice G x A, if G.Adj y z then w z else 0 := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hc
      rw [sum_neighborSlice G x A (fun z ↦ if G.Adj y z then w z else 0)]
      apply Finset.sum_le_sum
      intro z _
      by_cases hxz : G.Adj x z <;> by_cases hyz : G.Adj y z <;> simp [hxz, hyz, hw z]

/-- One lazy triangle-walk step leaks at most the old mass plus a uniform threshold term. -/
theorem triangleWalk_leakage_step_le [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (hw : ∀ v, 0 ≤ w v) (x : V)
    (hC : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    {θ t a : ℝ} (hθ : 0 < θ) (ht : 0 < t) (ha : 0 ≤ a)
    (hCt : ∀ v, G.Adj x v → θ / t ≤ commonNeighborhoodMass G w x v)
    (μ : FiniteLaw (G.neighborFinset x)) (hd : ∀ z, μ.mass z ≤ t * w z / θ)
    {A B : Finset V} (hAB : A ⊆ B)
    (hB : ∀ y, y ∉ B → neighborhoodMassOn G w A y ≤ a) :
    (μ.kernelMix (FiniteLaw.ofStochasticRow (lazyKernel (lawKernel
      (triangleWalk G w hw x hC))) (lazyKernel_stochastic
        (lawKernel_stochastic (triangleWalk G w hw x hC))))).outsideMass
          (neighborSlice G x B) ≤
      μ.outsideMass (neighborSlice G x A) +
        (t ^ 2 * a / θ ^ 2) * neighborhoodMass G w x := by
  classical
  let P := lawKernel (triangleWalk G w hw x hC)
  have hP := lawKernel_stochastic (triangleWalk G w hw x hC)
  have hs : neighborSlice G x A ⊆ neighborSlice G x B := by
    intro z hz
    exact (mem_neighborSlice G x B z).mpr (hAB ((mem_neighborSlice G x A z).mp hz))
  apply (μ.outsideMass_lazy_kernelMix_le hP hs).trans
  apply add_le_add le_rfl
  change (∑ z ∈ neighborSlice G x A, μ.mass z *
    ∑ y ∈ (neighborSlice G x B)ᶜ, (triangleWalk G w hw x hC z).mass y) ≤ _
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ y ∈ (neighborSlice G x B)ᶜ, (t ^ 2 * w y / θ ^ 2) * a := by
      apply Finset.sum_le_sum
      intro y hy
      apply (triangleWalk_incoming_le G w hw x hC hθ ht hCt μ hd A y).trans
      apply mul_le_mul_of_nonneg_left
        (hB y (by simpa only [Finset.mem_compl, mem_neighborSlice] using hy))
      exact div_nonneg (mul_nonneg (sq_nonneg t) (hw y)) (sq_nonneg θ)
    _ ≤ ∑ y : G.neighborFinset x, (t ^ 2 * w y / θ ^ 2) * a :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun y _ _ ↦ mul_nonneg
          (div_nonneg (mul_nonneg (sq_nonneg t) (hw y)) (sq_nonneg θ)) ha)
    _ = _ := by
      rw [Finset.sum_coe_sort (G.neighborFinset x)
        (fun y ↦ (t ^ 2 * w y / θ ^ 2) * a)]
      rw [neighborhoodMass_eq_sum_neighborFinset, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring

/-- The closure threshold and adjacent-scale ratio make the new leakage at most `t⁻⁴`. -/
theorem triangleClosure_leakage_numeric {t L θx θv Λ : ℝ}
    (ht : 0 < t) (hL : 0 < L) (hθx : 0 < θx) (hθv : 0 ≤ θv)
    (hload : Λ ≤ L * θx) (hratio : θv / θx ≤ t * L) :
    (t ^ 2 * (θv / (t ^ 7 * L ^ 2)) / θx ^ 2) * Λ ≤ 1 / t ^ 4 := by
  calc
    _ ≤ (t ^ 2 * (θv / (t ^ 7 * L ^ 2)) / θx ^ 2) * (L * θx) :=
      mul_le_mul_of_nonneg_left hload (by positivity)
    _ = (θv / θx) / (t ^ 5 * L) := by field_simp
    _ ≤ (t * L) / (t ^ 5 * L) :=
      div_le_div_of_nonneg_right hratio (by positivity)
    _ = 1 / t ^ 4 := by field_simp

/-- Prepared local walks lose at most `i/t⁴` mass outside their growing closure. -/
theorem triangleClosure_walk_leakage [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (w θ : V → ℝ) (hw : ∀ v, 0 ≤ w v) (hθ : ∀ v, 0 < θ v)
    {t : ℕ} (ht : 1 ≤ t)
    (hL : ∀ x, neighborhoodMass G w x ≤ (2 : ℝ) ^ t * θ x)
    (hC : ∀ x v, G.Adj x v →
      max (θ x) (θ v) / (t : ℝ) ≤ commonNeighborhoodMass G w x v)
    (x : V) (hCpos : ∀ v, G.Adj x v → 0 < commonNeighborhoodMass G w x v)
    (v : G.neighborFinset x) (i : ℕ) :
    (smoothedLaw (lawKernel (triangleWalk G w hw x hCpos))
      (lawKernel_stochastic (triangleWalk G w hw x hCpos)) i v).outsideMass
        (neighborSlice G x (triangleClosure G w θ t v i)) ≤ (i : ℝ) / (t : ℝ) ^ 4 := by
  classical
  let P := lawKernel (triangleWalk G w hw x hCpos)
  have hP := lawKernel_stochastic (triangleWalk G w hw x hCpos)
  have ht₀ : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hCt (z : V) (hz : G.Adj x z) :
      θ x / (t : ℝ) ≤ commonNeighborhoodMass G w x z :=
    (div_le_div_of_nonneg_right (le_max_left _ _) ht₀.le).trans (hC x z hz)
  have hden := triangleWalk_density_le G w hw x hCpos (hθ x) ht₀ hCt
  have hratio : θ v / θ x ≤ (t : ℝ) * 2 ^ t :=
    prepared_adjacent_scale_ratio G hθ hw ht₀ hL hC
      ((G.mem_neighborFinset x v).mp v.property).symm
  induction i with
  | zero =>
    simp only [Nat.cast_zero, zero_div]
    apply le_of_eq
    simp only [smoothedLaw, FiniteLaw.outsideMass, FiniteLaw.ofStochasticRow,
      triangleClosure, neighborhoodClosure, Nat.rec_zero]
    simp only [smoothedKernel, pow_zero, mul_one]
    apply Finset.sum_eq_zero
    intro y hy
    have hn : ¬G.Adj v y := by
      simpa only [Finset.mem_compl, mem_neighborSlice, SimpleGraph.mem_neighborFinset] using hy
    simp [lawKernel, triangleWalk, hn]
  | succ i ih =>
    have hd (z : G.neighborFinset x) :
        (smoothedLaw P hP i v).mass z ≤ (t : ℝ) * w z / θ x :=
      smoothedKernel_density_le hP hden i v z
    have hstep := triangleWalk_leakage_step_le G w hw x hCpos (hθ x) ht₀
      (a := θ v / ((t : ℝ) ^ 7 * ((2 : ℝ) ^ t) ^ 2))
      (div_nonneg (hθ v).le (by positivity))
      hCt (smoothedLaw P hP i v) hd
      (neighborhoodClosure_subset_succ G w _ v i)
      (fun y hy ↦ (neighborhoodMassOn_lt_of_not_mem_closure G w _ v y i hy).le)
    have hnum := triangleClosure_leakage_numeric ht₀ (by positivity : (0 : ℝ) < 2 ^ t)
      (hθ x) (hθ v).le (hL x) hratio
    change (smoothedLaw P hP (i + 1) v).outsideMass _ ≤ _
    rw [smoothedLaw_succ_right]
    calc
      _ ≤ (smoothedLaw P hP i v).outsideMass
          (neighborSlice G x (triangleClosure G w θ t v i)) +
          ((t : ℝ) ^ 2 * (θ v / ((t : ℝ) ^ 7 * ((2 : ℝ) ^ t) ^ 2)) / θ x ^ 2) *
            neighborhoodMass G w x := hstep
      _ ≤ (i : ℝ) / (t : ℝ) ^ 4 + 1 / (t : ℝ) ^ 4 := add_le_add ih hnum
      _ = _ := by push_cast; ring

end Cliquefree
