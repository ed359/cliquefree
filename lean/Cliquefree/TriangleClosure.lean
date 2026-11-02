module

public import Cliquefree.TriangleBasics

/-!
# Weighted neighborhood closures

The threshold closure used by the triangle dichotomy, together with its scale and mass bounds.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*}

/-- Neighbor weight restricted to a finite target set. -/
def neighborhoodMassOn (G : SimpleGraph V) (w : V → ℝ) (A : Finset V) (x : V) : ℝ := by
  classical
  exact ∑ y ∈ A, if G.Adj x y then w y else 0

/-- Restricted neighbor weight is nonnegative for nonnegative weights. -/
theorem neighborhoodMassOn_nonneg (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (A : Finset V) (x : V) : 0 ≤ neighborhoodMassOn G w A x := by
  classical
  exact Finset.sum_nonneg (fun y _ ↦ by split_ifs <;> simp [hw])

/-- Restricting the neighbor set cannot increase its mass. -/
theorem neighborhoodMassOn_le [Fintype V] (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (A : Finset V) (x : V) :
    neighborhoodMassOn G w A x ≤ neighborhoodMass G w x := by
  classical
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ A)
    (fun y _ _ ↦ by split_ifs <;> simp [hw])

/-- Positive restricted neighbor weight gives an adjacent vertex in the target set. -/
theorem neighborhoodMassOn_pos_neighbor (G : SimpleGraph V) {w : V → ℝ}
    {A : Finset V} {x : V} (h : 0 < neighborhoodMassOn G w A x) :
    ∃ y ∈ A, G.Adj x y := by
  classical
  by_contra hn
  push Not at hn
  have hz : neighborhoodMassOn G w A x = 0 :=
    Finset.sum_eq_zero (fun y hy ↦ ite_eq_right (hn y hy))
  linarith

/-- Cross mass is the weighted sum of restricted neighbor masses. -/
theorem crossMass_eq_sum_neighborhoodMassOn (G : SimpleGraph V) (w : V → ℝ)
    (A B : Finset V) : crossMass G w A B = ∑ x ∈ A, w x * neighborhoodMassOn G w B x := by
  classical
  simp only [crossMass, neighborhoodMassOn, Finset.mul_sum, mul_ite, mul_zero]

/-- Starting with a neighborhood, repeatedly add vertices seeing the threshold weight. -/
def neighborhoodClosure [Fintype V] (G : SimpleGraph V) (w : V → ℝ) (a : ℝ)
    (v : V) : ℕ → Finset V := by
  classical
  exact fun i ↦ Nat.rec (G.neighborFinset v)
    (fun _ A ↦ A ∪ Finset.univ.filter (fun y ↦ a ≤ neighborhoodMassOn G w A y)) i

/-- Closure sets grow at each step. -/
theorem neighborhoodClosure_subset_succ [Fintype V] (G : SimpleGraph V) (w : V → ℝ)
    (a : ℝ) (v : V) (i : ℕ) :
    neighborhoodClosure G w a v i ⊆ neighborhoodClosure G w a v (i + 1) := by
  classical
  exact Finset.subset_union_left

/-- Outside the next closure set, the previous set has neighbor mass below the threshold. -/
theorem neighborhoodMassOn_lt_of_not_mem_closure [Fintype V] (G : SimpleGraph V)
    (w : V → ℝ) (a : ℝ) (v y : V) (i : ℕ)
    (hy : y ∉ neighborhoodClosure G w a v (i + 1)) :
    neighborhoodMassOn G w (neighborhoodClosure G w a v i) y < a := by
  classical
  apply lt_of_not_ge
  intro hh
  exact hy (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩))

/-- An adjacent scale ratio bounds scales throughout the threshold closure. -/
theorem neighborhoodClosure_scale_le [Fintype V] (G : SimpleGraph V) (w θ : V → ℝ)
    {a R : ℝ} (ha : 0 < a) (hR : 1 ≤ R) (hθ : ∀ x, 0 ≤ θ x)
    (hratio : ∀ x y, G.Adj x y → θ y ≤ R * θ x) (v : V) (i : ℕ) :
    ∀ y ∈ neighborhoodClosure G w a v i, θ y ≤ θ v * R ^ (i + 1) := by
  classical
  induction i with
  | zero =>
    intro y hy
    simpa only [Nat.zero_add, pow_one, mul_comm] using hratio v y ((G.mem_neighborFinset v y).mp hy)
  | succ i ih =>
    intro y hy
    obtain hy | hy := Finset.mem_union.mp hy
    · apply (ih y hy).trans
      calc
        θ v * R ^ (i + 1) ≤ (θ v * R ^ (i + 1)) * R :=
          le_mul_of_one_le_right (mul_nonneg (hθ v) (pow_nonneg (by linarith) _)) hR
        _ = θ v * R ^ (i + 1 + 1) := by rw [pow_succ R (i + 1)]; ring
    · have hm := (Finset.mem_filter.mp hy).2
      obtain ⟨z, hz, hyz⟩ := neighborhoodMassOn_pos_neighbor G (ha.trans_le hm)
      calc
        θ y ≤ R * θ z := hratio z y hyz.symm
        _ ≤ R * (θ v * R ^ (i + 1)) := mul_le_mul_of_nonneg_left (ih z hz) (by linarith)
        _ = θ v * R ^ (i + 1 + 1) := by rw [pow_succ]; ring

/-- A threshold set has weight bounded by the cross mass feeding it. -/
theorem threshold_weight_le_crossMass (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ x, 0 ≤ w x) (A B : Finset V) {a : ℝ}
    (hB : ∀ x ∈ B, a ≤ neighborhoodMassOn G w A x) :
    a * weightSum w B ≤ crossMass G w B A := by
  rw [crossMass_eq_sum_neighborhoodMassOn]
  unfold weightSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hB x hx) (hw x)

/-- A uniform load bound on the source controls every cross mass out of that source. -/
theorem crossMass_le_load_weight [Fintype V] (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ x, 0 ≤ w x) (A B : Finset V) {M : ℝ}
    (hload : ∀ x ∈ A, neighborhoodMass G w x ≤ M) :
    crossMass G w A B ≤ M * weightSum w A := by
  rw [crossMass_eq_sum_neighborhoodMassOn]
  unfold weightSum
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro x hx
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left
    ((neighborhoodMassOn_le G hw B x).trans (hload x hx)) (hw x)

/-- One closure step increases weight by at most the load-to-threshold ratio. -/
theorem neighborhoodClosure_weight_step [Fintype V] (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ x, 0 ≤ w x) {a M : ℝ} (ha : 0 < a) (v : V) (i : ℕ)
    (hload : ∀ x ∈ neighborhoodClosure G w a v i, neighborhoodMass G w x ≤ M) :
    weightSum w (neighborhoodClosure G w a v (i + 1)) ≤
      (1 + M / a) * weightSum w (neighborhoodClosure G w a v i) := by
  classical
  let A := neighborhoodClosure G w a v i
  let B := Finset.univ.filter (fun y ↦ a ≤ neighborhoodMassOn G w A y)
  have hB : a * weightSum w B ≤ M * weightSum w A := by
    calc
      _ ≤ crossMass G w B A := threshold_weight_le_crossMass G hw A B
        (fun x hx ↦ (Finset.mem_filter.mp hx).2)
      _ = crossMass G w A B := crossMass_comm G w B A
      _ ≤ _ := crossMass_le_load_weight G hw A B hload
  have hBw : weightSum w B ≤ M / a * weightSum w A := by
    rw [div_mul_eq_mul_div]
    exact (le_div_iff₀ ha).mpr (by simpa only [mul_comm] using hB)
  have hu : weightSum w (A ∪ B) ≤ weightSum w A + weightSum w B := by
    have he := Finset.sum_union_inter (s₁ := A) (s₂ := B) (f := w)
    have hn := weightSum_nonneg hw (A ∩ B)
    change weightSum w (A ∪ B) + weightSum w (A ∩ B) =
      weightSum w A + weightSum w B at he
    linarith
  change weightSum w (A ∪ B) ≤ _
  calc
    _ ≤ weightSum w A + weightSum w B := hu
    _ ≤ weightSum w A + M / a * weightSum w A := add_le_add_right hBw _
    _ = _ := by ring

/-- A uniform load estimate through the first `n` steps gives a geometric weight bound. -/
theorem neighborhoodClosure_weight_le_pow [Fintype V] (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ x, 0 ≤ w x) {a M : ℝ} (ha : 0 < a) (hM : 0 ≤ M) (v : V) (n : ℕ)
    (hload : ∀ i < n, ∀ x ∈ neighborhoodClosure G w a v i, neighborhoodMass G w x ≤ M)
    (i : ℕ) (hi : i ≤ n) :
    weightSum w (neighborhoodClosure G w a v i) ≤
      neighborhoodMass G w v * (1 + M / a) ^ i := by
  classical
  induction i with
  | zero =>
    simp only [neighborhoodClosure, weightSum, Nat.rec_zero, pow_zero, mul_one]
    exact (neighborhoodMass_eq_sum_neighborFinset G w v).ge
  | succ i ih =>
    calc
      _ ≤ (1 + M / a) * weightSum w (neighborhoodClosure G w a v i) :=
        neighborhoodClosure_weight_step G hw ha v i (hload i (by omega))
      _ ≤ (1 + M / a) * (neighborhoodMass G w v * (1 + M / a) ^ i) :=
        mul_le_mul_of_nonneg_left (ih (by omega)) (by positivity)
      _ = _ := by rw [pow_succ]; ring

end Cliquefree
