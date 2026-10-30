module

public import Cliquefree.TriangleClosure

/-!
# Dyadic size bounds for triangle closures

Direct bounds by powers of two establish the size hypotheses of both cross-mass tests.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- The closure with the threshold prescribed in the triangle dichotomy. -/
def triangleClosure (G : SimpleGraph V) (w θ : V → ℝ) (t : ℕ) (v : V) : ℕ → Finset V :=
  neighborhoodClosure G w (θ v / ((t : ℝ) ^ 7 * ((2 : ℝ) ^ t) ^ 2)) v

/-- Scales in the triangle closure grow by at most the prepared adjacent-scale ratio. -/
theorem triangleClosure_scale_le (G : SimpleGraph V) (w θ : V → ℝ) {t : ℕ}
    (ht : 1 ≤ t) (hθ : ∀ x, 0 < θ x)
    (hratio : ∀ x y, G.Adj x y → θ y ≤ ((t : ℝ) * 2 ^ t) * θ x)
    (v : V) (i : ℕ) :
    ∀ y ∈ triangleClosure G w θ t v i, θ y ≤ θ v * ((t : ℝ) * 2 ^ t) ^ (i + 1) := by
  have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have htwo : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
  exact neighborhoodClosure_scale_le G w θ (div_pos (hθ v) (by positivity))
    (one_le_mul_of_one_le_of_one_le ht' htwo) (fun x ↦ (hθ x).le) hratio v i

omit [Fintype V] in
/-- A dyadic bound for the uniform growth factor over one full closure construction. -/
theorem triangleClosure_growth_factor {t : ℕ} (ht : 1 ≤ t) :
    1 + (t : ℝ) ^ 7 * (2 ^ t) ^ 3 * ((t : ℝ) * 2 ^ t) ^ (t + 1) ≤
      (2 : ℝ) ^ (16 * t ^ 2) := by
  have ht2 : (t : ℝ) ≤ (2 : ℝ) ^ t := by exact_mod_cast t.lt_two_pow_self.le
  have hR : (t : ℝ) * 2 ^ t ≤ (2 : ℝ) ^ (2 * t) := by
    calc
      _ ≤ (2 : ℝ) ^ t * 2 ^ t := mul_le_mul_of_nonneg_right ht2 (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hf : (t : ℝ) ^ 7 * (2 ^ t) ^ 3 * ((t : ℝ) * 2 ^ t) ^ (t + 1) ≤
      (2 : ℝ) ^ (14 * t ^ 2) := by
    calc
      _ ≤ ((2 : ℝ) ^ t) ^ 7 * (2 ^ t) ^ 3 * (2 ^ (2 * t)) ^ (t + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) ht2 7)
          (by positivity)) (pow_le_pow_left₀ (by positivity) hR _) (by positivity)
          (by positivity)
      _ = (2 : ℝ) ^ (t * 7 + t * 3 + (2 * t) * (t + 1)) := by
        simp only [← pow_mul, ← pow_add]
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith [sq_nonneg (t - 1 : ℤ)])
  calc
    _ ≤ 1 + (2 : ℝ) ^ (14 * t ^ 2) := add_le_add_right hf _
    _ ≤ (2 : ℝ) ^ (14 * t ^ 2) + 2 ^ (14 * t ^ 2) :=
      add_le_add_left (one_le_pow₀ (by norm_num)) _
    _ = (2 : ℝ) ^ (14 * t ^ 2 + 1) := by rw [pow_succ]; ring
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by nlinarith)

/-- The full triangle closure satisfies the first test's required weight bound. -/
theorem triangleClosure_weight_le (G : SimpleGraph V) {w θ : V → ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hw : ∀ x, 0 ≤ w x) (hθ : ∀ x, 0 < θ x)
    (hload : ∀ x, neighborhoodMass G w x ≤ 2 ^ t * θ x)
    (hratio : ∀ x y, G.Adj x y → θ y ≤ ((t : ℝ) * 2 ^ t) * θ x) (v : V) :
    weightSum w (triangleClosure G w θ t v t) ≤ θ v * (2 : ℝ) ^ (30 * t ^ 3) := by
  have ht' : (0 : ℝ) < t := by exact_mod_cast (show 0 < t by omega)
  have hθv := hθ v
  let a := θ v / ((t : ℝ) ^ 7 * ((2 : ℝ) ^ t) ^ 2)
  let R := (t : ℝ) * (2 : ℝ) ^ t
  let M := (2 : ℝ) ^ t * θ v * R ^ (t + 1)
  have ha : 0 < a := div_pos (hθ v) (by positivity)
  have hR : 1 ≤ R := one_le_mul_of_one_le_of_one_le (by exact_mod_cast ht)
    (one_le_pow₀ (by norm_num))
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hstep : ∀ i < t, ∀ x ∈ neighborhoodClosure G w a v i,
      neighborhoodMass G w x ≤ M := by
    intro i hi x hx
    have hs := triangleClosure_scale_le G w θ ht hθ hratio v i x hx
    calc
      _ ≤ 2 ^ t * θ x := hload x
      _ ≤ 2 ^ t * (θ v * R ^ (i + 1)) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ ≤ 2 ^ t * (θ v * R ^ (t + 1)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ hR (by omega)) hθv.le) (by positivity)
      _ = M := by dsimp [M]; ring
  have hf : 1 + M / a ≤ (2 : ℝ) ^ (16 * t ^ 2) := by
    convert triangleClosure_growth_factor ht using 1
    dsimp [M, a, R]
    field_simp [(hθ v).ne', ht'.ne']
  have hb := neighborhoodClosure_weight_le_pow G hw ha hM v t hstep t le_rfl
  calc
    _ ≤ neighborhoodMass G w v * (1 + M / a) ^ t := hb
    _ ≤ (2 ^ t * θ v) * ((2 : ℝ) ^ (16 * t ^ 2)) ^ t :=
      mul_le_mul (hload v) (pow_le_pow_left₀ (by positivity) hf t) (by positivity)
        (by positivity)
    _ = θ v * (2 : ℝ) ^ (t + 16 * t ^ 3) := by
      rw [← pow_mul]
      have he : 16 * t ^ 2 * t = 16 * t ^ 3 := by ring
      rw [he, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num)
        (by nlinarith [le_self_pow₀ ht (by norm_num : 3 ≠ 0)])) (hθ v).le

/-- A dyadic scale bound on the full closure, at the first test's exponent. -/
theorem triangleClosure_scale_le_dyadic (G : SimpleGraph V) (w θ : V → ℝ) {t : ℕ}
    (ht : 1 ≤ t) (hθ : ∀ x, 0 < θ x)
    (hratio : ∀ x y, G.Adj x y → θ y ≤ ((t : ℝ) * 2 ^ t) * θ x) (v : V) :
    ∀ y ∈ triangleClosure G w θ t v t, θ y ≤ θ v * (2 : ℝ) ^ (30 * t ^ 3) := by
  have ht2 : (t : ℝ) ≤ (2 : ℝ) ^ t := by exact_mod_cast t.lt_two_pow_self.le
  have hR : (t : ℝ) * 2 ^ t ≤ (2 : ℝ) ^ (2 * t) := by
    calc
      _ ≤ (2 : ℝ) ^ t * 2 ^ t := mul_le_mul_of_nonneg_right ht2 (by positivity)
      _ = _ := by rw [← pow_add]; congr 1; omega
  intro y hy
  apply (triangleClosure_scale_le G w θ ht hθ hratio v t y hy).trans
  apply mul_le_mul_of_nonneg_left _ (hθ v).le
  calc
    _ ≤ ((2 : ℝ) ^ (2 * t)) ^ (t + 1) := pow_le_pow_left₀ (by positivity) hR _
    _ = (2 : ℝ) ^ (2 * t * (t + 1)) := (pow_mul _ _ _).symm
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by
      have hsq : t ≤ t ^ 2 := le_self_pow₀ ht (by norm_num)
      have hcube : t ^ 2 ≤ t ^ 3 := by simpa [pow_succ] using Nat.mul_le_mul_right t hsq
      nlinarith)

/-- The full closure satisfies the first test's required scaled-mass bound. -/
theorem triangleClosure_scaledMass_le (G : SimpleGraph V) {w θ : V → ℝ} {t : ℕ}
    (ht : 1 ≤ t) (hw : ∀ x, 0 ≤ w x) (hθ : ∀ x, 0 < θ x)
    (hload : ∀ x, neighborhoodMass G w x ≤ 2 ^ t * θ x)
    (hratio : ∀ x y, G.Adj x y → θ y ≤ ((t : ℝ) * 2 ^ t) * θ x) (v : V) :
    scaledMass θ w (triangleClosure G w θ t v t) ≤ θ v ^ 2 * (2 : ℝ) ^ (60 * t ^ 3) := by
  have hθv := hθ v
  calc
    _ ≤ (θ v * (2 : ℝ) ^ (30 * t ^ 3)) *
        weightSum w (triangleClosure G w θ t v t) := by
      unfold scaledMass weightSum
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun y hy ↦ mul_le_mul_of_nonneg_right
        (triangleClosure_scale_le_dyadic G w θ ht hθ hratio v y hy) (hw y))
    _ ≤ (θ v * (2 : ℝ) ^ (30 * t ^ 3)) * (θ v * (2 : ℝ) ^ (30 * t ^ 3)) :=
      mul_le_mul_of_nonneg_left (triangleClosure_weight_le G ht hw hθ hload hratio v)
        (by positivity)
    _ = _ := by
      have he : 60 * t ^ 3 = 30 * t ^ 3 + 30 * t ^ 3 := by ring
      rw [he, pow_add]
      ring

/-- Failure of the first cross-mass test gives a triangle witness of exponent `30 t³`. -/
def triangleWitnessOfFirstTest (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} {t : ℕ} (ht : 1 ≤ t) (hw : ∀ x, 0 ≤ w x) (hθ : ∀ x, 0 < θ x)
    (hload : ∀ x, neighborhoodMass G w x ≤ 2 ^ t * θ x)
    (hratio : ∀ x y, G.Adj x y → θ y ≤ ((t : ℝ) * 2 ^ t) * θ x) (v : V)
    (hfail : 24 * (((30 * t ^ 3 : ℕ) : ℝ) * scaledMass θ w (G.neighborFinset v) +
      θ v ^ 2 / 2 ^ (30 * t ^ 3)) <
      crossMass G w (G.neighborFinset v) (triangleClosure G w θ t v t)) :
    TriangleWitness G θ w where
  A := G.neighborFinset v
  B := triangleClosure G w θ t v t
  p := 30 * t ^ 3
  p_pos := by nlinarith [Nat.one_le_pow 3 t ht]
  scaleVertex := v
  weight_A := by
    change (∑ y ∈ G.neighborFinset v, w y) ≤ _
    rw [← neighborhoodMass_eq_sum_neighborFinset]
    apply (hload v).trans
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num) (by nlinarith [le_self_pow₀ ht (by norm_num : 3 ≠ 0)]))
      (hθ v).le
  weight_B := triangleClosure_weight_le G ht hw hθ hload hratio v
  scaled_B := by
    convert triangleClosure_scaledMass_le G ht hw hθ hload hratio v using 1
    ring
  cross_large := hfail

/-- A prepared neighborhood has the scaled-mass bound needed by the second test. -/
theorem scaledMass_neighbor_le_dyadic (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} (t : ℕ) (hw : ∀ x, 0 ≤ w x) (hθ : ∀ x, 0 ≤ θ x)
    (hload : ∀ x, neighborhoodMass G w x ≤ 2 ^ t * θ x)
    (hratio : ∀ x y, G.Adj x y → θ y ≤ ((t : ℝ) * 2 ^ t) * θ x) (v : V) :
    scaledMass θ w (G.neighborFinset v) ≤ θ v ^ 2 * (2 : ℝ) ^ (4 * t) := by
  have hθv := hθ v
  have ht2 : (t : ℝ) ≤ (2 : ℝ) ^ t := by exact_mod_cast t.lt_two_pow_self.le
  calc
    _ ≤ (((t : ℝ) * 2 ^ t) * θ v) * neighborhoodMass G w v := by
      rw [neighborhoodMass_eq_sum_neighborFinset]
      unfold scaledMass weightSum
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum (fun y hy ↦ mul_le_mul_of_nonneg_right
        (hratio v y ((G.mem_neighborFinset v y).mp hy)) (hw y))
    _ ≤ (((t : ℝ) * 2 ^ t) * θ v) * (2 ^ t * θ v) :=
      mul_le_mul_of_nonneg_left (hload v) (by positivity)
    _ ≤ (((2 : ℝ) ^ t * 2 ^ t) * θ v) * (2 ^ t * θ v) := by
      gcongr
    _ = θ v ^ 2 * (2 : ℝ) ^ (3 * t) := by
      have he : 3 * t = t + t + t := by omega
      rw [he, pow_add, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega))
      (sq_nonneg _)

/-- Failure of the second test gives a triangle witness of exponent `2 t`. -/
def triangleWitnessOfSecondTest (G : SimpleGraph V) [DecidableRel G.Adj]
    {w θ : V → ℝ} {t : ℕ} (ht : 1 ≤ t) (hw : ∀ x, 0 ≤ w x) (hθ : ∀ x, 0 ≤ θ x)
    (hload : ∀ x, neighborhoodMass G w x ≤ 2 ^ t * θ x)
    (hratio : ∀ x y, G.Adj x y → θ y ≤ ((t : ℝ) * 2 ^ t) * θ x)
    (v : V) (B : Finset V) (hB : B ⊆ G.neighborFinset v)
    (hfail : 24 * (((2 * t : ℕ) : ℝ) * scaledMass θ w B + θ v ^ 2 / 2 ^ (2 * t)) <
      crossMass G w B (G.neighborFinset v)) : TriangleWitness G θ w := by
  have hN : weightSum w (G.neighborFinset v) ≤ θ v * (2 : ℝ) ^ (2 * t) := by
    change (∑ y ∈ G.neighborFinset v, w y) ≤ _
    rw [← neighborhoodMass_eq_sum_neighborFinset]
    apply (hload v).trans
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (hθ v)
  exact {
    A := B
    B := G.neighborFinset v
    p := 2 * t
    p_pos := by omega
    scaleVertex := v
    weight_A := (Finset.sum_le_sum_of_subset_of_nonneg hB (fun x _ _ ↦ hw x)).trans hN
    weight_B := hN
    scaled_B := by
      convert scaledMass_neighbor_le_dyadic G t hw hθ hload hratio v using 1
      ring
    cross_large := hfail }

end Cliquefree
