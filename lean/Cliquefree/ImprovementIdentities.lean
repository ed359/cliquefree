module

public import Cliquefree.GraphIdentities
public import Cliquefree.Potential
public import Cliquefree.Induced

/-!
# Exact potential changes under lifting and deletion
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Neighborhood mass is additive in its weight vector. -/
theorem neighborhoodMass_add (G : SimpleGraph V) (w d : V → ℝ) (v : V) :
    neighborhoodMass G (fun x ↦ w x + d x) v =
      neighborhoodMass G w v + neighborhoodMass G d v := by
  classical
  unfold neighborhoodMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> ring

/-- The exact quadratic expansion of edge mass has one symmetric mixed term. -/
theorem edgeMass_add (G : SimpleGraph V) (w d : V → ℝ) :
    edgeMass G (fun x ↦ w x + d x) =
      edgeMass G w + edgeMass G d + ∑ v, d v * neighborhoodMass G w v := by
  unfold edgeMass
  simp_rw [neighborhoodMass_add, add_mul, mul_add]
  simp only [Finset.sum_add_distrib]
  rw [sum_mul_neighborhoodMass_comm G w d]
  ring

/-- Potential change equals its first-order term minus scalar tangent losses and quadratic cost. -/
theorem graphPotential_add_change (G : SimpleGraph V) (u w d : V → ℝ) :
    graphPotential G u (fun v ↦ w v + d v) - graphPotential G u w =
      (∑ v, residual G u w v * d v) -
      (∑ v, (scalarPotential (u v) (w v) +
        deriv (scalarPotential (u v)) (w v) * d v - scalarPotential (u v) (w v + d v))) -
      2 * edgeMass G d := by
  unfold graphPotential
  rw [edgeMass_add]
  simp only [residual, sub_mul, mul_assoc, Finset.sum_sub_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum]
  have hcomm : (∑ v, neighborhoodMass G w v * d v) =
      ∑ v, d v * neighborhoodMass G w v := by
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hcomm]
  ring

/-- The exact change formula applies to any final weight vector. -/
theorem graphPotential_change (G : SimpleGraph V) (u w q : V → ℝ) :
    graphPotential G u q - graphPotential G u w =
      (∑ v, residual G u w v * (q v - w v)) -
      (∑ v, (scalarPotential (u v) (w v) + deriv (scalarPotential (u v)) (w v) *
        (q v - w v) - scalarPotential (u v) (q v))) -
      2 * edgeMass G (fun v ↦ q v - w v) := by
  simpa only [← add_sub_assoc, add_sub_cancel_left] using
    graphPotential_add_change G u w (fun v ↦ q v - w v)

/-- Increase the weights on one set and remove a second set. -/
def improvedWeights (w : V → ℝ) (A B : Finset V) (k : ℝ) (m : V → ℝ) : V → ℝ := by
  classical
  exact fun v ↦ if v ∈ B then 0 else if v ∈ A then (1 + k * m v) * w v else w v

omit [Fintype V] in
/-- Nonnegative original weights and multipliers give nonnegative improved weights. -/
theorem improvedWeights_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A B : Finset V)
    {k : ℝ} (hk : 0 ≤ k) {m : V → ℝ} (hm : ∀ v, 0 ≤ m v) (v : V) :
    0 ≤ improvedWeights w A B k m v := by
  classical
  unfold improvedWeights
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (add_nonneg zero_le_one (mul_nonneg hk (hm v))) (hw v)
  · exact hw v

/-- Scaling one vector and subtracting another has the expected exact quadratic edge mass. -/
theorem edgeMass_sub_scale (G : SimpleGraph V) (a b : V → ℝ) (k : ℝ) :
    edgeMass G (fun v ↦ k * a v - b v) =
      k ^ 2 * edgeMass G a + edgeMass G b -
        k * ∑ v, a v * neighborhoodMass G b v := by
  have heq : (fun v ↦ k * a v - b v) = (fun v ↦ k * a v + (-1) * b v) := by
    funext v
    ring
  rw [heq, edgeMass_add, edgeMass_scale, edgeMass_scale]
  simp only [neighborhoodMass_scale, neg_one_sq, one_mul]
  have hcross : (∑ v, (-1) * b v * (k * neighborhoodMass G a v)) =
      -k * ∑ v, b v * neighborhoodMass G a v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [hcross, sum_mul_neighborhoodMass_comm G b a]
  ring


omit [Fintype V] in
/-- Disjoint lifting and deletion sets split the displacement into two zero extensions. -/
theorem improvedWeights_sub_eq (w : V → ℝ) (A B : Finset V) (hAB : Disjoint A B)
    (k : ℝ) (m : V → ℝ) :
    (fun v ↦ improvedWeights w A B k m v - w v) =
      fun v ↦ k * extendByZero A (fun x ↦ w x * m x) v -
        extendByZero B (fun x ↦ w x) v := by
  classical
  funext v
  by_cases hvA : v ∈ A
  · have hvB : v ∉ B := fun h ↦ Finset.disjoint_left.mp hAB hvA h
    simp only [improvedWeights, extendByZero, ite_eq_right hvB, ite_eq_left hvA,
      dite_eq_left hvA, dite_eq_right hvB]
    ring
  · by_cases hvB : v ∈ B <;> simp [improvedWeights, extendByZero, hvA, hvB]

/-- The mixed edge form of two zero extensions is the ordered sum over their original sets. -/
theorem sum_extendByZero_neighborhoodMass (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (a : A → ℝ) (b : B → ℝ) :
    (∑ v, extendByZero A a v * neighborhoodMass G (extendByZero B b) v) =
      ∑ x : A, ∑ y : B, if G.Adj x y then a x * b y else 0 := by
  classical
  have heq : (fun v ↦ extendByZero A a v * neighborhoodMass G (extendByZero B b) v) =
      extendByZero A (fun x ↦ a x * neighborhoodMass G (extendByZero B b) x) := by
    funext v
    by_cases hv : v ∈ A <;> simp [extendByZero, hv]
  rw [heq, sum_extendByZero]
  simp_rw [neighborhoodMass_extendByZero, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

omit [Fintype V] in
/-- Cross mass can equivalently be summed over the two finite vertex subtypes. -/
theorem crossMass_eq_subtype_sum (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = ∑ x : A, ∑ y : B, if G.Adj x y then w x * w y else 0 := by
  classical
  symm
  rw [Finset.sum_coe_sort A (fun x : V ↦ ∑ y : B, if G.Adj x y then w x * w y else 0)]
  unfold crossMass
  apply Finset.sum_congr rfl
  intro x _
  convert Finset.sum_coe_sort B (fun y : V ↦ if G.Adj x y then w x * w y else 0) using 1
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> rfl

/-- Twice the edge mass never exceeds the square of the total nonnegative vertex mass. -/
theorem two_mul_edgeMass_le_total_sq (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) : 2 * edgeMass G w ≤ (∑ v, w v) ^ 2 := by
  classical
  rw [← weighted_handshake]
  have hn (v : V) : neighborhoodMass G w v ≤ ∑ x, w x := by
    unfold neighborhoodMass
    apply Finset.sum_le_sum
    intro x _
    split_ifs
    · exact le_rfl
    · exact hw x
  calc
    _ ≤ ∑ v, w v * (∑ x, w x) :=
      Finset.sum_le_sum (fun v _ ↦ mul_le_mul_of_nonneg_left (hn v) (hw v))
    _ = (∑ v, w v) ^ 2 := by rw [← Finset.sum_mul]; ring

end Cliquefree
