module

public import Cliquefree.FiniteLaw
public import Cliquefree.DeletionIdentities

/-!
# Disjoint cuts from finite random assignments
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- The uniform law on a nonempty finite sample space. -/
def FiniteLaw.uniform (Ω : Type*) [Fintype Ω] [Nonempty Ω] : FiniteLaw Ω where
  mass _ := 1 / Fintype.card Ω
  nonneg _ := by positivity
  sum_mass := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card Ω : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp

/-- Uniform expectation is unchanged by permuting the outcomes. -/
theorem FiniteLaw.expectation_uniform_comp {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (e : Ω ≃ Ω) (X : Ω → ℝ) :
    (FiniteLaw.uniform Ω).expectation (fun ω ↦ X (e ω)) =
      (FiniteLaw.uniform Ω).expectation X := by
  unfold FiniteLaw.expectation FiniteLaw.uniform
  exact e.sum_comp (fun ω ↦ (1 / Fintype.card Ω : ℝ) * X ω)

/-- Flip one coordinate of a Boolean vertex assignment. -/
def flipCoordinate (v : V) : (V → Bool) ≃ (V → Bool) := by
  classical
  exact Equiv.piCongrRight (fun x ↦ if x = v then Equiv.boolNot else Equiv.refl Bool)

omit [Fintype V] in
/-- The selected coordinate changes to its opposite Boolean value. -/
@[simp] theorem flipCoordinate_apply_self (v : V) (a : V → Bool) :
    flipCoordinate v a v = !(a v) := by
  classical
  simp [flipCoordinate, Equiv.boolNot]

omit [Fintype V] in
/-- Flipping a coordinate leaves every other coordinate unchanged. -/
theorem flipCoordinate_apply_ne {v x : V} (h : x ≠ v) (a : V → Bool) :
    flipCoordinate v a x = a x := by
  classical
  simp [flipCoordinate, h]

/-- Each Boolean coordinate takes either value with probability one half. -/
theorem expectation_uniform_bool_indicator [DecidableEq V] (v : V) (b : Bool) :
    (FiniteLaw.uniform (V → Bool)).expectation (fun a ↦ if a v = b then 1 else 0) =
      1 / 2 := by
  let μ := FiniteLaw.uniform (V → Bool)
  let X : (V → Bool) → ℝ := fun a ↦ if a v = b then 1 else 0
  have hs := FiniteLaw.expectation_uniform_comp (flipCoordinate v) X
  have hadd : μ.expectation X + μ.expectation (fun a ↦ X (flipCoordinate v a)) = 1 := by
    rw [← FiniteLaw.expectation_add]
    have hpoint : (fun a ↦ X a + X (flipCoordinate v a)) = fun _ ↦ (1 : ℝ) := by
      funext a
      dsimp [X]
      rw [flipCoordinate_apply_self]
      cases h : a v <;> cases b <;> norm_num
    rw [hpoint, FiniteLaw.expectation_const]
  change μ.expectation X = 1 / 2
  change μ.expectation (fun a ↦ X (flipCoordinate v a)) = μ.expectation X at hs
  linarith

/-- Distinct Boolean coordinates realize any ordered value pair with probability one quarter. -/
theorem expectation_uniform_bool_pair [DecidableEq V] {v x : V} (h : x ≠ v)
    (b c : Bool) :
    (FiniteLaw.uniform (V → Bool)).expectation
      (fun a ↦ if a v = b ∧ a x = c then 1 else 0) = 1 / 4 := by
  let μ := FiniteLaw.uniform (V → Bool)
  let X : (V → Bool) → ℝ := fun a ↦ if a v = b ∧ a x = c then 1 else 0
  have hs := FiniteLaw.expectation_uniform_comp (flipCoordinate v) X
  have hadd : μ.expectation X + μ.expectation (fun a ↦ X (flipCoordinate v a)) =
      μ.expectation (fun a ↦ if a x = c then 1 else 0) := by
    rw [← FiniteLaw.expectation_add]
    congr 1
    funext a
    dsimp [X]
    rw [flipCoordinate_apply_self, flipCoordinate_apply_ne h]
    cases hv : a v <;> cases hx : a x <;> cases b <;> cases c <;> norm_num
  rw [expectation_uniform_bool_indicator] at hadd
  change μ.expectation X = 1 / 4
  change μ.expectation (fun a ↦ X (flipCoordinate v a)) = μ.expectation X at hs
  linarith

/-- Expectation commutes with a sum over any finite set. -/
theorem FiniteLaw.expectation_finset_sum {Ω Ξ : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (S : Finset Ξ) (X : Ξ → Ω → ℝ) :
    μ.expectation (fun ω ↦ ∑ x ∈ S, X x ω) = ∑ x ∈ S, μ.expectation (X x) := by
  simp only [FiniteLaw.expectation, Finset.mul_sum]
  exact Finset.sum_comm

/-- The vertices of a set receiving one specified Boolean assignment. -/
def assignedPart (A : Finset V) (a : V → Bool) (b : Bool) : Finset V :=
  A.filter (fun v ↦ a v = b)

omit [Fintype V] in
/-- Membership in an assigned part specifies both the original set and the assigned value. -/
@[simp] theorem mem_assignedPart (A : Finset V) (a : V → Bool) (b : Bool) (v : V) :
    v ∈ assignedPart A a b ↔ v ∈ A ∧ a v = b := Finset.mem_filter

omit [Fintype V] in
/-- Every assigned part lies inside its original set. -/
theorem assignedPart_subset (A : Finset V) (a : V → Bool) (b : Bool) :
    assignedPart A a b ⊆ A := Finset.filter_subset _ _

omit [Fintype V] in
/-- Opposite assignments give disjoint parts even if the original sets overlap. -/
theorem assignedPart_disjoint (A B : Finset V) (a : V → Bool) :
    Disjoint (assignedPart A a false) (assignedPart B a true) := by
  apply Finset.disjoint_left.mpr
  intro v hvA hvB
  have hA := (mem_assignedPart A a false v).mp hvA |>.2
  have hB := (mem_assignedPart B a true v).mp hvB |>.2
  exact Bool.false_ne_true (hA.symm.trans hB)

/-- A fair assignment retains half of every finite weighted vertex sum on average. -/
theorem expectation_weightSum_assignedPart [DecidableEq V] (w : V → ℝ) (A : Finset V)
    (b : Bool) :
    (FiniteLaw.uniform (V → Bool)).expectation
      (fun a ↦ weightSum w (assignedPart A a b)) = weightSum w A / 2 := by
  simp only [weightSum, assignedPart, Finset.sum_filter]
  have hterm (v : V) :
      (FiniteLaw.uniform (V → Bool)).expectation (fun a ↦ if a v = b then w v else 0) =
        w v / 2 := by
    have hpoint : (fun a : V → Bool ↦ if a v = b then w v else 0) =
        fun a ↦ w v * (if a v = b then 1 else 0) := by funext a; split_ifs <;> ring
    rw [hpoint, FiniteLaw.expectation_smul, expectation_uniform_bool_indicator]
    ring
  rw [FiniteLaw.expectation_finset_sum]
  simp_rw [hterm]
  exact (Finset.sum_div A w 2).symm

/-- An oriented edge survives the disjoint fair cut with probability one quarter. -/
theorem expectation_crossMass_assignedPart [DecidableEq V] (G : SimpleGraph V)
    (w : V → ℝ) (A B : Finset V) :
    (FiniteLaw.uniform (V → Bool)).expectation
      (fun a ↦ crossMass G w (assignedPart A a false) (assignedPart B a true)) =
      crossMass G w A B / 4 := by
  classical
  let μ := FiniteLaw.uniform (V → Bool)
  have hpoint (a : V → Bool) :
      crossMass G w (assignedPart A a false) (assignedPart B a true) =
        ∑ x, ∑ y, if x ∈ A ∧ y ∈ B ∧ G.Adj x y then
          (w x * w y) * (if a x = false ∧ a y = true then 1 else 0) else 0 := by
    rw [crossMass_eq_sum_univ]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    simp only [mem_assignedPart]
    split_ifs <;> simp_all
  simp_rw [hpoint, FiniteLaw.expectation_sum]
  rw [crossMass_eq_sum_univ, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro y _
  by_cases h : x ∈ A ∧ y ∈ B ∧ G.Adj x y
  · simp only [ite_eq_left h]
    rw [FiniteLaw.expectation_smul, expectation_uniform_bool_pair h.2.2.ne.symm]
    ring
  · simp only [ite_eq_right h, FiniteLaw.expectation_const, zero_div]

omit [Fintype V] in
/-- A deterministic disjoint subpair attains the fair-partition lower bound on cross gain. -/
theorem exists_disjoint_partition_gain [Finite V] (G : SimpleGraph V) (w b : V → ℝ)
    (A B : Finset V) (p : ℝ) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧ Disjoint A' B' ∧
      (crossMass G w A B - 2 * p * weightSum b A) / 4 ≤
        crossMass G w A' B' - p * weightSum b A' := by
  classical
  let := Fintype.ofFinite V
  let μ := FiniteLaw.uniform (V → Bool)
  let X : (V → Bool) → ℝ := fun a ↦
    crossMass G w (assignedPart A a false) (assignedPart B a true) -
      p * weightSum b (assignedPart A a false)
  have hmean : μ.expectation X = (crossMass G w A B - 2 * p * weightSum b A) / 4 := by
    dsimp [X]
    rw [FiniteLaw.expectation_sub, FiniteLaw.expectation_smul,
      expectation_crossMass_assignedPart, expectation_weightSum_assignedPart]
    ring
  obtain ⟨a, ha, hgain⟩ := μ.exists_ge_expectation X
  refine ⟨assignedPart A a false, assignedPart B a true, assignedPart_subset A a false,
    assignedPart_subset B a true, assignedPart_disjoint A B a, ?_⟩
  rw [← hmean]
  exact hgain

omit [Fintype V] in
/-- A strong cross-mass witness contains a nonempty disjoint pair with the required gain margin. -/
theorem exists_disjoint_strong_witness [Finite V] (G : SimpleGraph V) (w b : V → ℝ)
    (hb : ∀ v, 0 ≤ b v) (A B : Finset V) {p δ : ℝ} (hp : 0 ≤ p) (hδ : 0 < δ)
    (hstrong : 24 * (p * weightSum b A + δ) < crossMass G w A B) :
    ∃ A' B' : Finset V, A' ⊆ A ∧ B' ⊆ B ∧ Disjoint A' B' ∧ A'.Nonempty ∧ B'.Nonempty ∧
      11 / 2 * p * weightSum b A + 6 * δ <
        crossMass G w A' B' - p * weightSum b A' := by
  obtain ⟨A', B', hA, hB, hd, hgain⟩ := exists_disjoint_partition_gain G w b A B p
  have hmargin : 11 / 2 * p * weightSum b A + 6 * δ <
      crossMass G w A' B' - p * weightSum b A' := by linarith
  have hpositive : 0 < crossMass G w A' B' - p * weightSum b A' := by
    have hmass := weightSum_nonneg hb A
    nlinarith [mul_nonneg hp hmass]
  have hAne : A'.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    simp [he, crossMass, weightSum] at hpositive
  have hBne : B'.Nonempty := by
    by_contra h
    have he := Finset.not_nonempty_iff_eq_empty.mp h
    have hmass := weightSum_nonneg hb A'
    simp only [he, crossMass, Finset.sum_empty, Finset.sum_const_zero] at hpositive
    nlinarith [mul_nonneg hp hmass]
  exact ⟨A', B', hA, hB, hd, hAne, hBne, hmargin⟩

end Cliquefree
