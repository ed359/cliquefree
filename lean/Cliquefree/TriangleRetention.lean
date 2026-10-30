module

public import Cliquefree.TriangleSplitting

/-!
# Expected triangle retention under incidence splitting

The three corner disagreements and six directed incidence rejections bound the loss.
Permutation symmetry reduces their weighted sums to one corner and one incidence.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V L Ω : Type*} [Fintype V] [Fintype Ω]

open Classical in
/-- Sum a function over ordered triangles with the product of their vertex weights. -/
def orderedTriangleSum (G : SimpleGraph V) (w : V → ℝ) (F : V → V → V → ℝ) : ℝ :=
  ∑ x, ∑ y, ∑ z, if G.Adj x y ∧ G.Adj y z ∧ G.Adj z x
    then w x * w y * w z * F x y z else 0

/-- Cyclically rotating an ordered triangle preserves its weighted sum. -/
theorem orderedTriangleSum_rotate (G : SimpleGraph V) (w : V → ℝ)
    (F : V → V → V → ℝ) :
    orderedTriangleSum G w (fun x y z ↦ F y z x) = orderedTriangleSum G w F := by
  classical
  unfold orderedTriangleSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : G.Adj x y ∧ G.Adj y z ∧ G.Adj z x
  · simp only [h.1, h.2.1, h.2.2, and_self, ite_true]
    ring
  · have h' : ¬(G.Adj y z ∧ G.Adj z x ∧ G.Adj x y) := by tauto
    simp only [h, h', ite_false]

/-- Reversing the last two vertices of an ordered triangle preserves its weighted sum. -/
theorem orderedTriangleSum_swap (G : SimpleGraph V) (w : V → ℝ)
    (F : V → V → V → ℝ) :
    orderedTriangleSum G w (fun x y z ↦ F x z y) = orderedTriangleSum G w F := by
  classical
  unfold orderedTriangleSum
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro y _
  have h : (G.Adj x y ∧ G.Adj y z ∧ G.Adj z x) ↔
      (G.Adj x z ∧ G.Adj z y ∧ G.Adj y x) := by
    constructor <;> rintro ⟨h₁, h₂, h₃⟩
    · exact ⟨h₃.symm, h₂.symm, h₁.symm⟩
    · exact ⟨h₃.symm, h₂.symm, h₁.symm⟩
  simp only [h]
  split_ifs <;> ring

/-- Ordered-triangle summation is additive. -/
theorem orderedTriangleSum_add (G : SimpleGraph V) (w : V → ℝ)
    (F H : V → V → V → ℝ) :
    orderedTriangleSum G w (fun x y z ↦ F x y z + H x y z) =
      orderedTriangleSum G w F + orderedTriangleSum G w H := by
  classical
  simp only [orderedTriangleSum, mul_add, ite_add_zero, Finset.sum_add_distrib]

/-- Nonnegative vertex weights make ordered-triangle summation monotone. -/
theorem orderedTriangleSum_mono (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {F H : V → V → V → ℝ}
    (h : ∀ x y z, G.Adj x y → G.Adj y z → G.Adj z x → F x y z ≤ H x y z) :
    orderedTriangleSum G w F ≤ orderedTriangleSum G w H := by
  classical
  apply Finset.sum_le_sum
  intro x _
  apply Finset.sum_le_sum
  intro y _
  apply Finset.sum_le_sum
  intro z _
  split_ifs with ht
  · exact mul_le_mul_of_nonneg_left (h x y z ht.1 ht.2.1 ht.2.2)
      (mul_nonneg (mul_nonneg (hw x) (hw y)) (hw z))
  · exact le_rfl

/-- Finite expectation commutes with weighted ordered-triangle summation. -/
theorem FiniteLaw.expectation_orderedTriangleSum (μ : FiniteLaw Ω) (G : SimpleGraph V)
    (w : V → ℝ) (F : Ω → V → V → V → ℝ) :
    μ.expectation (fun ω ↦ orderedTriangleSum G w (F ω)) =
      orderedTriangleSum G w (fun x y z ↦ μ.expectation (fun ω ↦ F ω x y z)) := by
  classical
  simp only [orderedTriangleSum, μ.expectation_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  by_cases ht : G.Adj x y ∧ G.Adj y z ∧ G.Adj z x
  · simp [ht, μ.expectation_smul]
  · simp only [ht, ite_false, μ.expectation_const]

open Classical in
/-- The indicator of a failure is bounded by the sum of the individual failure indicators. -/
theorem indicator_not_forall_le_sum {ι : Type*} [Fintype ι] (P : ι → Prop) :
    (if ∀ i, P i then (0 : ℝ) else 1) ≤ ∑ i, if P i then 0 else 1 := by
  classical
  by_cases h : ∀ i, P i
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [ite_eq_right h]
    calc
      (1 : ℝ) = if P i then 0 else 1 := by simp [hi]
      _ ≤ ∑ j, if P j then (0 : ℝ) else 1 :=
        by
          apply Finset.single_le_sum (f := fun j ↦ if P j then (0 : ℝ) else 1)
            (s := Finset.univ) (a := i)
          · intro j _
            split_ifs <;> norm_num
          · exact Finset.mem_univ i

omit [Fintype V] in
open Classical in
/-- Failure to retain a triangle is covered by three corner and six incidence failures. -/
theorem triangleRetained_indicator_le (label : V → V → L) (keep : V → V → Prop)
    (x y z : V) :
    (if TriangleRetained label keep x y z then (0 : ℝ) else 1) ≤
      (if label x y = label x z then 0 else 1) +
      (if label y x = label y z then 0 else 1) +
      (if label z x = label z y then 0 else 1) +
      (if keep x y then 0 else 1) + (if keep y x then 0 else 1) +
      (if keep y z then 0 else 1) + (if keep z y then 0 else 1) +
      (if keep z x then 0 else 1) + (if keep x z then 0 else 1) := by
  classical
  convert indicator_not_forall_le_sum
    ![label x y = label x z, label y x = label y z, label z x = label z y,
      keep x y, keep y x, keep y z, keep z y, keep z x, keep x z] using 1 <;>
    simp [TriangleRetained, Fin.forall_fin_succ, Fin.sum_univ_succ, and_assoc, add_assoc]
  congr 20

/-- The opposite cyclic rotation also preserves ordered-triangle summation. -/
theorem orderedTriangleSum_rotate_twice (G : SimpleGraph V) (w : V → ℝ)
    (F : V → V → V → ℝ) :
    orderedTriangleSum G w (fun x y z ↦ F z x y) = orderedTriangleSum G w F := by
  calc
    _ = orderedTriangleSum G w (fun x y z ↦ F y z x) :=
      orderedTriangleSum_rotate G w (fun x y z ↦ F y z x)
    _ = _ := orderedTriangleSum_rotate G w F

/-- Swapping the first two vertices preserves ordered-triangle summation. -/
theorem orderedTriangleSum_swap_first (G : SimpleGraph V) (w : V → ℝ)
    (F : V → V → V → ℝ) :
    orderedTriangleSum G w (fun x y z ↦ F y x z) = orderedTriangleSum G w F := by
  calc
    _ = orderedTriangleSum G w (fun x y z ↦ F z x y) :=
      orderedTriangleSum_swap G w (fun x y z ↦ F z x y)
    _ = _ := orderedTriangleSum_rotate_twice G w F

/-- Swapping the outside vertices preserves ordered-triangle summation. -/
theorem orderedTriangleSum_reverse (G : SimpleGraph V) (w : V → ℝ)
    (F : V → V → V → ℝ) :
    orderedTriangleSum G w (fun x y z ↦ F z y x) = orderedTriangleSum G w F := by
  calc
    _ = orderedTriangleSum G w (fun x y z ↦ F y x z) :=
      orderedTriangleSum_rotate G w (fun x y z ↦ F y x z)
    _ = _ := orderedTriangleSum_swap_first G w F

open Classical in
/-- The splitting loss is the ordered weighted sum of the triangle failure indicator. -/
theorem splitGraph_triangleMass_loss_eq_ordered [Fintype L] (G : SimpleGraph V)
    (label : V → V → L) (keep : V → V → Prop) (w : V → ℝ) :
    6 * (triangleMass G w - triangleMass (splitGraph G label keep) (fun a ↦ w a.1)) =
      orderedTriangleSum G w
        (fun x y z ↦ if TriangleRetained label keep x y z then 0 else 1) := by
  classical
  rw [splitGraph_triangleMass_loss]
  simp only [orderedTriangleSum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  by_cases ht : G.Adj x y ∧ G.Adj y z ∧ G.Adj z x <;>
    by_cases hr : TriangleRetained label keep x y z <;> simp_all

open Classical in
/-- Three identical corner terms and six identical directed incidence terms bound the loss. -/
theorem splitGraph_triangleMass_loss_le [Fintype L] (G : SimpleGraph V)
    (label : V → V → L) (keep : V → V → Prop) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) :
    6 * (triangleMass G w - triangleMass (splitGraph G label keep) (fun a ↦ w a.1)) ≤
      3 * orderedTriangleSum G w (fun x y z ↦ if label x y = label x z then 0 else 1) +
      6 * orderedTriangleSum G w (fun x y _ ↦ if keep x y then 0 else 1) := by
  classical
  rw [splitGraph_triangleMass_loss_eq_ordered]
  have h := orderedTriangleSum_mono G hw (fun x y z _ _ _ ↦
    triangleRetained_indicator_le label keep x y z)
  let D : V → V → V → ℝ := fun x y z ↦ if label x y = label x z then 0 else 1
  let R : V → V → V → ℝ := fun x y _ ↦ if keep x y then 0 else 1
  change orderedTriangleSum G w _ ≤ orderedTriangleSum G w (fun x y z ↦
    D x y z + D y x z + D z x y + R x y z + R y x z + R y z x + R z y x +
      R z x y + R x z y) at h
  simp only [orderedTriangleSum_add,
    orderedTriangleSum_swap_first G w D, orderedTriangleSum_rotate_twice G w D,
    orderedTriangleSum_swap_first G w R, orderedTriangleSum_rotate G w R,
    orderedTriangleSum_reverse G w R, orderedTriangleSum_rotate_twice G w R,
    orderedTriangleSum_swap G w R] at h
  change orderedTriangleSum G w _ ≤ 3 * orderedTriangleSum G w D +
    6 * orderedTriangleSum G w R
  linarith

open Classical in
/-- Expected splitting loss is controlled by a single weighted corner and incidence. -/
theorem FiniteLaw.expected_splitGraph_triangleMass_loss_le [Fintype L]
    (μ : FiniteLaw Ω) (G : SimpleGraph V) (label : Ω → V → V → L)
    (keep : Ω → V → V → Prop) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    6 * μ.expectation (fun ω ↦ triangleMass G w -
      triangleMass (splitGraph G (label ω) (keep ω)) (fun a ↦ w a.1)) ≤
      3 * orderedTriangleSum G w
        (fun x y z ↦ μ.expectation (fun ω ↦ if label ω x y = label ω x z then 0 else 1)) +
      6 * orderedTriangleSum G w
        (fun x y _ ↦ μ.expectation (fun ω ↦ if keep ω x y then 0 else 1)) := by
  classical
  have h := μ.expectation_mono_support (fun ω _ ↦
    splitGraph_triangleMass_loss_le G (label ω) (keep ω) hw)
  simpa only [μ.expectation_smul, μ.expectation_add,
    μ.expectation_orderedTriangleSum] using h

end Cliquefree
