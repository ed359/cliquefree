module

public import Cliquefree.LinearConstants
public import Cliquefree.Reductions
public import Cliquefree.BoundaryLimits
public import Cliquefree.Stationary

/-!
# Compactness induction for the inverse-linear existence coefficient

Deletion and compactness induction at scale $K=24r$ establish the weighted existence bound,
conditional on the corresponding stationary triangle estimate.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe u

namespace Cliquefree

section FiniteReductions

variable {V : Type*} [Fintype V]

/-- Removing a zero-objective vertex reduces the existence bound to a smaller graph. -/
theorem linear_zero_objective_existence_step [DecidableEq V] (G : SimpleGraph V) (r : ℕ)
    {u : V → ℝ} (hu : ∀ v, 0 ≤ u v) {x : V} (hx : u x = 0)
    (hsmall : (linearExistenceConstant r : ℝ) *
      extremalBenchmark (G.induce ((Finset.univ.erase x : Finset V) : Set V)) (fun v ↦ u v) ≤
      independenceWeight (G.induce ((Finset.univ.erase x : Finset V) : Set V))
        (fun v ↦ u v)) :
    (linearExistenceConstant r : ℝ) * extremalBenchmark G u ≤ independenceWeight G u := by
  have hz : ∀ v, v ∉ (Finset.univ : Finset V).erase x → u v = 0 := by
    intro v hv
    have he : v = x := by simpa using hv
    simpa [he] using hx
  have hc : 0 ≤ (linearExistenceConstant r : ℝ) := by
    exact_mod_cast (linearExistenceConstant_pos r).le
  have hF := mul_le_mul_of_nonneg_left
    (extremalBenchmark_le_induce_of_zero_outside G (Finset.univ.erase x) hu hz) hc
  have hα := independenceWeight_induce_le G (Finset.univ.erase x) u
  exact hF.trans (hsmall.trans hα)

/-- The extremal independent-set bound holds when the vertex type is empty. -/
theorem linear_empty_extremal_bound [IsEmpty V] (G : SimpleGraph V) (r : ℕ)
    (u : V → ℝ) :
    (linearExistenceConstant r : ℝ) * extremalBenchmark G u ≤ independenceWeight G u := by
  have hu : ∀ v, 0 ≤ u v := fun v ↦ isEmptyElim v
  have hF : extremalBenchmark G u ≤ 0 := by simpa using extremalBenchmark_le_total G hu
  have hc : 0 ≤ (linearExistenceConstant r : ℝ) := by
    exact_mod_cast (linearExistenceConstant_pos r).le
  have hmul := mul_nonpos_of_nonneg_of_nonpos hc hF
  exact hmul.trans (independenceWeight_nonneg G u)


/-- Induction on the remaining vertices proves the bound when an isolated vertex is present. -/
theorem linear_isolated_existence_step [DecidableEq V] (G : SimpleGraph V) (r : ℕ)
    {u : V → ℝ} (hu : ∀ v, 0 ≤ u v) {x : V} (hx : ∀ y, ¬G.Adj x y)
    (hsmall : (linearExistenceConstant r : ℝ) *
      extremalBenchmark (G.induce ((Finset.univ.erase x : Finset V) : Set V)) (fun v ↦ u v) ≤
      independenceWeight (G.induce ((Finset.univ.erase x : Finset V) : Set V))
        (fun v ↦ u v)) :
    (linearExistenceConstant r : ℝ) * extremalBenchmark G u ≤ independenceWeight G u := by
  have hc : 0 ≤ (linearExistenceConstant r : ℝ) := by
    exact_mod_cast (linearExistenceConstant_pos r).le
  have hf := mul_le_mul_of_nonneg_left (extremalBenchmark_erase_isolated_le G hu hx) hc
  have hx' := mul_le_of_le_one_left (hu x) (linearExistenceConstant_real_le_one r)
  have hsel := selection_isolated_independenceWeight_le G u hx
  nlinarith only [hf, hx', hsmall, hsel]


/-- A triangle bound at a stationary vector gives a vertex with nonnegative deletion reward. -/
theorem linear_exists_nonnegative_deletionReward [Nonempty V] (G : SimpleGraph V) {u w : V → ℝ}
    (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v) (r : ℕ)
    (hz : ∀ v, residual G u w v = 0)
    (hT : triangleMass G w ≤
      (triangleBoundConstant : ℝ) * (linearCliqueScale r : ℝ) * objectiveMass u w) :
    ∃ x, 0 ≤ deletionReward G u w (linearExistenceConstant r : ℝ) x := by
  apply exists_nonnegative_of_weighted_sum hw
  rw [averaged_deletion_reward_stationary G hu hw _ hz]
  have hc : 0 ≤ (linearExistenceConstant r : ℝ) := by
    exact_mod_cast (linearExistenceConstant_pos r).le
  have hS := (objectiveMass_pos hu hw).le
  have hmul := mul_le_mul_of_nonneg_left hT (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) hc)
  have hslack := linearExistenceConstant_real_existence_slack r
  nlinarith [mul_nonneg hslack hS]


/-- The interior induction step follows from stationarity, a triangle bound, and smaller cases. -/
theorem linear_independence_bound_of_stationary_triangle_bound [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) {u w : V → ℝ} (hu : ∀ v, 0 < u v) (hw : ∀ v, 0 < w v)
    (r : ℕ) (hz : ∀ v, residual G u w v = 0)
    (hT : triangleMass G w ≤
      (triangleBoundConstant : ℝ) * (linearCliqueScale r : ℝ) * objectiveMass u w)
    (hsmall : ∀ x : V, (linearExistenceConstant r : ℝ) *
      extremalBenchmark
        (G.induce ((Finset.univ \ closedNeighborhood G x : Finset V) : Set V))
        (fun v ↦ u v) ≤
      independenceWeight
        (G.induce ((Finset.univ \ closedNeighborhood G x : Finset V) : Set V))
        (fun v ↦ u v)) :
    (linearExistenceConstant r : ℝ) * graphPotential G u w ≤ independenceWeight G u := by
  obtain ⟨x, hx⟩ := linear_exists_nonnegative_deletionReward G hu hw r hz hT
  let A := Finset.univ \ closedNeighborhood G x
  let H := G.induce (A : Set V)
  have hc : 0 ≤ (linearExistenceConstant r : ℝ) := by
    exact_mod_cast (linearExistenceConstant_pos r).le
  have hp : graphPotential G u (eraseWeights w (closedNeighborhood G x)) ≤
      extremalBenchmark H (fun v ↦ u v) := by
    rw [graphPotential_eraseWeights_eq_induce]
    convert graphPotential_le_extremalBenchmark H (fun v ↦ (hu v).le)
      (fun v ↦ hw v) using 1
  calc
    (linearExistenceConstant r : ℝ) * graphPotential G u w ≤
        u x + (linearExistenceConstant r : ℝ) *
          graphPotential G u (eraseWeights w (closedNeighborhood G x)) := by
      unfold deletionReward at hx
      linarith
    _ ≤ u x + (linearExistenceConstant r : ℝ) * extremalBenchmark H (fun v ↦ u v) :=
      by nlinarith only [mul_le_mul_of_nonneg_left hp hc]
    _ ≤ u x + independenceWeight H (fun v ↦ u v) := by
      have hi : (linearExistenceConstant r : ℝ) * extremalBenchmark H (fun v ↦ u v) ≤
          independenceWeight H (fun v ↦ u v) := by
        convert hsmall x using 1
      linarith only [hi]
    _ ≤ independenceWeight G u := selection_independenceWeight_le G u x


end FiniteReductions

/-- The triangle estimate needed at positive global potential maximizers. -/
def LinearStationaryTriangleBound (r : ℕ) : Prop :=
  ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (a w : V → ℝ),
    G.CliqueFree r → (∀ v, 0 < a v) → (∀ v, 0 < w v) →
    (∀ q : V → ℝ, (∀ v, 0 ≤ q v) → graphPotential G a q ≤ graphPotential G a w) →
    triangleMass G w ≤
      (triangleBoundConstant : ℝ) * (linearCliqueScale r : ℝ) * objectiveMass a w

/-- Compactness and induction turn the stationary triangle estimate into the extremal bound. -/
theorem linear_extremal_bound_of_stationary_triangle_bound {r : ℕ}
    (htri : LinearStationaryTriangleBound.{u} r) {V : Type u} [Fintype V]
    (G : SimpleGraph V) (a : V → ℝ) (hG : G.CliqueFree r) (ha : ∀ v, 0 ≤ a v) :
    (linearExistenceConstant r : ℝ) * extremalBenchmark G a ≤ independenceWeight G a := by
  classical
  suffices h : ∀ n : ℕ, ∀ (W : Type u) [Fintype W], Fintype.card W = n →
      ∀ (H : SimpleGraph W) (b : W → ℝ), H.CliqueFree r → (∀ v, 0 ≤ b v) →
        (linearExistenceConstant r : ℝ) * extremalBenchmark H b ≤ independenceWeight H b by
    exact h (Fintype.card V) V rfl G a hG ha
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro W inst hcard H b hH hb
    have hc : 0 ≤ (linearExistenceConstant r : ℝ) := by
      exact_mod_cast (linearExistenceConstant_pos r).le
    have hsmall (A : Finset W) (hA : A ≠ Finset.univ) :
        (linearExistenceConstant r : ℝ) * extremalBenchmark (H.induce (A : Set W))
          (fun v ↦ b v) ≤ independenceWeight (H.induce (A : Set W)) (fun v ↦ b v) := by
      have hn : Fintype.card (A : Set W) < n := (card_induced_lt hA).trans_eq hcard
      exact ih _ hn (A : Set W) rfl (H.induce (A : Set W)) (fun v ↦ b v)
        (cliqueFree_induce H A hH) (fun v ↦ hb v)
    rcases isEmpty_or_nonempty W with hEmpty | hNonempty
    · let := hEmpty
      exact linear_empty_extremal_bound H r b
    · let := hNonempty
      by_cases hz : ∃ x, b x = 0
      · obtain ⟨x, hx⟩ := hz
        exact linear_zero_objective_existence_step H r hb hx
          (hsmall (Finset.univ.erase x) (erase_univ_ne_univ x))
      have hpos : ∀ v, 0 < b v := by
        intro v
        exact lt_of_le_of_ne (hb v) (fun h ↦ hz ⟨v, h.symm⟩)
      by_cases hiso : ∃ x, ∀ y, ¬H.Adj x y
      · obtain ⟨x, hx⟩ := hiso
        exact linear_isolated_existence_step H r hb hx
          (hsmall (Finset.univ.erase x) (erase_univ_ne_univ x))
      have hno : ∀ v, ∃ y, H.Adj v y := by
        push Not at hiso
        exact hiso
      obtain ⟨s, s₀, hs, _, h₀, hlim, hmax⟩ := exists_normalized_maximizing_limit H hb
      by_cases hfull : ∀ v, 0 < s₀ v
      · have hatt := maximizing_limit_attains H b hfull hlim hmax
        have hsm : ∀ t : W → ℝ, (∀ v, 0 < t v) →
            benchmark H b t ≤ benchmark H b s₀ := by
          intro t ht
          rw [hatt]
          exact benchmark_le_extremalBenchmark H hb ht
        let q := liftedWeights H b s₀
        have hq : ∀ v, 0 < q v := liftedWeights_pos H hpos hfull hno
        have hqm : ∀ z : W → ℝ, (∀ v, 0 ≤ z v) →
            graphPotential H b z ≤ graphPotential H b q :=
          lift_maximizes_nonnegativePotential H hpos hfull hno hsm
        have hqvalue : graphPotential H b q = extremalBenchmark H b :=
          (lifted_maximizer_value H hpos hfull hno hsm).trans hatt
        rw [← hqvalue]
        apply linear_independence_bound_of_stationary_triangle_bound H hpos hq r
          (positive_maximizer_stationary H hpos hq (fun z hz ↦ hqm z (fun v ↦ (hz v).le)))
          (htri W H b q hH hpos hq hqm)
        intro x
        apply hsmall
        intro he
        have hx : x ∈ (Finset.univ \ closedNeighborhood H x : Finset W) := by
          rw [he]
          exact Finset.mem_univ x
        exact (Finset.mem_sdiff.mp hx).2 (mem_closedNeighborhood_self H x)
      · let A := positiveSupport s₀
        let B := boundaryRemainder H A
        have hA : A ≠ Finset.univ := by
          intro he
          apply hfull
          intro v
          have hv : v ∈ A := by rw [he]; exact Finset.mem_univ v
          exact (mem_positiveSupport s₀ v).mp hv
        obtain ⟨x, hx⟩ := simplex_positive_support_nonempty h₀
        have hxA : x ∈ A := (mem_positiveSupport s₀ x).mpr hx
        have hB : B ≠ Finset.univ := by
          intro he
          have hxB : x ∈ B := by rw [he]; exact Finset.mem_univ x
          exact ((mem_boundaryRemainder H A x).mp hxB).1 hxA
        have hAB : Disjoint A B := by
          apply Finset.disjoint_left.mpr
          intro v hvA hvB
          exact ((mem_boundaryRemainder H A v).mp hvB).1 hvA
        have hE : ∀ x ∈ A, ∀ y ∈ B, ¬H.Adj x y := by
          intro x hx y hy hxy
          exact ((mem_boundaryRemainder H A y).mp hy).2 x hx hxy.symm
        have hF : extremalBenchmark H b ≤
            extremalBenchmark (H.induce (A : Set W)) (fun v ↦ b v) +
              extremalBenchmark (H.induce (B : Set W)) (fun v ↦ b v) := by
          exact boundary_decomposition H hb hs h₀.1 hlim hmax
        have hI := independenceWeight_induce_add_le H b hAB hE
        have hIA := hsmall A hA
        have hIB := hsmall B hB
        have hmul := mul_le_mul_of_nonneg_left hF hc
        nlinarith only [hmul, hIA, hIB, hI]

/-- The prescribed-weight existence inequality follows from the same stationary estimate. -/
theorem linear_prescribed_bound_of_stationary_triangle_bound {r : ℕ}
    (htri : LinearStationaryTriangleBound.{u} r) {V : Type u} [Fintype V]
    (G : SimpleGraph V) {a s : V → ℝ} (hG : G.CliqueFree r)
    (ha : ∀ v, 0 ≤ a v) (hs : ∀ v, 0 < s v) :
    (linearExistenceConstant r : ℝ) * benchmark G a s ≤ independenceWeight G a := by
  have hc : 0 ≤ (linearExistenceConstant r : ℝ) := by
    exact_mod_cast (linearExistenceConstant_pos r).le
  exact (mul_le_mul_of_nonneg_left (benchmark_le_extremalBenchmark G ha hs) hc).trans
    (linear_extremal_bound_of_stationary_triangle_bound htri G a hG ha)


end Cliquefree
