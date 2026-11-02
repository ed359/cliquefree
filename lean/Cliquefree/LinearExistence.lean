module

public import Cliquefree.Existence
public import Cliquefree.LinearImprovement
public import Cliquefree.LinearExistenceReduction

/-!
# The weighted existence theorem with inverse-linear clique dependence

The sparse neighborhood restriction rules out triangle witnesses at positive maximizers
using scale $K=24r$. The triangle dichotomy and compactness induction then give the weighted
existence bound with rational coefficient $c_r=1/(1+1152B_0r)=\Theta(1/r)$.
-/

@[expose] public section

noncomputable section

universe u

namespace Cliquefree

/-- At scale $K=24r$ a positive global maximizer cannot have a triangle witness. -/
theorem linear_no_triangleWitness_at_maximizer {V : Type u} [Fintype V]
    (G : SimpleGraph V) {a w : V → ℝ} {r : ℕ} (hr : 2 ≤ r)
    (hG : G.CliqueFree r) (ha : ∀ v, 0 < a v) (hw : ∀ v, 0 < w v)
    (hmax : ∀ q : V → ℝ, (∀ v, 0 ≤ q v) →
      graphPotential G a q ≤ graphPotential G a w) :
    ¬Nonempty (TriangleWitness G (stationaryScale (linearCliqueScale r) a w) w) := by
  rintro ⟨W⟩
  have hK : (0 : ℝ) < linearCliqueScale r := by
    exact_mod_cast linearCliqueScale_pos (show 1 ≤ r by omega)
  have hθ := stationaryScale_pos hK ha hw
  have hz := positive_maximizer_stationary G ha hw
    (fun q hq ↦ hmax q (fun v ↦ (hq v).le))
  have hbudget (v : V) :
      24 * (r : ℝ) * scalarXi (a v) (w v) ≤
        stationaryScale (linearCliqueScale r) a w v * w v := by
    rw [stationaryScale_mul hw]
    norm_num [linearCliqueScale]
  obtain ⟨q, hq, hgain⟩ :=
    exists_stationary_linear_improvement G ha hw hθ hr hG hz hbudget W
  exact (not_lt_of_ge (hmax q hq)) hgain

/-- A global maximizer obeys both triangle bounds at scale $K=24r$. -/
theorem linear_triangles_at_maximizer {V : Type u} [Fintype V]
    (G : SimpleGraph V) {a w : V → ℝ} {r : ℕ} (hr : 2 ≤ r)
    (hG : G.CliqueFree r) (ha : ∀ v, 0 < a v) (hw : ∀ v, 0 < w v)
    (hmax : ∀ q : V → ℝ, (∀ v, 0 ≤ q v) →
      graphPotential G a q ≤ graphPotential G a w) :
    triangleMass G w ≤ (triangleBoundConstant : ℝ) *
        scaledDegreeBudget G (stationaryScale (linearCliqueScale r) a w) w ∧
      (triangleBoundConstant : ℝ) *
        scaledDegreeBudget G (stationaryScale (linearCliqueScale r) a w) w ≤
        (triangleBoundConstant : ℝ) * (linearCliqueScale r : ℝ) * objectiveMass a w := by
  have hK : (0 : ℝ) < linearCliqueScale r := by
    exact_mod_cast linearCliqueScale_pos (show 1 ≤ r by omega)
  have hz := positive_maximizer_stationary G ha hw
    (fun q hq ↦ hmax q (fun v ↦ (hq v).le))
  constructor
  · rcases triangle_dichotomy V G _ w (stationaryScale_pos hK ha hw) hw with h | h
    · exact h
    · exact (linear_no_triangleWitness_at_maximizer G hr hG ha hw hmax h).elim
  · have hB : (0 : ℝ) ≤ triangleBoundConstant := by
      exact_mod_cast triangleBoundConstant_pos.le
    exact (mul_le_mul_of_nonneg_left
      (stationary_degree_budget_le G hK.le ha hw hz) hB).trans_eq (mul_assoc _ _ _).symm

/-- The stationary triangle estimate at scale $K=24r$ holds for every finite clique-free graph. -/
theorem linear_stationary_triangle_bound {r : ℕ} (hr : 2 ≤ r) :
    LinearStationaryTriangleBound.{u} r := by
  intro V inst G a w hG ha hw hmax
  have h := linear_triangles_at_maximizer G hr hG ha hw hmax
  exact h.1.trans h.2

/-- The prescribed-weight existence inequality with the inverse-linear rational coefficient. -/
theorem linear_weighted_independence_bound {V : Type u} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (hr : 2 ≤ r) {u s : V → ℝ}
    (hG : G.CliqueFree r) (hu : ∀ v, 0 ≤ u v) (hs : ∀ v, 0 < s v) :
    (linearExistenceConstant r : ℝ) * benchmark G u s ≤ independenceWeight G u :=
  linear_prescribed_bound_of_stationary_triangle_bound
    (linear_stationary_triangle_bound hr) G hG hu hs

/-- An independent set attains the guaranteed objective weight. -/
theorem linear_exists_independent_set_bound {V : Type u} [Fintype V]
    (G : SimpleGraph V) {r : ℕ} (hr : 2 ≤ r) {u s : V → ℝ}
    (hG : G.CliqueFree r) (hu : ∀ v, 0 ≤ u v) (hs : ∀ v, 0 < s v) :
    ∃ I : Finset V, Independent G I ∧
      (linearExistenceConstant r : ℝ) * benchmark G u s ≤ weightSum u I := by
  obtain ⟨I, hI, heq⟩ := independenceWeight_attained G u
  exact ⟨I, hI, heq ▸ linear_weighted_independence_bound G hr hG hu hs⟩

/-- The existence theorem with rational positive coefficients of order $1/r$. -/
theorem existenceTheorem :
    ∃ c : ℕ → ℚ, (∀ r : ℕ, 4 ≤ r → 0 < c r) ∧
      (∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ r : ℕ, 4 ≤ r →
        A / (r : ℝ) ≤ (c r : ℝ) ∧ (c r : ℝ) ≤ B / (r : ℝ)) ∧
      ∀ r : ℕ, 4 ≤ r → ∀ (V : Type u) [Fintype V] (G : SimpleGraph V) (s a : V → ℝ),
        G.CliqueFree r → (∀ v, 0 < s v) → (∀ v, 0 ≤ a v) →
          (c r : ℝ) * benchmark G a s ≤ independenceWeight G a := by
  refine ⟨linearExistenceConstant, fun r _ ↦ linearExistenceConstant_pos r,
    linearExistenceConstant_order_inverse, ?_⟩
  intro r hr V inst G s a hG hs ha
  exact linear_weighted_independence_bound G (by omega) hG ha hs

end Cliquefree
