module

public import Cliquefree.TriangleBasics
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Pruning edges with small common neighborhoods

Finite edge deletion preserves the triangle mass minus its scaled degree budget.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- A subgraph has no larger neighborhood masses for nonnegative weights. -/
theorem neighborhoodMass_subgraph_le {G H : SimpleGraph V} (hHG : H ≤ G)
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (x : V) :
    neighborhoodMass H w x ≤ neighborhoodMass G w x := by
  classical
  unfold neighborhoodMass
  apply Finset.sum_le_sum
  intro y _
  by_cases hh : H.Adj x y
  · simp [hh, hHG hh]
  · by_cases hg : G.Adj x y <;> simp [hh, hg, hw y]

/-- A subgraph has no larger degree budget for nonnegative weights and scales. -/
theorem scaledDegreeBudget_subgraph_le {G H : SimpleGraph V} (hHG : H ≤ G)
    {θ w : V → ℝ} (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v) :
    scaledDegreeBudget H θ w ≤ scaledDegreeBudget G θ w := by
  apply Finset.sum_le_sum
  intro x _
  exact mul_le_mul_of_nonneg_left (neighborhoodMass_subgraph_le hHG hw x)
    (mul_nonneg (hθ x) (hw x))

/-- A cyclic change of variables preserves an ordered triple sum. -/
theorem sum_triple_rotate (F : V → V → V → ℝ) :
    (∑ a, ∑ b, ∑ c, F b c a) = ∑ a, ∑ b, ∑ c, F a b c := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.sum_comm]

/-- An ordered sum supported on a single unordered pair has its two orientations. -/
theorem sum_single_unordered_pair [DecidableEq V] (F : V → V → ℝ) {x y : V} (hxy : x ≠ y) :
    (∑ a, ∑ b, if s(a, b) = s(x, y) then F a b else 0) = F x y + F y x := by
  classical
  have hp (a b : V) :
      (if s(a, b) = s(x, y) then F a b else 0) =
        (if a = x ∧ b = y then F a b else 0) +
        (if a = y ∧ b = x then F a b else 0) := by
    simp only [Sym2.eq_iff]
    by_cases hax : a = x <;> by_cases hay : a = y <;>
      by_cases hbx : b = x <;> by_cases hby : b = y <;> simp_all
  simp_rw [hp, Finset.sum_add_distrib]
  simp [ite_and]

/-- Every triangle lost in a subgraph contains a deleted edge, giving a weighted union bound. -/
theorem triangleMass_subgraph_loss (G H : SimpleGraph V) [DecidableRel G.Adj]
    [DecidableRel H.Adj] {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) :
    triangleMass G w ≤ triangleMass H w +
      (∑ a, ∑ b, if G.Adj a b ∧ ¬H.Adj a b then
        w a * w b * commonNeighborhoodMass G w a b else 0) / 2 := by
  classical
  let E (a b c : V) : ℝ :=
    if G.Adj a b ∧ G.Adj b c ∧ G.Adj c a ∧ ¬H.Adj a b then
      w a * w b * w c else 0
  have hpoint (a b c : V) :
      (if G.Adj a b ∧ G.Adj b c ∧ G.Adj c a then w a * w b * w c else 0) ≤
      (if H.Adj a b ∧ H.Adj b c ∧ H.Adj c a then w a * w b * w c else 0) +
        E a b c + E b c a + E c a b := by
    have hp := mul_nonneg (mul_nonneg (hw a) (hw b)) (hw c)
    have hcycle₁ : w b * w c * w a = w a * w b * w c := by ring
    have hcycle₂ : w c * w a * w b = w a * w b * w c := by ring
    by_cases h₁ : G.Adj a b <;> by_cases h₂ : G.Adj b c <;>
      by_cases h₃ : G.Adj c a <;> by_cases h₄ : H.Adj a b <;>
      by_cases h₅ : H.Adj b c <;> by_cases h₆ : H.Adj c a <;>
      simp [E, h₁, h₂, h₃, h₄, h₅, h₆, hcycle₁, hcycle₂] <;> linarith
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun a _ ↦
    Finset.sum_le_sum (s := Finset.univ) (fun b _ ↦
      Finset.sum_le_sum (s := Finset.univ) (fun c _ ↦ hpoint a b c)))
  simp only [Finset.sum_add_distrib] at hsum
  have hrot₂ : (∑ a, ∑ b, ∑ c, E c a b) = ∑ a, ∑ b, ∑ c, E a b c := by
    rw [sum_triple_rotate (fun a b c ↦ E b c a), sum_triple_rotate]
  rw [sum_triple_rotate E, hrot₂] at hsum
  have hE : (∑ a, ∑ b, ∑ c, E a b c) =
      ∑ a, ∑ b, if G.Adj a b ∧ ¬H.Adj a b then
        w a * w b * commonNeighborhoodMass G w a b else 0 := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases hg : G.Adj a b <;> by_cases hh : H.Adj a b
    · simp [E, hh]
    · simp only [hg, hh, not_false_eq_true, and_self, ite_true,
        commonNeighborhoodMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c _
      by_cases ha : G.Adj a c <;> by_cases hb : G.Adj b c <;>
        simp [E, hg, hh, ha, hb, G.adj_comm]
    · simp [E, hg]
    · simp [E, hg]
  rw [hE] at hsum
  unfold triangleMass
  convert (div_le_div_of_nonneg_right hsum (by norm_num : (0 : ℝ) ≤ 6)) using 1 <;> ring_nf

/-- Removing one edge loses at most its endpoint weights times its common-neighbor mass. -/
theorem triangleMass_delete_edge_le (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {x y : V} (hxy : G.Adj x y) :
    triangleMass G w ≤ triangleMass (G.deleteEdges {s(x, y)}) w +
      w x * w y * commonNeighborhoodMass G w x y := by
  classical
  have h := triangleMass_subgraph_loss G (G.deleteEdges {s(x, y)}) hw
  have hp (a b : V) :
      (if G.Adj a b ∧ ¬(G.deleteEdges {s(x, y)}).Adj a b then
        w a * w b * commonNeighborhoodMass G w a b else 0) =
      (if s(a, b) = s(x, y) then w a * w b * commonNeighborhoodMass G w a b else 0) := by
    by_cases he : s(a, b) = s(x, y)
    · have hab : G.Adj a b := by
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxy
        · exact hxy.symm
      simp [SimpleGraph.deleteEdges_adj, he, hab]
    · simp [SimpleGraph.deleteEdges_adj, he]
  simp_rw [hp] at h
  rw [sum_single_unordered_pair _ hxy.ne, commonNeighborhoodMass_comm G w y x] at h
  nlinarith only [h]

/-- Removing one edge decreases the degree budget by the sum of its two endpoint charges. -/
theorem scaledDegreeBudget_delete_edge (G : SimpleGraph V) (θ w : V → ℝ)
    {x y : V} (hxy : G.Adj x y) :
    scaledDegreeBudget G θ w = scaledDegreeBudget (G.deleteEdges {s(x, y)}) θ w +
      w x * w y * (θ x + θ y) := by
  classical
  have hp (a b : V) :
      (if G.Adj a b then θ a * w a * w b else 0) =
      (if (G.deleteEdges {s(x, y)}).Adj a b then θ a * w a * w b else 0) +
      (if s(a, b) = s(x, y) then θ a * w a * w b else 0) := by
    by_cases he : s(a, b) = s(x, y)
    · have hab : G.Adj a b := by
        rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hxy
        · exact hxy.symm
      simp [SimpleGraph.deleteEdges_adj, he, hab]
    · simp [SimpleGraph.deleteEdges_adj, he]
  simp only [scaledDegreeBudget, neighborhoodMass, Finset.mul_sum, mul_ite, mul_zero]
  simp_rw [hp]
  simp_rw [Finset.sum_add_distrib]
  rw [sum_single_unordered_pair _ hxy.ne]
  ring

/-- Deleting an edge below the common-neighbor threshold preserves the pruning potential. -/
theorem pruning_potential_delete_edge (G : SimpleGraph V) {θ w : V → ℝ}
    (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v) {t : ℝ} (ht : 0 < t)
    {x y : V} (hxy : G.Adj x y)
    (hbad : commonNeighborhoodMass G w x y ≤ max (θ x) (θ y) / t) :
    triangleMass G w - scaledDegreeBudget G θ w / t ≤
      triangleMass (G.deleteEdges {s(x, y)}) w -
        scaledDegreeBudget (G.deleteEdges {s(x, y)}) θ w / t := by
  have hmax : max (θ x) (θ y) ≤ θ x + θ y :=
    max_le (le_add_of_nonneg_right (hθ y)) (le_add_of_nonneg_left (hθ x))
  have hc : commonNeighborhoodMass G w x y ≤ (θ x + θ y) / t :=
    hbad.trans (div_le_div_of_nonneg_right hmax ht.le)
  have hm := mul_le_mul_of_nonneg_left hc (mul_nonneg (hw x) (hw y))
  have hT := triangleMass_delete_edge_le G hw hxy
  rw [scaledDegreeBudget_delete_edge G θ w hxy, add_div]
  rw [← mul_div_assoc] at hm
  linarith only [hT, hm]

/-- Repeated pruning terminates and preserves triangle mass minus budget divided by threshold. -/
theorem exists_pruned_subgraph (G : SimpleGraph V) {θ w : V → ℝ}
    (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v) {t : ℝ} (ht : 0 < t) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ x y, H.Adj x y → max (θ x) (θ y) / t ≤ commonNeighborhoodMass H w x y) ∧
      triangleMass G w - scaledDegreeBudget G θ w / t ≤
        triangleMass H w - scaledDegreeBudget H θ w / t := by
  classical
  suffices hall : ∀ n : ℕ, ∀ J : SimpleGraph V, J.edgeFinset.card = n →
      ∃ H : SimpleGraph V, H ≤ J ∧
        (∀ x y, H.Adj x y → max (θ x) (θ y) / t ≤ commonNeighborhoodMass H w x y) ∧
        triangleMass J w - scaledDegreeBudget J θ w / t ≤
          triangleMass H w - scaledDegreeBudget H θ w / t from hall _ G rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro J hn
    by_cases hdone : ∀ x y, J.Adj x y →
        max (θ x) (θ y) / t ≤ commonNeighborhoodMass J w x y
    · exact ⟨J, le_rfl, hdone, le_rfl⟩
    push Not at hdone
    obtain ⟨x, y, hxy, hbad⟩ := hdone
    let K := J.deleteEdges {s(x, y)}
    have hKJ : K ≤ J := SimpleGraph.deleteEdges_le _
    have hlt : K < J := by
      refine lt_iff_le_not_ge.mpr ⟨hKJ, ?_⟩
      intro hback
      have hk := hback hxy
      simp [K, SimpleGraph.deleteEdges_adj] at hk
    have hc : K.edgeFinset.card < n := by
      rw [← hn]
      exact Finset.card_lt_card (SimpleGraph.edgeFinset_strict_mono hlt)
    obtain ⟨H, hHK, hH, hpot⟩ := ih _ hc K (by congr 1; ext e; simp)
    refine ⟨H, hHK.trans hKJ, hH, ?_⟩
    exact (pruning_potential_delete_edge J hθ hw ht hxy hbad.le).trans hpot

/-- The prepared subgraph retains triangle mass and decreases every load and budget. -/
theorem exists_prepared_subgraph (G : SimpleGraph V) {θ w : V → ℝ}
    (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v) {t : ℝ} (ht : 0 < t) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ x y, H.Adj x y → max (θ x) (θ y) / t ≤ commonNeighborhoodMass H w x y) ∧
      triangleMass G w - scaledDegreeBudget G θ w / t ≤ triangleMass H w ∧
      scaledDegreeBudget H θ w ≤ scaledDegreeBudget G θ w ∧
      ∀ v, neighborhoodMass H w v ≤ neighborhoodMass G w v := by
  obtain ⟨H, hHG, hC, hpot⟩ := exists_pruned_subgraph G hθ hw ht
  refine ⟨H, hHG, hC, ?_, scaledDegreeBudget_subgraph_le hHG hθ hw,
    neighborhoodMass_subgraph_le hHG hw⟩
  have hD := div_nonneg (scaledDegreeBudget_nonneg H hθ hw) ht.le
  linarith only [hpot, hD]

/-- Positive triangle mass implies that the graph contains an edge. -/
theorem exists_adj_of_triangleMass_pos (G : SimpleGraph V) (w : V → ℝ)
    (hT : 0 < triangleMass G w) : ∃ x y, G.Adj x y := by
  classical
  by_contra hn
  push Not at hn
  simp [triangleMass, hn] at hT

/-- An edge gives strictly positive degree budget when all weights and scales are positive. -/
theorem scaledDegreeBudget_pos_of_adj (G : SimpleGraph V) {θ w : V → ℝ}
    (hθ : ∀ v, 0 < θ v) (hw : ∀ v, 0 < w v) {x y : V} (hxy : G.Adj x y) :
    0 < scaledDegreeBudget G θ w := by
  classical
  have hL : 0 < neighborhoodMass G w x := by
    apply Finset.sum_pos'
    · intro v _
      split_ifs
      · exact (hw v).le
      · exact le_rfl
    · exact ⟨y, Finset.mem_univ y, by simp [hxy, hw y]⟩
  apply Finset.sum_pos'
  · intro v _
    exact mul_nonneg (mul_nonneg (hθ v).le (hw v).le)
      (neighborhoodMass_nonneg G (fun z ↦ (hw z).le) v)
  · exact ⟨x, Finset.mem_univ x, mul_pos (mul_pos (hθ x) (hw x)) hL⟩

/-- Preparation from more than twice the budget retains positive budget and excess triangles. -/
theorem exists_prepared_subgraph_positive (G : SimpleGraph V) {θ w : V → ℝ}
    (hθ : ∀ v, 0 < θ v) (hw : ∀ v, 0 < w v) {t : ℝ} (ht : 1 ≤ t)
    (hD : 0 < scaledDegreeBudget G θ w)
    (hT : 2 * scaledDegreeBudget G θ w < triangleMass G w) :
    ∃ H : SimpleGraph V, H ≤ G ∧
      (∀ x y, H.Adj x y → max (θ x) (θ y) / t ≤ commonNeighborhoodMass H w x y) ∧
      triangleMass G w - scaledDegreeBudget G θ w / t ≤ triangleMass H w ∧
      scaledDegreeBudget H θ w ≤ scaledDegreeBudget G θ w ∧
      0 < scaledDegreeBudget H θ w ∧ scaledDegreeBudget H θ w < triangleMass H w := by
  obtain ⟨H, hHG, hC, hmass, hbudget, _⟩ := exists_prepared_subgraph G
    (fun v ↦ (hθ v).le) (fun v ↦ (hw v).le) (lt_of_lt_of_le zero_lt_one ht)
  have hdiv : scaledDegreeBudget G θ w / t ≤ scaledDegreeBudget G θ w :=
    div_le_self hD.le ht
  have hTH : scaledDegreeBudget G θ w < triangleMass H w := by
    linarith only [hT, hmass, hdiv]
  obtain ⟨x, y, hxy⟩ := exists_adj_of_triangleMass_pos H w (hD.trans hTH)
  exact ⟨H, hHG, hC, hmass, hbudget, scaledDegreeBudget_pos_of_adj H hθ hw hxy,
    hbudget.trans_lt hTH⟩

end Cliquefree
