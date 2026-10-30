module

public import Cliquefree.Induced

/-!
# Sparse restrictions with linear dependence on clique order

Restricting to a heavy neighborhood lowers the excluded clique order by one and loses at
most a factor `Q` of the mass. After at most `r - 2` such restrictions the remaining graph
is independent, so a sparse nonempty restriction always exists.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*}

/-- The open neighborhood restricted to the current vertex set. -/
def restrictedNeighborhood (G : SimpleGraph V) (S : Finset V) (v : V) : Finset V := by
  classical
  exact S.filter (G.Adj v)

/-- Membership in a restricted neighborhood records membership in the set and adjacency. -/
@[simp] theorem mem_restrictedNeighborhood (G : SimpleGraph V) (S : Finset V) (v x : V) :
    x ∈ restrictedNeighborhood G S v ↔ x ∈ S ∧ G.Adj v x := by
  classical
  simp [restrictedNeighborhood]

/-- A restricted neighborhood lies in the current vertex set. -/
theorem restrictedNeighborhood_subset (G : SimpleGraph V) (S : Finset V) (v : V) :
    restrictedNeighborhood G S v ⊆ S := by
  intro x hx
  exact (mem_restrictedNeighborhood G S v x).mp hx |>.1

/-- A neighborhood inside an induced graph is the corresponding restricted weighted sum. -/
theorem neighborhoodMass_induce_eq_weightSum (G : SimpleGraph V) (A : Finset V)
    (w : V → ℝ) (v : A) :
    neighborhoodMass (G.induce (A : Set V)) (fun x ↦ w x) v =
      weightSum w (restrictedNeighborhood G A v) := by
  classical
  unfold neighborhoodMass
  change (∑ y : A, if G.Adj v y then w y else 0) = _
  rw [Finset.sum_coe_sort A (fun y : V ↦ if G.Adj v y then w y else 0)]
  simp only [weightSum, restrictedNeighborhood, Finset.sum_filter]

/-- A uniform weighted-neighborhood bound controls total edge mass. -/
theorem edgeMass_le_of_neighborhood_bound [Fintype V] (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) {L : ℝ} (hL : ∀ v, neighborhoodMass G w v ≤ L) :
    edgeMass G w ≤ (∑ v, w v) * L / 2 := by
  unfold edgeMass
  apply div_le_div_of_nonneg_right _ (by norm_num : (0 : ℝ) ≤ 2)
  calc
    ∑ v, w v * neighborhoodMass G w v ≤ ∑ v, w v * L :=
      Finset.sum_le_sum (fun v _ ↦ mul_le_mul_of_nonneg_left (hL v) (hw v))
    _ = (∑ v, w v) * L := (Finset.sum_mul ..).symm

/-- A restricted neighborhood lowers the excluded clique order on the current support. -/
theorem restrictedNeighborhood_cliqueFreeOn_of_mem (G : SimpleGraph V) {H : Finset V}
    {r : ℕ} (hG : G.CliqueFreeOn (H : Set V) (r + 1)) {v : V} (hv : v ∈ H) :
    G.CliqueFreeOn (restrictedNeighborhood G H v : Set V) r := by
  apply (hG.of_succ G hv).subset G
  intro x hx
  exact (mem_restrictedNeighborhood G H v x).mp hx

/-- Neighborhood restriction preserves at least `Q⁻ⁿ` of the mass in clique order `n + 2`. -/
theorem exists_sparseRestriction_add_two (n : ℕ) (G : SimpleGraph V) (w : V → ℝ)
    (hw : ∀ v, 0 < w v) {H : Finset V} (hH : H.Nonempty)
    (hG : G.CliqueFreeOn (H : Set V) (n + 2)) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ C : Finset V, C ⊆ H ∧ C.Nonempty ∧ weightSum w H ≤ Q ^ n * weightSum w C ∧
      ∀ v ∈ C, weightSum w (restrictedNeighborhood G C v) ≤ weightSum w C / Q := by
  classical
  have hQpos : 0 < Q := lt_of_lt_of_le zero_lt_one hQ
  induction n generalizing H with
  | zero =>
    refine ⟨H, Finset.Subset.refl H, hH, by simp, ?_⟩
    intro v hv
    have hN : restrictedNeighborhood G H v = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro x hx
      obtain ⟨hxH, hvx⟩ := (mem_restrictedNeighborhood G H v x).mp hx
      exact ((G.cliqueFreeOn_two.mp hG) hv hxH hvx.ne) hvx
    rw [hN, weightSum_empty]
    exact div_nonneg (weightSum_nonneg (fun v ↦ (hw v).le) H) hQpos.le
  | succ n ih =>
    by_cases hstop : ∀ v ∈ H,
        weightSum w (restrictedNeighborhood G H v) ≤ weightSum w H / Q
    · refine ⟨H, Finset.Subset.refl H, hH, ?_, hstop⟩
      exact le_mul_of_one_le_left (weightSum_nonneg (fun v ↦ (hw v).le) H)
        (one_le_pow₀ hQ)
    · push Not at hstop
      obtain ⟨v, hv, hheavy⟩ := hstop
      let N := restrictedNeighborhood G H v
      have hNpos : 0 < weightSum w N :=
        lt_of_le_of_lt (div_nonneg (weightSum_nonneg (fun v ↦ (hw v).le) H) hQpos.le)
          hheavy
      have hN : N.Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        intro h
        simp [h] at hNpos
      have hGN : G.CliqueFreeOn (N : Set V) (n + 2) := by
        apply restrictedNeighborhood_cliqueFreeOn_of_mem G (r := n + 2) _ hv
        convert hG using 1
      obtain ⟨C, hCN, hC, hmass, hsparse⟩ := ih hN hGN
      refine ⟨C, hCN.trans (restrictedNeighborhood_subset G H v), hC, ?_, hsparse⟩
      calc
        weightSum w H ≤ Q * weightSum w N := by
          have h := (div_lt_iff₀ hQpos).mp hheavy
          nlinarith
        _ ≤ Q * (Q ^ n * weightSum w C) := mul_le_mul_of_nonneg_left hmass hQpos.le
        _ = Q ^ (n + 1) * weightSum w C := by rw [pow_succ]; ring

/-- Every nonempty set in a clique-free graph contains a quantitatively large sparse set. -/
theorem exists_sparseRestriction (G : SimpleGraph V) {r : ℕ} (hr : 2 ≤ r)
    (hG : G.CliqueFree r) (w : V → ℝ) (hw : ∀ v, 0 < w v)
    {H : Finset V} (hH : H.Nonempty) {Q : ℝ} (hQ : 1 ≤ Q) :
    ∃ C : Finset V, C ⊆ H ∧ C.Nonempty ∧ weightSum w H / Q ^ (r - 2) ≤ weightSum w C ∧
      ∀ v ∈ C, weightSum w (restrictedNeighborhood G C v) ≤ weightSum w C / Q := by
  have hGr : G.CliqueFreeOn (H : Set V) ((r - 2) + 2) := by
    rw [Nat.sub_add_cancel hr]
    exact hG.cliqueFreeOn
  obtain ⟨C, hCH, hC, hmass, hsparse⟩ :=
    exists_sparseRestriction_add_two (r - 2) G w hw hH hGr hQ
  refine ⟨C, hCH, hC, ?_, hsparse⟩
  apply (div_le_iff₀ (pow_pos (lt_of_lt_of_le zero_lt_one hQ) _)).mpr
  simpa only [mul_comm] using hmass

/-- A sparse restriction has at most its squared mass divided by `Q` in ordered edge mass. -/
theorem two_mul_edgeMass_induce_le_of_sparseRestriction (G : SimpleGraph V) (w : V → ℝ)
    (hw : ∀ v, 0 ≤ w v) (C : Finset V) {Q : ℝ}
    (hsparse : ∀ v ∈ C,
      weightSum w (restrictedNeighborhood G C v) ≤ weightSum w C / Q) :
    2 * edgeMass (G.induce (C : Set V)) (fun v ↦ w v) ≤ weightSum w C ^ 2 / Q := by
  have h := edgeMass_le_of_neighborhood_bound (G.induce (C : Set V))
    (fun v ↦ hw v) (fun v ↦ by
      rw [neighborhoodMass_induce_eq_weightSum]
      exact hsparse v v.property)
  have hsum : (∑ v : (C : Set V), w v) = weightSum w C :=
    sum_restrict_eq_weightSum C w
  rw [hsum] at h
  calc
    2 * edgeMass (G.induce (C : Set V)) (fun v ↦ w v) ≤
        2 * (weightSum w C * (weightSum w C / Q) / 2) := by linarith
    _ = weightSum w C ^ 2 / Q := by ring

end Cliquefree
