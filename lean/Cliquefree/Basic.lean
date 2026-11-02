module

public import Mathlib

/-!
# Finite weighted graphs

Edge and triangle masses count each unordered edge and triangle once, using symmetric ordered
sums divided by two and six, respectively; cross mass counts ordered pairs without a divisor.
-/

open scoped BigOperators

@[expose] public section

namespace Cliquefree

noncomputable section

variable {V : Type*} [Fintype V]

/-- The total weight of a finite vertex set. -/
def weightSum (w : V → ℝ) (A : Finset V) : ℝ := ∑ v ∈ A, w v

/-- The mass of the open neighborhood of a vertex. -/
def neighborhoodMass (G : SimpleGraph V) (w : V → ℝ) (v : V) : ℝ := by
  classical
  exact ∑ y, if G.Adj v y then w y else 0

/-- Weighted degree, used with a strictly positive denominator. -/
def weightedDegree (G : SimpleGraph V) (s : V → ℝ) (v : V) : ℝ :=
  neighborhoodMass G s v / s v

/-- Weighted edge mass, with each unordered edge counted once. -/
def edgeMass (G : SimpleGraph V) (w : V → ℝ) : ℝ :=
  (∑ v, w v * neighborhoodMass G w v) / 2

/-- Weighted triangle mass, with each unordered triangle counted once. -/
def triangleMass (G : SimpleGraph V) (w : V → ℝ) : ℝ := by
  classical
  exact (∑ x, ∑ y, ∑ z,
    if G.Adj x y ∧ G.Adj y z ∧ G.Adj z x then w x * w y * w z else 0) / 6

/-- Ordered cross mass; an edge in the overlap of the sets is counted twice. -/
def crossMass (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) : ℝ := by
  classical
  exact ∑ x ∈ A, ∑ y ∈ B, if G.Adj x y then w x * w y else 0

/-- The closed neighborhood deleted when a vertex is selected. -/
def closedNeighborhood (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact Finset.univ.filter (fun y ↦ y = x ∨ G.Adj x y)

/-- Independent finite vertex sets, using mathlib's graph-theoretic predicate. -/
def Independent (G : SimpleGraph V) (I : Finset V) : Prop :=
  G.IsIndepSet (I : Set V)

/-- Maximum independent-set weight, expressed as the supremum of a finite nonempty set. -/
def independenceWeight (G : SimpleGraph V) (u : V → ℝ) : ℝ :=
  sSup {a | ∃ I : Finset V, Independent G I ∧ weightSum u I = a}

/-- The scaled vertex mass `b(A)`. -/
def scaledMass (θ w : V → ℝ) (A : Finset V) : ℝ :=
  weightSum (fun v ↦ θ v * w v) A

/-- The degree budget for the triangle dichotomy. -/
def scaledDegreeBudget (G : SimpleGraph V) (θ w : V → ℝ) : ℝ :=
  ∑ v, θ v * w v * neighborhoodMass G w v

/-- The mixed objective mass `S`. -/
def objectiveMass (u w : V → ℝ) : ℝ := ∑ v, u v * w v

omit [Fintype V] in
/-- The weight of the empty vertex set vanishes. -/
@[simp] theorem weightSum_empty (w : V → ℝ) : weightSum w ∅ = 0 := by
  simp [weightSum]

omit [Fintype V] in
/-- A nonnegative weighting gives every finite set nonnegative mass. -/
theorem weightSum_nonneg {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset V) :
    0 ≤ weightSum w A :=
  Finset.sum_nonneg (fun v _ ↦ hw v)

/-- Neighborhood mass is nonnegative for nonnegative vertex weights. -/
theorem neighborhoodMass_nonneg (G : SimpleGraph V) {w : V → ℝ}
    (hw : ∀ v, 0 ≤ w v) (x : V) : 0 ≤ neighborhoodMass G w x := by
  classical
  unfold neighborhoodMass
  exact Finset.sum_nonneg (fun v _ ↦ by
    split_ifs
    · exact hw v
    · exact le_rfl)

/-- Neighborhood mass scales linearly with the weights. -/
theorem neighborhoodMass_scale (G : SimpleGraph V) (w : V → ℝ) (a : ℝ) (x : V) :
    neighborhoodMass G (fun v ↦ a * w v) x = a * neighborhoodMass G w x := by
  classical
  simp only [neighborhoodMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  split_ifs <;> simp

/-- Weighted degrees are invariant under a nonzero common rescaling. -/
theorem weightedDegree_scale (G : SimpleGraph V) (s : V → ℝ) {a : ℝ}
    (ha : a ≠ 0) (x : V) :
    weightedDegree G (fun v ↦ a * s v) x = weightedDegree G s x := by
  rw [weightedDegree, neighborhoodMass_scale, weightedDegree]
  exact mul_div_mul_left _ _ ha

/-- Positive weights give nonnegative weighted degrees. -/
theorem weightedDegree_nonneg (G : SimpleGraph V) {s : V → ℝ} (hs : ∀ v, 0 < s v)
    (x : V) : 0 ≤ weightedDegree G s x :=
  div_nonneg (neighborhoodMass_nonneg G (fun v ↦ (hs v).le) x) (hs x).le

/-- Weighted handshake identity with unordered edge normalization. -/
theorem weighted_handshake (G : SimpleGraph V) (w : V → ℝ) :
    ∑ v, w v * neighborhoodMass G w v = 2 * edgeMass G w := by
  unfold edgeMass
  ring

/-- Edge mass is homogeneous of degree two. -/
theorem edgeMass_scale (G : SimpleGraph V) (w : V → ℝ) (a : ℝ) :
    edgeMass G (fun v ↦ a * w v) = a ^ 2 * edgeMass G w := by
  simp only [edgeMass, neighborhoodMass_scale]
  simp_rw [show ∀ v, a * w v * (a * neighborhoodMass G w v) =
    a ^ 2 * (w v * neighborhoodMass G w v) by intro v; ring]
  rw [← Finset.mul_sum]
  ring

omit [Fintype V] in
/-- Symmetry of ordered cross mass, including overlapping sets. -/
theorem crossMass_comm (G : SimpleGraph V) (w : V → ℝ) (A B : Finset V) :
    crossMass G w A B = crossMass G w B A := by
  classical
  unfold crossMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  simp only [G.adj_comm, mul_comm]

/-- Selecting a vertex always removes that vertex. -/
theorem mem_closedNeighborhood_self (G : SimpleGraph V) (x : V) :
    x ∈ closedNeighborhood G x := by
  classical
  simp [closedNeighborhood]

/-- Every adjacent vertex is removed with a selected vertex. -/
theorem mem_closedNeighborhood_of_adj (G : SimpleGraph V) {x y : V} (h : G.Adj x y) :
    y ∈ closedNeighborhood G x := by
  classical
  simp [closedNeighborhood, h]

omit [Fintype V] in
/-- The empty finite vertex set is independent. -/
@[simp] theorem independent_empty (G : SimpleGraph V) : Independent G ∅ := by
  simp [Independent, SimpleGraph.IsIndepSet]

omit [Fintype V] in
/-- There are only finitely many independent-set weights in a finite graph. -/
theorem independentWeights_finite [Finite V] (G : SimpleGraph V) (u : V → ℝ) :
    {a | ∃ I : Finset V, Independent G I ∧ weightSum u I = a}.Finite := by
  classical
  apply (Set.finite_range (weightSum u)).subset
  rintro a ⟨I, _, rfl⟩
  exact ⟨I, rfl⟩

omit [Fintype V] in
/-- The empty independent set makes the set of attainable weights nonempty. -/
theorem independentWeights_nonempty (G : SimpleGraph V) (u : V → ℝ) :
    {a | ∃ I : Finset V, Independent G I ∧ weightSum u I = a}.Nonempty :=
  ⟨0, ∅, independent_empty G, weightSum_empty u⟩

omit [Fintype V] in
/-- The weight of any independent set is bounded by the maximum independent weight. -/
theorem weightSum_le_independenceWeight [Finite V] (G : SimpleGraph V) (u : V → ℝ)
    {I : Finset V} (hI : Independent G I) : weightSum u I ≤ independenceWeight G u := by
  exact le_csSup (independentWeights_finite G u).bddAbove ⟨I, hI, rfl⟩

omit [Fintype V] in
/-- Some independent set attains the maximum independent weight. -/
theorem independenceWeight_attained [Finite V] (G : SimpleGraph V) (u : V → ℝ) :
    ∃ I : Finset V, Independent G I ∧ weightSum u I = independenceWeight G u := by
  exact (independentWeights_nonempty G u).csSup_mem (independentWeights_finite G u)

omit [Fintype V] in
/-- The maximum independent weight is nonnegative, even when some weights are negative. -/
theorem independenceWeight_nonneg [Finite V] (G : SimpleGraph V) (u : V → ℝ) :
    0 ≤ independenceWeight G u := by
  simpa using weightSum_le_independenceWeight G u (independent_empty G)

/-- The open-neighborhood mass agrees with a sum over mathlib's neighbor finset. -/
theorem neighborhoodMass_eq_sum_neighborFinset (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ) (x : V) :
    neighborhoodMass G w x = ∑ y ∈ G.neighborFinset x, w y := by
  classical
  simp only [neighborhoodMass, SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> rfl

/-- Isolated vertices have zero open-neighborhood mass. -/
theorem neighborhoodMass_eq_zero_of_isolated (G : SimpleGraph V) (w : V → ℝ) {x : V}
    (hx : ∀ y, ¬G.Adj x y) : neighborhoodMass G w x = 0 := by
  classical
  simp [neighborhoodMass, hx]

/-- An isolated vertex has weighted degree zero for every weight vector. -/
theorem weightedDegree_eq_zero_of_isolated (G : SimpleGraph V) (s : V → ℝ) {x : V}
    (hx : ∀ y, ¬G.Adj x y) : weightedDegree G s x = 0 := by
  rw [weightedDegree, neighborhoodMass_eq_zero_of_isolated G s hx, zero_div]

/-- Cross mass from a singleton to all vertices is its weighted neighborhood mass. -/
theorem crossMass_singleton_univ (G : SimpleGraph V) (w : V → ℝ) (x : V) :
    crossMass G w {x} Finset.univ = w x * neighborhoodMass G w x := by
  classical
  simp only [crossMass, Finset.sum_singleton, neighborhoodMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  split_ifs <;> simp

/-- Membership in a closed neighborhood is equality or adjacency. -/
@[simp] theorem mem_closedNeighborhood (G : SimpleGraph V) (x y : V) :
    y ∈ closedNeighborhood G x ↔ y = x ∨ G.Adj x y := by
  classical
  simp [closedNeighborhood]

/-- A vertex can extend any independent set disjoint from its closed neighborhood. -/
theorem independent_insert_of_disjoint_closedNeighborhood (G : SimpleGraph V)
    [DecidableEq V] {I : Finset V} (hI : Independent G I) {x : V}
    (hdisj : Disjoint I (closedNeighborhood G x)) : Independent G (insert x I) := by
  intro a ha b hb hab
  rcases Finset.mem_insert.mp ha with hax | haI
  · subst a
    rcases Finset.mem_insert.mp hb with hbx | hbI
    · exact (hab hbx.symm).elim
    · exact fun h ↦ Finset.disjoint_left.mp hdisj hbI (mem_closedNeighborhood_of_adj G h)
  · rcases Finset.mem_insert.mp hb with hbx | hbI
    · subst b
      exact fun h ↦ Finset.disjoint_left.mp hdisj haI (mem_closedNeighborhood_of_adj G h.symm)
    · exact hI haI hbI hab

/-- Extending an independent set outside a closed neighborhood adds the selected weight. -/
theorem selection_weight_le_independenceWeight (G : SimpleGraph V) (u : V → ℝ)
    {I : Finset V} (hI : Independent G I) {x : V}
    (hdisj : Disjoint I (closedNeighborhood G x)) :
    u x + weightSum u I ≤ independenceWeight G u := by
  classical
  have hx : x ∉ I := fun hx ↦
    Finset.disjoint_left.mp hdisj hx (mem_closedNeighborhood_self G x)
  simpa [weightSum, hx] using weightSum_le_independenceWeight G u
    (independent_insert_of_disjoint_closedNeighborhood G hI hdisj)

/-- The ordered cross mass of the whole graph is twice its unordered edge mass. -/
theorem crossMass_univ_univ (G : SimpleGraph V) (w : V → ℝ) :
    crossMass G w Finset.univ Finset.univ = 2 * edgeMass G w := by
  classical
  rw [← weighted_handshake]
  unfold crossMass
  apply Finset.sum_congr rfl
  intro x _
  simpa only [crossMass, Finset.sum_singleton] using crossMass_singleton_univ G w x

end

end Cliquefree
