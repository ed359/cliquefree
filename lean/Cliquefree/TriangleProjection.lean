module

public import Cliquefree.TriangleBasics

/-!
# Projecting witnesses from split graphs

A split graph inherits vertex weights and scales and projects injectively on directed edges.
Its cross mass can only increase under projection, while repeated vertex copies merge.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V W : Type*}

/-- A vertex projection preserving edges and distinguishing all directed source edges. -/
structure EdgeProjection (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- Each split vertex remembers its original vertex. -/
  vertex : W → V
  /-- Every edge of the split graph projects to an original edge. -/
  map_adj : ∀ {x y}, H.Adj x y → G.Adj (vertex x) (vertex y)
  /-- Distinct directed source edges have distinct projected endpoint pairs. -/
  edge_injective : ∀ {x y z t}, H.Adj x y → H.Adj z t →
    vertex x = vertex z → vertex y = vertex t → x = z ∧ y = t

/-- Merging vertex copies never increases the mass of a projected set. -/
theorem EdgeProjection.weightSum_image_le [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V}
    (π : EdgeProjection H G) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A : Finset W) :
    weightSum w (A.image π.vertex) ≤ weightSum (fun v ↦ w (π.vertex v)) A := by
  classical
  exact Finset.sum_image_le_of_nonneg (fun v _ ↦ hw v)

/-- Merging vertex copies never increases a set's inherited scaled mass. -/
theorem EdgeProjection.scaledMass_image_le [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V} (π : EdgeProjection H G) {θ w : V → ℝ}
    (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v) (A : Finset W) :
    scaledMass θ w (A.image π.vertex) ≤
      scaledMass (fun v ↦ θ (π.vertex v)) (fun v ↦ w (π.vertex v)) A :=
  π.weightSum_image_le (fun v ↦ mul_nonneg (hθ v) (hw v)) A

/-- An injective directed-edge projection cannot lose nonnegative edge observables. -/
theorem EdgeProjection.sum_edges_le
    {H : SimpleGraph W} {G : SimpleGraph V} [DecidableRel H.Adj] [DecidableRel G.Adj]
    (π : EdgeProjection H G) (F : V → V → ℝ) (hF : ∀ x y, 0 ≤ F x y)
    (A B : Finset W) (C D : Finset V)
    (hA : ∀ x ∈ A, π.vertex x ∈ C) (hB : ∀ y ∈ B, π.vertex y ∈ D) :
    (∑ x ∈ A, ∑ y ∈ B, if H.Adj x y then F (π.vertex x) (π.vertex y) else 0) ≤
      ∑ x ∈ C, ∑ y ∈ D, if G.Adj x y then F x y else 0 := by
  classical
  let s := (A.product B).filter (fun e ↦ H.Adj e.1 e.2)
  let t := (C.product D).filter (fun e ↦ G.Adj e.1 e.2)
  let f : W × W → V × V := fun e ↦ (π.vertex e.1, π.vertex e.2)
  have hinj : Set.InjOn f (s : Set (W × W)) := by
    intro e he e' he' heq
    have h := π.edge_injective (Finset.mem_filter.mp he).2
      (Finset.mem_filter.mp he').2 (congrArg Prod.fst heq) (congrArg Prod.snd heq)
    exact Prod.ext h.1 h.2
  have hsub : s.image f ⊆ t := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨hab, hedge⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hA a.1 ha, hB a.2 hb⟩,
      π.map_adj hedge⟩
  calc
    _ = ∑ e ∈ s, F (π.vertex e.1) (π.vertex e.2) := by
      dsimp only [s]
      rw [Finset.sum_filter]
      exact (Finset.sum_product A B
        (fun e ↦ if H.Adj e.1 e.2 then F (π.vertex e.1) (π.vertex e.2) else 0)).symm
    _ = ∑ e ∈ s.image f, F e.1 e.2 :=
      (Finset.sum_image (f := fun e ↦ F e.1 e.2) hinj).symm
    _ ≤ ∑ e ∈ t, F e.1 e.2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun e _ _ ↦ hF e.1 e.2)
    _ = _ := by
      dsimp only [t]
      rw [Finset.sum_filter]
      exact Finset.sum_product C D (fun e ↦ if G.Adj e.1 e.2 then F e.1 e.2 else 0)

/-- Cross mass can only increase when split vertices are projected to the original graph. -/
theorem EdgeProjection.crossMass_image_le [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V} (π : EdgeProjection H G)
    {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (A B : Finset W) :
    crossMass H (fun v ↦ w (π.vertex v)) A B ≤
      crossMass G w (A.image π.vertex) (B.image π.vertex) := by
  classical
  exact π.sum_edges_le (fun x y ↦ w x * w y) (fun x y ↦ mul_nonneg (hw x) (hw y))
    A B (A.image π.vertex) (B.image π.vertex)
    (fun _ hx ↦ Finset.mem_image_of_mem π.vertex hx)
    (fun _ hy ↦ Finset.mem_image_of_mem π.vertex hy)

/-- Inherited weights and directed-edge injectivity prevent splitting from raising the budget. -/
theorem EdgeProjection.scaledDegreeBudget_le [Fintype V] [Fintype W]
    {H : SimpleGraph W} {G : SimpleGraph V} (π : EdgeProjection H G) {θ w : V → ℝ}
    (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v) :
    scaledDegreeBudget H (fun v ↦ θ (π.vertex v)) (fun v ↦ w (π.vertex v)) ≤
      scaledDegreeBudget G θ w := by
  classical
  have h := π.sum_edges_le (fun x y ↦ θ x * w x * w y)
    (fun x y ↦ mul_nonneg (mul_nonneg (hθ x) (hw x)) (hw y))
    Finset.univ Finset.univ Finset.univ Finset.univ
    (fun _ _ ↦ Finset.mem_univ _) (fun _ _ ↦ Finset.mem_univ _)
  simpa only [scaledDegreeBudget, neighborhoodMass, Finset.mul_sum, mul_ite, mul_zero] using h

/-- All strong-witness inequalities survive projection to the original graph. -/
def TriangleWitness.project [DecidableEq V]
    {H : SimpleGraph W} {G : SimpleGraph V} (π : EdgeProjection H G) {θ w : V → ℝ}
    (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v)
    (q : TriangleWitness H (fun v ↦ θ (π.vertex v)) (fun v ↦ w (π.vertex v))) :
    TriangleWitness G θ w where
  A := q.A.image π.vertex
  B := q.B.image π.vertex
  p := q.p
  p_pos := q.p_pos
  scaleVertex := π.vertex q.scaleVertex
  weight_A := (π.weightSum_image_le hw q.A).trans q.weight_A
  weight_B := (π.weightSum_image_le hw q.B).trans q.weight_B
  scaled_B := (π.scaledMass_image_le hθ hw q.B).trans q.scaled_B
  cross_large := by
    have hs := mul_le_mul_of_nonneg_left (π.scaledMass_image_le hθ hw q.A)
      (Nat.cast_nonneg q.p : (0 : ℝ) ≤ q.p)
    have hc := π.crossMass_image_le hw q.A q.B
    have hq := q.cross_large
    nlinarith

/-- Directed-edge injectivity is preserved throughout any sequence of graph splittings. -/
def EdgeProjection.comp {U : Type*} {K : SimpleGraph U} {H : SimpleGraph W}
    {G : SimpleGraph V} (π : EdgeProjection H G) (σ : EdgeProjection K H) :
    EdgeProjection K G where
  vertex x := π.vertex (σ.vertex x)
  map_adj h := π.map_adj (σ.map_adj h)
  edge_injective hxy hzt hx hy := by
    obtain ⟨hx', hy'⟩ := π.edge_injective (σ.map_adj hxy) (σ.map_adj hzt) hx hy
    exact σ.edge_injective hxy hzt hx' hy'

end Cliquefree
