module

public import Cliquefree.TriangleProjection
public import Cliquefree.TriangleKernels

/-!
# Splitting a graph by incidence labels

Each retained directed incidence is assigned to one copy of its center. An edge survives
when both incidences survive, and joins the two copies chosen by their respective labels.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V L : Type*}

/-- Split each vertex by its incidence labels and retain edges surviving at both endpoints. -/
def splitGraph (G : SimpleGraph V) (label : V → V → L) (keep : V → V → Prop) :
    SimpleGraph (V × L) where
  Adj a b := G.Adj a.1 b.1 ∧ keep a.1 b.1 ∧ keep b.1 a.1 ∧
    label a.1 b.1 = a.2 ∧ label b.1 a.1 = b.2
  symm := ⟨fun _ _ h ↦ ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.2, h.2.2.2.1⟩⟩
  loopless := ⟨fun _ h ↦ G.irrefl h.1⟩

/-- Forgetting labels projects every surviving directed edge injectively to the old graph. -/
def splitGraphProjection (G : SimpleGraph V) (label : V → V → L)
    (keep : V → V → Prop) : EdgeProjection (splitGraph G label keep) G where
  vertex := Prod.fst
  map_adj h := h.1
  edge_injective := by
    intro x y z t hxy hzt hx hy
    constructor
    · apply Prod.ext hx
      calc
        x.2 = label x.1 y.1 := hxy.2.2.2.1.symm
        _ = label z.1 t.1 := by rw [hx, hy]
        _ = z.2 := hzt.2.2.2.1
    · apply Prod.ext hy
      calc
        y.2 = label y.1 x.1 := hxy.2.2.2.2.symm
        _ = label t.1 z.1 := by rw [hx, hy]
        _ = t.2 := hzt.2.2.2.2

/-- Splitting cannot increase the degree budget with inherited vertex weights and scales. -/
theorem splitGraph_budget_le [Fintype V] [Fintype L] (G : SimpleGraph V)
    (label : V → V → L) (keep : V → V → Prop) {θ w : V → ℝ}
    (hθ : ∀ v, 0 ≤ θ v) (hw : ∀ v, 0 ≤ w v) :
    scaledDegreeBudget (splitGraph G label keep) (fun a ↦ θ a.1) (fun a ↦ w a.1) ≤
      scaledDegreeBudget G θ w :=
  (splitGraphProjection G label keep).scaledDegreeBudget_le hθ hw

/-- Each old neighbor contributes to exactly one copy at its own endpoint. -/
theorem splitGraph_neighborhoodMass [Fintype V] [Fintype L] [DecidableEq L]
    (G : SimpleGraph V) [DecidableRel G.Adj] (label : V → V → L)
    (keep : V → V → Prop) [DecidableRel keep] (w : V → ℝ) (x : V) (l : L) :
    neighborhoodMass (splitGraph G label keep) (fun a ↦ w a.1) (x, l) =
      ∑ v, if G.Adj x v ∧ keep x v ∧ keep v x ∧ label x v = l then w v else 0 := by
  classical
  unfold neighborhoodMass
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  by_cases h₁ : G.Adj x v <;> by_cases h₂ : keep x v <;> by_cases h₃ : keep v x <;>
    by_cases h₄ : label x v = l <;> simp [splitGraph, h₁, h₂, h₃, h₄]

/-- A reversed-row threshold bounds each split copy's neighborhood mass. -/
theorem splitGraph_load_le [Fintype V] [Fintype L] (G : SimpleGraph V)
    (label : V → V → L) (keep : V → V → Prop) (w C : V → ℝ)
    (K : V → L → V → ℝ) (hC : ∀ x, 0 ≤ C x) (hK : ∀ x l v, 0 ≤ K x l v)
    (hrow : ∀ x l, (∑ v, K x l v) ≤ 1)
    (hkeep : ∀ x v, keep x v → w v ≤ C x * K x (label x v) v) (x : V) (l : L) :
    neighborhoodMass (splitGraph G label keep) (fun a ↦ w a.1) (x, l) ≤ C x := by
  classical
  rw [splitGraph_neighborhoodMass]
  calc
    _ ≤ ∑ v, C x * K x l v := by
      apply Finset.sum_le_sum
      intro v _
      split_ifs with hv
      · simpa only [hv.2.2.2] using hkeep x v hv.2.1
      · exact mul_nonneg (hC x) (hK x l v)
    _ = C x * ∑ v, K x l v := (Finset.mul_sum ..).symm
    _ ≤ C x := mul_le_of_le_one_right (hC x) (hrow x l)

/-- A triangle survives when each corner agrees on a label and all six incidences survive. -/
def TriangleRetained (label : V → V → L) (keep : V → V → Prop) (x y z : V) : Prop :=
  (label x y = label x z ∧ label y x = label y z ∧ label z x = label z y) ∧
    (keep x y ∧ keep y x ∧ keep y z ∧ keep z y ∧ keep z x ∧ keep x z)

/-- A retained original triangle gives a triangle on its three prescribed copies. -/
theorem splitGraph_triangle_of_retained (G : SimpleGraph V) (label : V → V → L)
    (keep : V → V → Prop) {x y z : V} (hxy : G.Adj x y) (hyz : G.Adj y z)
    (hzx : G.Adj z x) (h : TriangleRetained label keep x y z) :
    (splitGraph G label keep).Adj (x, label x y) (y, label y z) ∧
      (splitGraph G label keep).Adj (y, label y z) (z, label z x) ∧
      (splitGraph G label keep).Adj (z, label z x) (x, label x y) := by
  obtain ⟨⟨hlx, hly, hlz⟩, hxy', hyx', hyz', hzy', hzx', hxz'⟩ := h
  exact ⟨⟨hxy, hxy', hyx', rfl, hly⟩, ⟨hyz, hyz', hzy', rfl, hlz.symm⟩,
    ⟨hzx, hzx', hxz', rfl, hlx.symm⟩⟩

/-- Every triangle in the split graph projects to a retained original triangle. -/
theorem splitGraph_triangle_retained (G : SimpleGraph V) (label : V → V → L)
    (keep : V → V → Prop) {a b c : V × L}
    (hab : (splitGraph G label keep).Adj a b)
    (hbc : (splitGraph G label keep).Adj b c)
    (hca : (splitGraph G label keep).Adj c a) :
    TriangleRetained label keep a.1 b.1 c.1 := by
  exact ⟨⟨hab.2.2.2.1.trans hca.2.2.2.2.symm,
    hab.2.2.2.2.trans hbc.2.2.2.1.symm, hca.2.2.2.1.trans hbc.2.2.2.2.symm⟩,
    hab.2.1, hab.2.2.1, hbc.2.1, hbc.2.2.1, hca.2.1, hca.2.2.1⟩

/-- The ordered triple expression for six times the unordered triangle mass. -/
theorem six_mul_triangleMass_eq_sum_triples [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (w : V → ℝ) :
    6 * triangleMass G w = ∑ t : V × V × V,
      if G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1
      then w t.1 * w t.2.1 * w t.2.2 else 0 := by
  simp only [triangleMass, Fintype.sum_prod_type]
  ring_nf

open Classical in
/-- The triangle mass after splitting is exactly the mass of retained original triangles. -/
theorem splitGraph_triangleMass [Fintype V] [Fintype L] (G : SimpleGraph V)
    (label : V → V → L) (keep : V → V → Prop) (w : V → ℝ) :
    6 * triangleMass (splitGraph G label keep) (fun a ↦ w a.1) =
      ∑ t : V × V × V, if G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧
        G.Adj t.2.2 t.1 ∧ TriangleRetained label keep t.1 t.2.1 t.2.2
      then w t.1 * w t.2.1 * w t.2.2 else 0 := by
  classical
  let s := Finset.univ.filter (fun t : V × V × V ↦ G.Adj t.1 t.2.1 ∧
    G.Adj t.2.1 t.2.2 ∧ G.Adj t.2.2 t.1 ∧ TriangleRetained label keep t.1 t.2.1 t.2.2)
  let t := Finset.univ.filter (fun a : (V × L) × (V × L) × (V × L) ↦
    (splitGraph G label keep).Adj a.1 a.2.1 ∧
      (splitGraph G label keep).Adj a.2.1 a.2.2 ∧
      (splitGraph G label keep).Adj a.2.2 a.1)
  let f : V × V × V → (V × L) × (V × L) × (V × L) := fun a ↦
    ((a.1, label a.1 a.2.1), (a.2.1, label a.2.1 a.2.2), (a.2.2, label a.2.2 a.1))
  have hf : Function.Injective f := by
    intro a b h
    exact Prod.ext (congrArg (fun c ↦ c.1.1) h)
      (Prod.ext (congrArg (fun c ↦ c.2.1.1) h) (congrArg (fun c ↦ c.2.2.1) h))
  have himage : s.image f = t := by
    ext a
    constructor
    · intro ha
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
      obtain ⟨hxy, hyz, hzx, hr⟩ := (Finset.mem_filter.mp hb).2
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        splitGraph_triangle_of_retained G label keep hxy hyz hzx hr⟩
    · intro ha
      obtain ⟨hab, hbc, hca⟩ := (Finset.mem_filter.mp ha).2
      refine Finset.mem_image.mpr ⟨(a.1.1, a.2.1.1, a.2.2.1), ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hab.1, hbc.1, hca.1,
          splitGraph_triangle_retained G label keep hab hbc hca⟩
      · apply Prod.ext
        · exact Prod.ext rfl hab.2.2.2.1
        · exact Prod.ext (Prod.ext rfl hbc.2.2.2.1) (Prod.ext rfl hca.2.2.2.1)
  rw [six_mul_triangleMass_eq_sum_triples]
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  change (∑ a ∈ t, w a.1.1 * w a.2.1.1 * w a.2.2.1) =
    ∑ a ∈ s, w a.1 * w a.2.1 * w a.2.2
  rw [← himage, Finset.sum_image (fun a _ b _ h ↦ hf h)]


open Classical in
/-- The exact splitting loss is the weight of original triangles that were not retained. -/
theorem splitGraph_triangleMass_loss [Fintype V] [Fintype L] (G : SimpleGraph V)
    (label : V → V → L) (keep : V → V → Prop) (w : V → ℝ) :
    6 * (triangleMass G w - triangleMass (splitGraph G label keep) (fun a ↦ w a.1)) =
      ∑ t : V × V × V, if G.Adj t.1 t.2.1 ∧ G.Adj t.2.1 t.2.2 ∧
        G.Adj t.2.2 t.1 ∧ ¬TriangleRetained label keep t.1 t.2.1 t.2.2
      then w t.1 * w t.2.1 * w t.2.2 else 0 := by
  classical
  rw [mul_sub, six_mul_triangleMass_eq_sum_triples, splitGraph_triangleMass,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : G.Adj a.1 a.2.1 ∧ G.Adj a.2.1 a.2.2 ∧ G.Adj a.2.2 a.1 <;>
    by_cases hr : TriangleRetained label keep a.1 a.2.1 a.2.2 <;>
    simp_all

end Cliquefree
