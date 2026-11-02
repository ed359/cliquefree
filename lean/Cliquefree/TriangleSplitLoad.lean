module

public import Cliquefree.TriangleRandomSplit
public import Cliquefree.TriangleSplitting

/-! # Load bounds for splits using local reversed-row thresholds -/

@[expose] public section

noncomputable section

open scoped BigOperators

namespace Cliquefree

variable {V : Type*} [Fintype V]

/-- Extend each local transition row by zero off its center's open neighborhood. -/
def centerKernelExtension (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (x y v : V) : ℝ := by
  classical
  exact if hx : x ∈ triangleCenters G w then
    if hy : G.Adj x y then
      if hv : G.Adj x v then
        (P ⟨x, hx⟩ ⟨y, (G.mem_neighborFinset x y).mpr hy⟩).mass
          ⟨v, (G.mem_neighborFinset x v).mpr hv⟩
      else 0
    else 0
  else 0

/-- On a local row the zero extension has exactly the original point mass. -/
@[simp] theorem centerKernelExtension_coe (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (x : triangleCenters G w) (y v : G.neighborFinset x.val) :
    centerKernelExtension G w P x y v = (P x y).mass v := by
  simp only [centerKernelExtension, x.property, dite_true,
    (G.mem_neighborFinset x y).mp y.property, (G.mem_neighborFinset x v).mp v.property]

/-- Extended transition entries are nonnegative even off their valid local carriers. -/
theorem centerKernelExtension_nonneg (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (x y v : V) : 0 ≤ centerKernelExtension G w P x y v := by
  classical
  unfold centerKernelExtension
  split_ifs <;> first | exact FiniteLaw.nonneg _ _ | exact le_rfl

/-- Every extended row has total mass at most one, with zero mass on invalid rows. -/
theorem centerKernelExtension_row_le_one (G : SimpleGraph V) [DecidableRel G.Adj]
    (w : V → ℝ)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (x y : V) : (∑ v, centerKernelExtension G w P x y v) ≤ 1 := by
  classical
  by_cases hx : x ∈ triangleCenters G w
  · by_cases hy : G.Adj x y
    · let x' : triangleCenters G w := ⟨x, hx⟩
      let y' : G.neighborFinset x := ⟨y, (G.mem_neighborFinset x y).mpr hy⟩
      have he : (∑ v, centerKernelExtension G w P x y v) = 1 := by
        calc
          _ = ∑ v, if G.Adj x v then centerKernelExtension G w P x y v else 0 := by
            apply Finset.sum_congr rfl
            intro v _
            by_cases hv : G.Adj x v
            · simp only [hv, ite_true]
            · simp [centerKernelExtension, hx, hy, hv]
          _ = ∑ v : G.neighborFinset x, centerKernelExtension G w P x y v :=
            (sum_neighbor_subtype G x (centerKernelExtension G w P x y)).symm
          _ = ∑ v, (P x' y').mass v := by
            apply Finset.sum_congr rfl
            intro v _
            exact centerKernelExtension_coe G w P x' y' v
          _ = 1 := (P x' y').sum_mass
      exact he.le
    · simp [centerKernelExtension, hx, hy]
  · simp [centerKernelExtension, hx]

/-- Reversed local-row thresholds bound every copy's load in the incidence split. -/
theorem centerIncidenceSplit_load_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w C : V → ℝ) (hC : ∀ x, 0 ≤ C x) (fallback : V)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (f : TriangleLabeling G w) (x l : V) :
    neighborhoodMass (splitGraph G (centerIncidenceLabel G w fallback f)
      (centerIncidenceKeep G w (fun x v y ↦ w v ≤ C x * (P x y).mass v) f))
        (fun a ↦ w a.1) (x, l) ≤ C x := by
  classical
  apply splitGraph_load_le G (centerIncidenceLabel G w fallback f)
    (centerIncidenceKeep G w (fun x v y ↦ w v ≤ C x * (P x y).mass v) f)
    w C (centerKernelExtension G w P) hC (centerKernelExtension_nonneg G w P)
    (centerKernelExtension_row_le_one G w P)
  intro z v hkeep
  by_cases hz : z ∈ triangleCenters G w
  · by_cases hv : G.Adj z v
    · let z' : triangleCenters G w := ⟨z, hz⟩
      let v' : G.neighborFinset z := ⟨v, (G.mem_neighborFinset z v).mpr hv⟩
      have hk : w v ≤ C z * (P z' (f z' v')).mass v' := by
        simpa only [centerIncidenceKeep, hz, hv, dite_true] using hkeep
      change w v ≤ C z * centerKernelExtension G w P z'
        (centerIncidenceLabel G w fallback f z' v') v'
      rw [centerIncidenceLabel_coe, centerKernelExtension_coe]
      exact hk
    · simp [centerIncidenceKeep, hz, hv] at hkeep
  · simp [centerIncidenceKeep, hz] at hkeep

/-- The normalized reversed-row test bounds each new normalized load by its chosen scale. -/
theorem centerIncidenceSplit_normalized_load_le (G : SimpleGraph V) [DecidableRel G.Adj]
    (w θ : V → ℝ) (hθ : ∀ x, 0 < θ x) {S : ℝ} (hS : 0 < S) (fallback : V)
    (P : ∀ x : triangleCenters G w, G.neighborFinset x.val → FiniteLaw (G.neighborFinset x.val))
    (f : TriangleLabeling G w) (x l : V) :
    neighborhoodMass (splitGraph G (centerIncidenceLabel G w fallback f)
      (centerIncidenceKeep G w (fun x v y ↦ (w v / θ x) / S ≤ (P x y).mass v) f))
        (fun a ↦ w a.1) (x, l) ≤ S * θ x := by
  have he : (fun (x : triangleCenters G w) (v y : G.neighborFinset x.val) ↦
      (w v / θ x) / S ≤ (P x y).mass v) =
      (fun (x : triangleCenters G w) (v y : G.neighborFinset x.val) ↦
        w v ≤ (S * θ x) * (P x y).mass v) := by
    funext x v y
    apply propext
    rw [div_le_iff₀ hS, div_le_iff₀ (hθ x)]
    constructor <;> intro h <;> nlinarith only [h]
  rw [he]
  exact centerIncidenceSplit_load_le G w (fun x ↦ S * θ x)
    (fun x ↦ (mul_pos hS (hθ x)).le) fallback P f x l

end Cliquefree
