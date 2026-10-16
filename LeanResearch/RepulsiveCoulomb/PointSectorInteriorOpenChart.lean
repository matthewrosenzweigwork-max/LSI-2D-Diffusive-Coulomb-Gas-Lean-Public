import LeanResearch.RepulsiveCoulomb.PointActualSectorContractionChart
import LeanResearch.RepulsiveCoulomb.EuclideanSectorBoundaryCases
import Mathlib.Topology.OpenPartialHomeomorph.Defs
import Mathlib.Topology.Homeomorph.Lemmas

/-! SOURCE-ONLY, UNCOMPILED. Points inside a selected open sector have actual
ambient open charts directly from that sector's angular contraction. This
is a separate branch from the incident-boundary construction; an interior
point is not incorrectly forced into an apex or halfdisk model. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def subsetInsideSubtypeHomeomorph {X : Type*} [TopologicalSpace X]
    (A B : Set X) (hAB : A ⊆ B) : A ≃ₜ {x : B | x.1 ∈ A} where
  toFun x := ⟨⟨x.1, hAB x.2⟩, x.2⟩
  invFun x := ⟨x.1.1, x.2⟩
  left_inv := fun _ ↦ rfl
  right_inv := fun _ ↦ rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem closedSectorContractionHomeomorph_interior_iff {c β : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1) (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (x : closedEuclideanSector β) :
    x.1 ∈ interior (closedEuclideanSector β) ↔
      (closedSectorContractionHomeomorph hc hc1 hβ.le hβπ x).1 ∈
        interior (closedEuclideanSector (c * β)) := by
  have hcβ : 0 < c * β := mul_pos hc hβ
  have hcβπ : c * β ≤ Real.pi := (mul_le_of_le_one_left hβ.le hc1).trans hβπ
  constructor
  · intro hx
    have ha := closedEuclideanSector_interior_strict_arg hβ hβπ hx
    apply mem_interior_closedEuclideanSector_of_strict_arg hcβ hcβπ
    change Complex.arg (sectorAngularMap c x.1) ∈ Ioo 0 (c * β)
    rw [sectorAngularMap_arg hc.le hc1 hβπ x.2]
    exact ⟨mul_pos hc ha.1, mul_lt_mul_of_pos_left ha.2 hc⟩
  · intro hx
    have ha := closedEuclideanSector_interior_strict_arg hcβ hcβπ hx
    change Complex.arg (sectorAngularMap c x.1) ∈ Ioo 0 (c * β) at ha
    rw [sectorAngularMap_arg hc.le hc1 hβπ x.2] at ha
    apply mem_interior_closedEuclideanSector_of_strict_arg hβ hβπ
    exact ⟨(mul_pos_iff_of_pos_left hc).mp ha.1, (mul_lt_mul_iff_right₀ hc).mp ha.2⟩

theorem pointActualSectorContractionChart_interior_iff
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (x : range S.map) :
    x.1 ∈ S.openImage ↔ (pointActualSectorContractionChart ha S hc hc1 x).1 ∈
      interior (closedEuclideanSector (c * S.beta)) := by
  obtain ⟨q, hq⟩ := x.2
  have hx : x = ⟨S.map q, mem_range_self q⟩ := Subtype.ext hq.symm
  rw [hx, pointActualSectorContractionChart_apply_map]
  have hsource : S.map q ∈ S.openImage ↔ q.1 ∈ interior (closedEuclideanSector S.beta) := by
    constructor
    · rintro ⟨w, hw, he⟩
      have hqw : w = q := S.map_injective he
      exact hqw ▸ hw
    · intro hq
      exact ⟨q, hq, rfl⟩
  exact hsource.trans (closedSectorContractionHomeomorph_interior_iff hc hc1 S.positive S.le_pi q)

def pointActualSectorInteriorHomeomorph
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) :
    S.openImage ≃ₜ interior (closedEuclideanSector (c * S.beta)) :=
  (subsetInsideSubtypeHomeomorph S.openImage (range S.map) S.openImage_subset_range).trans
    (((pointActualSectorContractionChart ha S hc hc1).subtype
      (pointActualSectorContractionChart_interior_iff ha S hc hc1)).trans
      (subsetInsideSubtypeHomeomorph (interior (closedEuclideanSector (c * S.beta)))
        (closedEuclideanSector (c * S.beta)) interior_subset).symm)

theorem pointActualSectorInteriorHomeomorph_apply
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (x : S.openImage) :
    (pointActualSectorInteriorHomeomorph ha S hc hc1 x : ℂ) =
      (pointActualSectorContractionChart ha S hc hc1
        ⟨x.1, S.openImage_subset_range x.2⟩ : ℂ) := rfl

/-- Extend an actual homeomorphism between open subsets to an ambient open
partial homeomorphism. Outside values are immaterial and fixed explicitly. -/
def openPartialHomeomorphOfComplexOpenSubsets {U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (H : U ≃ₜ V) : OpenPartialHomeomorph ℂ ℂ := by
  classical
  let F : ℂ → ℂ := fun x ↦ if hx : x ∈ U then (H ⟨x, hx⟩).1 else 0
  let G : ℂ → ℂ := fun y ↦ if hy : y ∈ V then (H.symm ⟨y, hy⟩).1 else 0
  have hF (x : ℂ) (hx : x ∈ U) : F x = (H ⟨x, hx⟩).1 := dif_pos hx
  have hG (y : ℂ) (hy : y ∈ V) : G y = (H.symm ⟨y, hy⟩).1 := dif_pos hy
  refine {
    toFun := F, invFun := G, source := U, target := V,
    map_source' := fun _ hx ↦ (hF _ hx).symm ▸ (H ⟨_, hx⟩).2,
    map_target' := fun _ hy ↦ (hG _ hy).symm ▸ (H.symm ⟨_, hy⟩).2,
    left_inv' := ?_, right_inv' := ?_,
    continuousOn_toFun := ?_, continuousOn_invFun := ?_,
    open_source := hU, open_target := hV
  }
  · intro x hx
    rw [hF x hx, hG _ (H ⟨x, hx⟩).2]
    exact congrArg Subtype.val (H.symm_apply_apply ⟨x, hx⟩)
  · intro y hy
    rw [hG y hy, hF _ (H.symm ⟨y, hy⟩).2]
    exact congrArg Subtype.val (H.apply_symm_apply ⟨y, hy⟩)
  · apply continuousOn_iff_continuous_restrict.mpr
    have he : (fun x : U ↦ F x.1) = (fun x : U ↦ (H x).1) := by
      funext x
      exact hF x.1 x.2
    change Continuous (fun x : U ↦ F x.1)
    rw [he]
    exact continuous_subtype_val.comp H.continuous
  · apply continuousOn_iff_continuous_restrict.mpr
    have he : (fun y : V ↦ G y.1) = (fun y : V ↦ (H.symm y).1) := by
      funext y
      exact hG y.1 y.2
    change Continuous (fun y : V ↦ G y.1)
    rw [he]
    exact continuous_subtype_val.comp H.symm.continuous

def pointActualSectorInteriorOpenChart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hS : IsOpen S.openImage) : OpenPartialHomeomorph ℂ ℂ :=
  openPartialHomeomorphOfComplexOpenSubsets hS isOpen_interior
    (pointActualSectorInteriorHomeomorph ha S hc hc1)

@[simp] theorem pointActualSectorInteriorOpenChart_source
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hS : IsOpen S.openImage) :
    (pointActualSectorInteriorOpenChart ha S hc hc1 hS).source = S.openImage := rfl

end RepulsiveCoulomb
