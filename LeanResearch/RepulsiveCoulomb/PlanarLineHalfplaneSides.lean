module

public import Mathlib.Analysis.Complex.ReImTopology
public import Mathlib.Analysis.Convex.PathConnected
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section

/-! Literal upper/lower halfplane sides and restrictions of a constructed line
straightening. Side labels are explicit: positive imaginary coordinate is the
positive side. Conjugation makes both closed-side targets the same closed
upper halfplane, and fixes every real boundary coordinate. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

def planarOpenUpperHalfplane : Set ℂ := {z | 0 < z.im}
def planarOpenLowerHalfplane : Set ℂ := {z | z.im < 0}
def planarClosedUpperHalfplane : Set ℂ := {z | 0 ≤ z.im}
def planarClosedLowerHalfplane : Set ℂ := {z | z.im ≤ 0}

theorem planar_halfplane_partition :
    IsOpen planarOpenUpperHalfplane ∧ IsOpen planarOpenLowerHalfplane ∧
    IsConnected planarOpenUpperHalfplane ∧ IsConnected planarOpenLowerHalfplane ∧
    Disjoint planarOpenUpperHalfplane planarOpenLowerHalfplane ∧
    planarOpenUpperHalfplane ∪ planarOpenLowerHalfplane = {z : ℂ | z.im = 0}ᶜ ∧
    closure planarOpenUpperHalfplane = planarClosedUpperHalfplane ∧
    closure planarOpenLowerHalfplane = planarClosedLowerHalfplane ∧
    frontier planarOpenUpperHalfplane = {z : ℂ | z.im = 0} ∧
    frontier planarOpenLowerHalfplane = {z : ℂ | z.im = 0} := by
  have hup : Convex ℝ planarOpenUpperHalfplane :=
    convex_halfSpace_gt (.mk Complex.add_im Complex.smul_im) 0
  have hdn : Convex ℝ planarOpenLowerHalfplane :=
    convex_halfSpace_lt (.mk Complex.add_im Complex.smul_im) 0
  refine ⟨isOpen_lt continuous_const Complex.continuous_im,
    isOpen_lt Complex.continuous_im continuous_const,
    ⟨⟨Complex.I, by simp [planarOpenUpperHalfplane]⟩, hup.isPreconnected⟩,
    ⟨⟨-Complex.I, by simp [planarOpenLowerHalfplane]⟩, hdn.isPreconnected⟩,
    ?_, ?_, Complex.closure_setOfPred_lt_im 0, Complex.closure_setOfPred_im_lt 0,
    Complex.frontier_setOfPred_lt_im 0, Complex.frontier_setOfPred_im_lt 0⟩
  · apply disjoint_left.mpr
    intro z hz hz'
    change 0 < z.im at hz
    change z.im < 0 at hz'
    exact lt_asymm hz hz'
  · ext z
    change (0 < z.im ∨ z.im < 0) ↔ ¬z.im = 0
    constructor
    · rintro (h | h)
      · exact ne_of_gt h
      · exact ne_of_lt h
    · intro h
      rcases lt_or_gt_of_ne h with h | h
      · exact Or.inr h
      · exact Or.inl h

/-- An open connected partition identifies the actual connected components. -/
theorem component_of_two_open_connected_sets {X : Type*} [TopologicalSpace X]
    {C U V : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsConnected U) (hUV : Disjoint U V) (hcover : U ∪ V = C)
    {x : X} (hx : x ∈ U) : connectedComponentIn C x = U := by
  have hUC : U ⊆ C := by rw [← hcover]; exact subset_union_left
  have hxc : x ∈ connectedComponentIn C x := mem_connectedComponentIn (hUC hx)
  apply Subset.antisymm
  · exact isPreconnected_connectedComponentIn.subset_left_of_subset_union hU hV hUV
      (by rw [hcover]; exact connectedComponentIn_subset C x) ⟨x, hxc, hx⟩
  · exact hUc.isPreconnected.subset_connectedComponentIn hx hUC

/-- Any other pair of actual open connected sides differs only by the displayed
swap. This is the alignment step needed when re-centering local cone charts. -/
theorem two_open_connected_partitions_eq_or_swap {X : Type*} [TopologicalSpace X]
    {C U V A B : Set X} (hU : IsOpen U) (hV : IsOpen V)
    (hUc : IsConnected U) (hVc : IsConnected V) (hUV : Disjoint U V)
    (hcover : U ∪ V = C) (hA : IsOpen A) (hB : IsOpen B)
    (hAc : IsConnected A) (hBc : IsConnected B) (hAB : Disjoint A B)
    (hcover' : A ∪ B = C) : (U = A ∧ V = B) ∨ (U = B ∧ V = A) := by
  obtain ⟨x, hx⟩ := hUc.nonempty
  have hxm : x ∈ A ∪ B := hcover'.symm ▸ (hcover ▸ Or.inl hx)
  have hux := component_of_two_open_connected_sets hU hV hUc hUV hcover hx
  have hswap : V ∪ U = C := by rwa [union_comm]
  have hswap' : B ∪ A = C := by rwa [union_comm]
  rcases hxm with hxA | hxB
  · have hUA : U = A := hux.symm.trans
      (component_of_two_open_connected_sets hA hB hAc hAB hcover' hxA)
    left
    refine ⟨hUA, ?_⟩
    obtain ⟨z, hz⟩ := hVc.nonempty
    have hzA : z ∉ A := fun h ↦ disjoint_left.mp hUV (hUA.symm ▸ h) hz
    have hzB : z ∈ B := (hcover'.symm ▸ (hcover ▸ Or.inr hz) : z ∈ A ∪ B).resolve_left hzA
    exact (component_of_two_open_connected_sets hV hU hVc hUV.symm hswap hz).symm.trans
      (component_of_two_open_connected_sets hB hA hBc hAB.symm hswap' hzB)
  · have hUB : U = B := hux.symm.trans
      (component_of_two_open_connected_sets hB hA hBc hAB.symm hswap' hxB)
    right
    refine ⟨hUB, ?_⟩
    obtain ⟨z, hz⟩ := hVc.nonempty
    have hzB : z ∉ B := fun h ↦ disjoint_left.mp hUV (hUB.symm ▸ h) hz
    have hzA : z ∈ A := (hcover'.symm ▸ (hcover ▸ Or.inr hz) : z ∈ A ∪ B).resolve_right hzB
    exact (component_of_two_open_connected_sets hV hU hVc hUV.symm hswap hz).symm.trans
      (component_of_two_open_connected_sets hA hB hAc hAB hcover' hzA)

/-- Upper-side closure is carried to the literal Euclidean closed halfplane. -/
def straighteningUpperHalfplaneHomeomorph (H : ℂ ≃ₜ ℂ) :
    closure (H ⁻¹' planarOpenUpperHalfplane) ≃ₜ planarClosedUpperHalfplane := by
  have hcl : closure (H ⁻¹' planarOpenUpperHalfplane) = H ⁻¹' planarClosedUpperHalfplane := by
    rw [← H.preimage_closure, planar_halfplane_partition.2.2.2.2.2.2.1]
  exact (Homeomorph.setCongr hcl).trans (H.subtype (fun _ ↦ Iff.rfl))

/-- Reflection of the lower halfplane fixes the boundary pointwise. -/
def lowerToUpperHalfplaneHomeomorph :
    planarClosedLowerHalfplane ≃ₜ planarClosedUpperHalfplane :=
  Complex.conjCLE.toHomeomorph.subtype (fun z ↦ by
    change z.im ≤ 0 ↔ 0 ≤ (starRingEnd ℂ z).im
    simp)

/-- Both side homeomorphisms have the same target, with explicit lower-side
reflection; neither loses the literal real coordinate along the boundary. -/
def straighteningLowerHalfplaneHomeomorph (H : ℂ ≃ₜ ℂ) :
    closure (H ⁻¹' planarOpenLowerHalfplane) ≃ₜ planarClosedUpperHalfplane := by
  have hcl : closure (H ⁻¹' planarOpenLowerHalfplane) = H ⁻¹' planarClosedLowerHalfplane := by
    rw [← H.preimage_closure, planar_halfplane_partition.2.2.2.2.2.2.2.1]
  exact ((Homeomorph.setCongr hcl).trans (H.subtype (fun _ ↦ Iff.rfl))).trans
    lowerToUpperHalfplaneHomeomorph

@[simp] theorem straighteningUpperHalfplaneHomeomorph_apply (H : ℂ ≃ₜ ℂ)
    (z : closure (H ⁻¹' planarOpenUpperHalfplane)) :
    (straighteningUpperHalfplaneHomeomorph H z : ℂ) = H z := rfl

@[simp] theorem straighteningLowerHalfplaneHomeomorph_apply (H : ℂ ≃ₜ ℂ)
    (z : closure (H ⁻¹' planarOpenLowerHalfplane)) :
    (straighteningLowerHalfplaneHomeomorph H z : ℂ) = starRingEnd ℂ (H z) := rfl

end RepulsiveCoulomb
