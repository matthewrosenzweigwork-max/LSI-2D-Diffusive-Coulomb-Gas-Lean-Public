module

public import LeanResearch.RepulsiveCoulomb.PointRadialSectorTopology

@[expose] public section

/-! Local inside/outside choice is forced by the actual two-ray boundary.
The polar sectors are concrete connected sets, and their opposite side choices
follow from the two closure incidences at the vertex. This is a local theorem;
it neither assumes nor asserts global total turn. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Two connected pieces of a punctured neighborhood must occupy opposite
open sides if both sides accumulate at the vertex. -/
theorem two_local_connected_pieces_opposite_sides {X : Type*} [TopologicalSpace X]
    {W C U V A B : Set X} {p : X}
    (hW : IsOpen W) (hpW : p ∈ W) (hU : IsOpen U) (hV : IsOpen V)
    (hd : Disjoint U V) (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    (hlocal : W \ C = A ∪ B)
    (hcover : ∀ z ∈ W, z ∉ C ↔ z ∈ U ∨ z ∈ V)
    (hA : IsPreconnected A) (hB : IsPreconnected B) :
    (A ⊆ U ∧ B ⊆ V) ∨ (A ⊆ V ∧ B ⊆ U) := by
  have hsubA : A ⊆ U ∪ V := by
    intro z hz
    have hzw : z ∈ W \ C := hlocal.symm ▸ Or.inl hz
    exact (hcover z hzw.1).mp hzw.2
  have hsubB : B ⊆ U ∪ V := by
    intro z hz
    have hzw : z ∈ W \ C := hlocal.symm ▸ Or.inr hz
    exact (hcover z hzw.1).mp hzw.2
  have hnotUU : ¬ (A ⊆ U ∧ B ⊆ U) := by
    intro hh
    obtain ⟨v, hvW, hvV⟩ := mem_closure_iff.mp hpV W hW hpW
    have hvC : v ∉ C := (hcover v hvW).mpr (Or.inr hvV)
    have hvAB : v ∈ A ∪ B := hlocal ▸ (show v ∈ W \ C from ⟨hvW, hvC⟩)
    exact disjoint_left.mp hd (hvAB.elim (fun h => hh.1 h) (fun h => hh.2 h)) hvV
  have hnotVV : ¬ (A ⊆ V ∧ B ⊆ V) := by
    intro hh
    obtain ⟨u, huW, huU⟩ := mem_closure_iff.mp hpU W hW hpW
    have huC : u ∉ C := (hcover u huW).mpr (Or.inl huU)
    have huAB : u ∈ A ∪ B := hlocal ▸ (show u ∈ W \ C from ⟨huW, huC⟩)
    exact disjoint_left.mp hd huU (huAB.elim (fun h => hh.1 h) (fun h => hh.2 h))
  rcases IsPreconnected.subset_or_subset hU hV hd hsubA hA with hAU | hAV
  · rcases IsPreconnected.subset_or_subset hU hV hd hsubB hB with hBU | hBV
    · exact False.elim (hnotUU ⟨hAU, hBU⟩)
    · exact Or.inl ⟨hAU, hBV⟩
  · rcases IsPreconnected.subset_or_subset hU hV hd hsubB hB with hBU | hBV
    · exact Or.inr ⟨hAV, hBU⟩
    · exact False.elim (hnotVV ⟨hAV, hBV⟩)

/-- In coordinates where the actual boundary is two rays, precisely one of
its actual connected polar sectors is on each of the two local Jordan sides.
The local-cover form also applies to a partial-homeomorphism chart image. -/
theorem pointRadialBoundary_jordan_side_choice {R θ : ℝ} (hR : 0 < R)
    (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi) {C U V : Set ℂ}
    (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (h0U : (0 : ℂ) ∈ closure U) (h0V : (0 : ℂ) ∈ closure V)
    (hcover : ∀ z ∈ ball (0 : ℂ) R, z ∉ C ↔ z ∈ U ∨ z ∈ V)
    (hboundary : ∀ z ∈ ball (0 : ℂ) R,
      z ∈ C ↔ z ∈ pointDiskRay R 0 ∪ pointDiskRay R θ) :
    (pointOpenRadialSector R 0 θ ⊆ U ∧ pointOpenRadialSector R θ (2 * Real.pi) ⊆ V) ∨
      (pointOpenRadialSector R 0 θ ⊆ V ∧ pointOpenRadialSector R θ (2 * Real.pi) ⊆ U) := by
  apply two_local_connected_pieces_opposite_sides isOpen_ball (mem_ball_self hR)
    hU hV hd h0U h0V ?_ hcover
    (pointOpenRadialSector_preconnected R 0 θ)
    (pointOpenRadialSector_preconnected R θ (2 * Real.pi))
  rw [← pointDiskRay_complement_eq_sectors hR hθ0 hθ2]
  ext z
  constructor
  · intro hz
    exact ⟨hz.1, fun hr => hz.2 ((hboundary z hz.1).mpr hr)⟩
  · intro hz
    exact ⟨hz.1, fun hc => hz.2 ((hboundary z hz.1).mp hc)⟩

end RepulsiveCoulomb
