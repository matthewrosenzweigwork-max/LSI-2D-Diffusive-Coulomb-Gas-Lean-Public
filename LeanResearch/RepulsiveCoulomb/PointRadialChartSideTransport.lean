import LeanResearch.RepulsiveCoulomb.PointRadialJordanSideChoice
import Mathlib.Topology.OpenPartialHomeomorph.IsImage

/-! Transport actual Jordan regions into a local chart and back. The side
choice is derived from the actual region partition and frontier incidences;
only the explicit normalized two-ray boundary equation is consumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Actual open regions with a common boundary vertex choose opposite sectors
in every chart whose local boundary is the specified two rays. -/
theorem pointRadialChart_region_side_choice {X : Type*} [TopologicalSpace X]
    {C U V : Set X} (hU : IsOpen U) (hV : IsOpen V) (hd : Disjoint U V)
    (hcover : U ∪ V = Cᶜ) {p : X} (hpU : p ∈ closure U) (hpV : p ∈ closure V)
    (e : OpenPartialHomeomorph X ℂ) (hp : p ∈ e.source) (hep : e p = 0)
    {R θ : ℝ} (hR : 0 < R) (hθ0 : 0 < θ) (hθ2 : θ < 2 * Real.pi)
    (hball : ball (0 : ℂ) R ⊆ e.target)
    (hboundary : ∀ z ∈ ball (0 : ℂ) R,
      e.symm z ∈ C ↔ z ∈ pointDiskRay R 0 ∪ pointDiskRay R θ) :
    (MapsTo e.symm (pointOpenRadialSector R 0 θ) U ∧
      MapsTo e.symm (pointOpenRadialSector R θ (2 * Real.pi)) V) ∨
      (MapsTo e.symm (pointOpenRadialSector R 0 θ) V ∧
        MapsTo e.symm (pointOpenRadialSector R θ (2 * Real.pi)) U) := by
  let U' : Set ℂ := e.target ∩ e.symm ⁻¹' U
  let V' : Set ℂ := e.target ∩ e.symm ⁻¹' V
  let C' : Set ℂ := e.target ∩ e.symm ⁻¹' C
  have hU' : IsOpen U' := e.isOpen_inter_preimage_symm hU
  have hV' : IsOpen V' := e.isOpen_inter_preimage_symm hV
  have hd' : Disjoint U' V' := by
    apply disjoint_left.mpr
    intro z hzU hzV
    exact disjoint_left.mp hd hzU.2 hzV.2
  have hIU : e.IsImage U U' := by
    intro x hx
    change e x ∈ e.target ∩ e.symm ⁻¹' U ↔ x ∈ U
    simp only [mem_inter_iff, mem_preimage, e.left_inv hx, e.map_source hx, true_and]
  have hIV : e.IsImage V V' := by
    intro x hx
    change e x ∈ e.target ∩ e.symm ⁻¹' V ↔ x ∈ V
    simp only [mem_inter_iff, mem_preimage, e.left_inv hx, e.map_source hx, true_and]
  have h0U : (0 : ℂ) ∈ closure U' := by
    rw [← hep]
    exact (hIU.closure hp).mpr hpU
  have h0V : (0 : ℂ) ∈ closure V' := by
    rw [← hep]
    exact (hIV.closure hp).mpr hpV
  have hcover' : ∀ z ∈ ball (0 : ℂ) R, z ∉ C' ↔ z ∈ U' ∨ z ∈ V' := by
    intro z hz
    have hzt := hball hz
    change ¬ (z ∈ e.target ∧ e.symm z ∈ C) ↔
      (z ∈ e.target ∧ e.symm z ∈ U) ∨ (z ∈ e.target ∧ e.symm z ∈ V)
    simp only [hzt, true_and]
    change e.symm z ∈ Cᶜ ↔ e.symm z ∈ U ∪ V
    rw [hcover]
  have hboundary' : ∀ z ∈ ball (0 : ℂ) R,
      z ∈ C' ↔ z ∈ pointDiskRay R 0 ∪ pointDiskRay R θ := by
    intro z hz
    change (z ∈ e.target ∧ e.symm z ∈ C) ↔ _
    simp only [hball hz, true_and]
    exact hboundary z hz
  rcases pointRadialBoundary_jordan_side_choice hR hθ0 hθ2 hU' hV' hd' h0U h0V
    hcover' hboundary' with hh | hh
  · exact Or.inl ⟨fun _ hz => (hh.1 hz).2, fun _ hz => (hh.2 hz).2⟩
  · exact Or.inr ⟨fun _ hz => (hh.1 hz).2, fun _ hz => (hh.2 hz).2⟩

end RepulsiveCoulomb
