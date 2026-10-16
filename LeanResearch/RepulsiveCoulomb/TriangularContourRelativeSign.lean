import LeanResearch.RepulsiveCoulomb.TriangularContourInterior
import LeanResearch.RepulsiveCoulomb.FinitePolygonLevelSign

/-! Actual regular interpolant level sides on a connected physical observation
set are controlled by the interiors of the contour components meeting that set. -/
noncomputable section
open Set Schoenflies
open scoped Function
namespace RepulsiveCoulomb

theorem gridContour_relative_sign_cover (v : (ℤ × ℤ) →₀ ℝ) {t : ℝ}
    (ht : t ∉ gridExceptionalLevels v) {B : Set ℂ} (hB : IsConnected B) :
    (B ∩ {z | triangularGridInterpolant v z < t} ⊆
      ⋃ c : (gridContourGraph v t).ConnectedComponent,
        ⋃ (_ : (gridContourComponentCarrier v t c ∩ B).Nonempty), gridContourComponentInterior v t c) ∨
    (B ∩ {z | t < triangularGridInterpolant v z} ⊆
      ⋃ c : (gridContourGraph v t).ConnectedComponent,
        ⋃ (_ : (gridContourComponentCarrier v t c ∩ B).Nonempty), gridContourComponentInterior v t c) := by
  classical
  let e := Complex.orthonormalBasisOneI.repr
  letI : Fintype (gridContourGraph v t).ConnectedComponent := Fintype.ofFinite _
  have hp : ∀ c : (gridContourGraph v t).ConnectedComponent,
      ∃ n : ℕ, ∃ P : ClosedPolygon n, P.carrier = e '' gridContourComponentCarrier v t c := by
    intro c
    exact exists_closedPolygon (gridContourComponent_isJordan_polygon v ht c).1
      (gridContourComponent_isJordan_polygon v ht c).2
  choose n P hP using hp
  let f : Plane → ℝ := fun x => triangularGridInterpolant v (e.symm x)
  have hf : Continuous f := (triangularGridInterpolant_lipschitz v).continuous.comp e.symm.continuous
  have hlevel : f ⁻¹' {t} = ⋃ c ∈ (Finset.univ : Finset (gridContourGraph v t).ConnectedComponent),
      (P c).carrier := by
    have hlev : f ⁻¹' {t} = e '' ((triangularGridInterpolant v) ⁻¹' {t}) := by
      ext x
      constructor
      · intro hx
        exact ⟨e.symm x,hx,e.apply_symm_apply x⟩
      · rintro ⟨z,hz,rfl⟩
        simpa [f] using hz
    rw [hlev, ← gridContourComponent_plane_union v ht]
    simp only [hP, Finset.mem_univ, iUnion_true]
    rfl
  have hdis : ((Finset.univ : Finset (gridContourGraph v t).ConnectedComponent) : Set _).Pairwise
      (Disjoint on fun c => (P c).carrier) := by
    intro c _ d _ hcd
    change Disjoint (P c).carrier (P d).carrier
    rw [hP,hP]
    exact gridContourComponent_plane_disjoint v ht hcd
  have hmeet : ∀ c, ((P c).carrier ∩ e '' B).Nonempty →
      (gridContourComponentCarrier v t c ∩ B).Nonempty := by
    intro c hc
    rw [hP] at hc
    obtain ⟨x,⟨z,hz,hzx⟩,⟨w,hw,hwx⟩⟩ := hc
    have hzw := e.injective (hzx.trans hwx.symm)
    subst w
    exact ⟨z,hz,hw⟩
  have htrans : ∀ z, e z ∈
      (⋃ c ∈ (Finset.univ : Finset (gridContourGraph v t).ConnectedComponent),
        ⋃ (_ : ((P c).carrier ∩ e '' B).Nonempty), inside (P c).carrier) →
      z ∈ (⋃ c : (gridContourGraph v t).ConnectedComponent,
        ⋃ (_ : (gridContourComponentCarrier v t c ∩ B).Nonempty), gridContourComponentInterior v t c) := by
    intro z hz
    obtain ⟨c,hz⟩ := mem_iUnion.mp hz
    obtain ⟨_,hz⟩ := mem_iUnion.mp hz
    obtain ⟨hc,hz⟩ := mem_iUnion.mp hz
    rw [hP] at hz
    exact mem_iUnion.mpr ⟨c,mem_iUnion.mpr ⟨hmeet c hc,hz⟩⟩
  have hsign := finite_polygon_level_sign_cover n P Finset.univ
    (hB.image e e.continuous.continuousOn) hdis hf t hlevel
  rcases hsign with hlo | hhi
  · left
    intro z hz
    apply htrans z
    apply hlo
    exact ⟨mem_image_of_mem e hz.1, by simpa [f] using hz.2⟩
  · right
    intro z hz
    apply htrans z
    apply hhi
    exact ⟨mem_image_of_mem e hz.1, by simpa [f] using hz.2⟩

end RepulsiveCoulomb
