module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicTriangleSubedges
public import LeanResearch.RepulsiveCoulomb.Imported.Schoenflies.Concatenate

@[expose] public section

/-! The extracted three minimizing subedges form a genuine Jordan curve via
the approved arbitrary-arc concatenation theorem, without polygonal substitution. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointGeodesicTreeEdge_isArc {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) :
    Schoenflies.IsArcBetween (Complex.orthonormalBasisOneI.repr '' range E.curve)
      (Complex.orthonormalBasisOneI.repr E.start) (Complex.orthonormalBasisOneI.repr E.finish) := by
  have h := isArcBetween_of_continuous_injective_interval
    (Complex.orthonormalBasisOneI.repr ∘ E.curve)
    (Complex.orthonormalBasisOneI.repr.continuous.comp E.continuous)
    (Complex.orthonormalBasisOneI.repr.injective.comp (pointGeodesicTree_edges_injective ha y E))
  simpa only [range_comp, Function.comp_apply, E.curve_start, E.curve_finish] using h

/-- The three actual sides, with their proved singleton intersections, determine
an honest Jordan curve and hence have an actual bounded inside component. -/
theorem pointSimpleGeodesicTriangle_jordan {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {q : ℂ}
    (T : PointSimpleGeodesicTriangle a y q) :
    Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr ''
      (range T.left.curve ∪ range T.right.curve ∪ range T.cross.curve)) := by
  let φ := Complex.orthonormalBasisOneI.repr
  have hleft := pointGeodesicTreeEdge_isArc ha y T.left
  have hright := pointGeodesicTreeEdge_isArc ha y T.right
  have hcross := pointGeodesicTreeEdge_isArc ha y T.cross
  rw [T.left_start] at hleft
  rw [T.right_start] at hright
  rw [T.cross_start, T.cross_finish] at hcross
  have hlegs : (φ '' range T.left.curve) ∩ (φ '' range T.right.curve) = {φ q} := by
    rw [← image_inter φ.injective, T.legs_meet, image_singleton]
  have hCL : (φ '' range T.cross.curve) ∩ (φ '' range T.left.curve) = {φ T.left.finish} := by
    rw [← image_inter φ.injective, T.cross_left, image_singleton, T.cross_start]
  have hCR : (φ '' range T.cross.curve) ∩ (φ '' range T.right.curve) = {φ T.right.finish} := by
    rw [← image_inter φ.injective, T.cross_right, image_singleton, T.cross_finish]
  have hjoin := hleft.reverse.concatenate hright (fun z hzL hzR ↦
    mem_singleton_iff.mp (hlegs ▸ And.intro hzL hzR))
  have hj := Schoenflies.IsJordanCurve.of_two_arcs hjoin hcross.reverse (by
    intro z hz hzC
    rcases hz with hzL | hzR
    · exact Or.inl (mem_singleton_iff.mp (hCL ▸ And.intro hzC hzL))
    · exact Or.inr (mem_singleton_iff.mp (hCR ▸ And.intro hzC hzR)))
  simpa only [image_union] using hj

end RepulsiveCoulomb
