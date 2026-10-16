import LeanResearch.RepulsiveCoulomb.PointTranslatedStageFlatCharts
import LeanResearch.RepulsiveCoulomb.PointCleanRayRetainedHalfDisks
import LeanResearch.RepulsiveCoulomb.MetricRayAnchoredPatchUniqueness
import LeanResearch.RepulsiveCoulomb.PointTranslatedCornerSeed

/-! SOURCE-ONLY ASSEMBLY. Original geometric data for the initial translated
strip. The two trace fields are literal one-dimensional identifications in a
chosen actual local corner chart; they contain no two-dimensional rectangle,
strip, development family, continuation, no-return or first-contact premise.
Normalization of both old germs from an unoriented original corner is a
separate local adapter, not asserted by this structure.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

structure PointTranslatedOriginalData {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ha : ∀ j, 0 ≤ a j) (P : Set ℂ) where
  halfplane : ℂ ≃ₜ ℂ
  halfplane_eq : P = halfplane ⁻¹' planarClosedUpperHalfplane
  closed : IsClosed P
  pieceCount : ℕ
  pieces : Fin pieceCount → PointClosedBoundaryGeodesicPiece a y
  boundary_cover : frontier P = ⋃ i, range (pieces i).curve
  nu : ℂ →₀ ℝ
  alpha : ℂ →₀ ℝ
  budget : PointSignedBudgetInvariant nu alpha
  boundary_atom : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
    nu p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo)
  interior_support : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ pointSignedMarked nu alpha
  ray : NNReal → P
  ray_metric : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ray
  ray_frontier : ∀ t, (ray t).1 ∈ frontier P
  ray_clean : Disjoint ((↑(pointSignedMarked nu alpha) : Set ℂ) \ {(ray 0).1})
    (range (fun t ↦ (ray t).1))
  corner : PointRetainedConeNeighborhood a y P (ray 0).1
  corner_admissible : corner.Admissible
  corner_width_lt_pi : corner.flatPhysicalWidth < Real.pi
  corner_atom : nu (ray 0).1 = Real.pi - corner.flatPhysicalWidth
  edgeLength : ℝ
  edgeLength_pos : 0 < edgeLength
  edge : Icc (0 : ℝ) edgeLength → P
  edge_metric : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace edge
  edge_frontier : ∀ u, (edge u).1 ∈ frontier P
  germRadius : ℝ
  germRadius_pos : 0 < germRadius
  germRadius_edge : germRadius ≤ edgeLength
  lower_trace : ∀ t : NNReal, t.1 ≤ germRadius → corner.flatInverse (t : ℂ) = (ray t).1
  upper_trace : ∀ t : Icc (0 : ℝ) edgeLength, t.1 ≤ germRadius →
    corner.flatInverse (flatShearedPoint (conePhase corner.flatPhysicalWidth) 0 t.1) = (edge t).1

namespace PointTranslatedOriginalData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointTranslatedOriginalData a y ha P)

def angle : ℝ := D.corner.flatPhysicalWidth

theorem angle_pos : 0 < D.angle := D.corner.flatPhysicalWidth_pos

theorem angle_lt_pi : D.angle < Real.pi := D.corner_width_lt_pi

/-- One actual stage. This is not a user hypothesis in the final construction:
the width/length supremum quantifies over all such literal finite maps. -/
structure Stage (s : ℝ) (hs : 0 < s) (hsedge : s < D.edgeLength) (R : ℝ) where
  length_pos : 0 < R
  map : flatShearedRectangle (conePhase D.angle) R s → P
  metric : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace map
  bottom : ∀ r : Icc (0 : ℝ) R, map (shearedBottomPoint hs.le r) = D.ray ⟨r.1, r.2.1⟩
  compact_edge : ∀ u : Icc (0 : ℝ) s,
    map (shearedCompactEdgePoint length_pos.le u) = D.edge ⟨u.1, u.2.1, u.2.2.trans hsedge.le⟩

/-- Every positive-length, positive-height point of every ACTUAL stage has
its full chart derived from the original geometry. -/
theorem Stage.positive_flatChart {s delta R : ℝ} {hs : 0 < s} {hsedge : s < D.edgeLength}
    (T : D.Stage s hs hsedge R) (hsdelta : s ≤ delta)
    (hclear : ∀ z ∈ (↑(pointSignedMarked D.nu D.alpha) : Set ℂ) \ {(D.ray 0).1}, ∀ r : NNReal,
      delta < (pointSmoothConformalEDist a y z (D.ray r).1).toReal)
    (r : Icc (0 : ℝ) R) (hr : 0 < r.1) (u : Icc (0 : ℝ) s) (hu : 0 < u.1) :
    let q : flatShearedRectangle (conePhase D.angle) R s :=
      ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩
    (T.map q).1 ∈ interior P ∧ (T.map q).1 ∉ pointSignedMarked D.nu D.alpha ∧
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P) (T.map q)) :=
  point_translated_stage_positive_flatChart ha y D.halfplane D.halfplane_eq D.pieces D.boundary_cover
    D.budget D.boundary_atom D.interior_support D.angle_pos D.angle_lt_pi T.length_pos hs hsedge hsdelta
    D.ray D.ray_metric D.ray_frontier D.corner_atom hclear D.edge D.edge_metric D.edge_frontier
    T.map T.metric T.bottom T.compact_edge r hr u hu

theorem Stage.interior_flatChart {s delta R : ℝ} {hs : 0 < s} {hsedge : s < D.edgeLength}
    (T : D.Stage s hs hsedge R) (hsdelta : s ≤ delta)
    (hclear : ∀ z ∈ (↑(pointSignedMarked D.nu D.alpha) : Set ℂ) \ {(D.ray 0).1}, ∀ r : NNReal,
      delta < (pointSmoothConformalEDist a y z (D.ray r).1).toReal)
    (z : flatShearedRectangle (conePhase D.angle) R s)
    (hz : z.1 ∈ interior (flatShearedRectangle (conePhase D.angle) R s)) :
    Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P) (T.map z)) := by
  have hvi : (conePhase D.angle).im ≠ 0 := by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi D.angle_pos D.angle_lt_pi).ne'
  rw [flatShearedRectangle_interior hvi] at hz
  obtain ⟨⟨r,u⟩, ⟨hr,hu⟩, he⟩ := hz
  have hzq : z = ⟨flatShearedPoint (conePhase D.angle) r u,
      r, ⟨hr.1.le,hr.2.le⟩, u, ⟨hu.1.le,hu.2.le⟩, rfl⟩ := Subtype.ext he.symm
  rw [hzq]
  exact (Stage.positive_flatChart D T hsdelta hclear ⟨r,hr.1.le,hr.2.le⟩ hr.1
    ⟨u,hu.1.le,hu.2.le⟩ hu.1).2.2

theorem Stage.real_bottom {s R : ℝ} {hs : 0 < s} {hsedge : s < D.edgeLength}
    (T : D.Stage s hs hsedge R) (t : NNReal)
    (ht : (t : ℂ) ∈ flatShearedRectangle (conePhase D.angle) R s) : T.map ⟨(t : ℂ), ht⟩ = D.ray t := by
  have hcoords := ht
  obtain ⟨r,hr,u,hu,he⟩ := hcoords
  have hsin := Real.sin_pos_of_pos_of_lt_pi D.angle_pos D.angle_lt_pi
  have him := congrArg Complex.im he
  simp only [flatShearedPoint,Complex.ofReal_im,Complex.add_im,Complex.mul_im,
    Complex.ofReal_re,zero_mul,add_zero,zero_add,conePhase_im] at him
  have hu0 : u=0 := by nlinarith
  have hre := congrArg Complex.re he
  simp only [hu0,flatShearedPoint_zero,Complex.ofReal_re] at hre
  have htr : (t:ℝ)∈Icc (0:ℝ) R := hre.symm ▸ hr
  have hpoint : shearedBottomPoint (v := conePhase D.angle) hs.le ⟨t.1,htr⟩ = ⟨(t:ℂ),ht⟩ := by
    apply Subtype.ext
    simp [shearedBottomPoint]
  have h := T.bottom ⟨t.1,htr⟩
  rw [hpoint] at h
  exact h.trans (congrArg D.ray (Subtype.ext rfl))

/-- Arbitrary actual stages agree. The shared lower boundary supplies a
literal halfdisk and two anchors; all interior chart hypotheses are derived. -/
theorem stages_agree {s delta R T : ℝ} {hs : 0 < s} {hsedge : s < D.edgeLength}
    (F : D.Stage s hs hsedge R) (G : D.Stage s hs hsedge T) (hRT : R ≤ T)
    (hsdelta : s ≤ delta)
    (hclear : ∀ z ∈ (↑(pointSignedMarked D.nu D.alpha) : Set ℂ) \ {(D.ray 0).1}, ∀ r : NNReal,
      delta < (pointSmoothConformalEDist a y z (D.ray r).1).toReal) :
    ∀ z : flatShearedRectangle (conePhase D.angle) R s,
      F.map z = G.map ⟨z.1,flatShearedRectangle_mono hRT le_rfl z.2⟩ := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  have hvi : (conePhase D.angle).im ≠ 0 := by
    rw [conePhase_im]
    exact (Real.sin_pos_of_pos_of_lt_pi D.angle_pos D.angle_lt_pi).ne'
  have hc : 0 < R/2 := half_pos F.length_pos
  obtain ⟨C⟩ := pointCleanRay_exists_actual_retained_halfDisk ha y D.boundary_atom
    D.ray D.ray_metric D.ray_frontier D.ray_clean (⟨R/2,hc.le⟩ : NNReal) hc
  have hwindow : ∀ q∈Icc (R/2-R/4) (R/2+R/4), (q:ℂ)∈flatShearedRectangle (conePhase D.angle) R s := by
    intro q hq
    refine ⟨q,⟨by linarith [hq.1],by linarith [hq.2]⟩,0,⟨le_rfl,hs.le⟩,?_⟩
    simp
  exact metricRay_stages_agree D.ray D.ray_metric (by linarith : 0<R/4) (by linarith : R/4<R/2) C
    (flatShearedRectangle_convex _ _ _) (flatShearedRectangle_compact _ _ _).isClosed
    (flatShearedRectangle_interior_nonempty hvi F.length_pos hs)
    (flatShearedRectangle_mono hRT le_rfl) hwindow F.map G.map F.metric G.metric
    (Stage.real_bottom D F) (Stage.real_bottom D G) (Stage.interior_flatChart D F hsdelta hclear)

end PointTranslatedOriginalData
end RepulsiveCoulomb
