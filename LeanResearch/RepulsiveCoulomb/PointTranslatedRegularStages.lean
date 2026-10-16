module

public import LeanResearch.RepulsiveCoulomb.PointPositiveCornerUniformTranslatedStrip
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripStateAdapters
public import LeanResearch.RepulsiveCoulomb.TranslatedStripWidthSupremum

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The actual regular-width set is constructed here
from original geometric data. It is not a supplied compatible development or
extension certificate. Every pair of its actual maps agrees by the clean-ray
halfdisk and genuine full interior charts. The initial member is the actual
positive-corner producer. This file alone makes no maximal-contact claim. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

structure PointTranslatedRegularData {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ha : ∀ j, 0 ≤ a j) (P : Set ℂ) (ν α : ℂ →₀ ℝ) extends
    PointRetainedSignedHalfplaneState a y P ν α where
  budget : PointSignedBudgetInvariant ν α
  pieceCount : ℕ
  pieces : Fin pieceCount → PointClosedBoundaryGeodesicPiece a y
  boundary_cover : frontier P = ⋃ i, range (pieces i).curve
  ray : NNReal → P
  ray_metric : @Isometry NNReal P inferInstance
    (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ray
  ray_frontier : ∀ t, (ray t).1 ∈ frontier P
  ray_clean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {(ray 0).1})
    (range (fun t ↦ (ray t).1))
  corner : PointRetainedConeNeighborhood a y P (ray 0).1
  corner_admissible : corner.Admissible
  corner_lt_pi : corner.flatPhysicalWidth < Real.pi
  apex_budget_zero : α (ray 0).1 = 0

namespace PointTranslatedRegularData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} (D : PointTranslatedRegularData a y ha P ν α)

def angle : ℝ := D.corner.flatPhysicalWidth

theorem angle_pos : 0 < D.angle := D.corner.flatPhysicalWidth_pos

theorem angle_lt_pi : D.angle < Real.pi := D.corner_lt_pi

theorem direction_im_ne_zero : (conePhase D.angle).im ≠ 0 := by
  rw [conePhase_im]
  exact (Real.sin_pos_of_pos_of_lt_pi D.angle_pos D.angle_lt_pi).ne'

include D in
theorem boundary_formula (x : ℂ) (hx : x ∈ frontier P) :
    ∃ C : PointRetainedConeNeighborhood a y P x,
      ν x = Real.pi - (1 + coalescedPointExponent a y x / 2) * (C.hi - C.lo) := by
  obtain ⟨C, _, he⟩ := D.boundary_coeff x hx
  refine ⟨C, ?_⟩
  simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
    add_comm (coalescedPointExponent a y x / 2) 1] using he

include D in
theorem interior_marked (x : ℂ) (hx : x ∈ interior P)
    (he : coalescedPointExponent a y x ≠ 0) : x ∈ pointSignedMarked ν α := by
  apply (mem_pointSignedMarked ν α x).mpr
  left
  rw [D.interior_coeff x hx]
  exact mul_ne_zero (neg_ne_zero.mpr Real.pi_ne_zero) he

/-- Literal regular strip maps. Regularity describes their actual image, not
an oracle promising future extensions or an attained maximal contact. -/
structure Stage (s : ℝ) where
  positive : 0 < s
  map : flatShearedStrip (conePhase D.angle) s → P
  metric : @Isometry _ P inferInstance
    (pointRegionMetricSpace ha y P).toPseudoEMetricSpace map
  bottom : ∀ r : NNReal, map (translatedStripBottom positive.le r) = D.ray r
  edge_frontier : ∀ u : Icc (0 : ℝ) s, (map (translatedStripEdge u)).1 ∈ frontier P
  unmarked : ∀ z, (map z).1 ∉ (↑(pointSignedMarked ν α) : Set ℂ) \ {(D.ray 0).1}
  positive_interior : ∀ r : NNReal, 0 < r → ∀ u : Icc (0 : ℝ) s, 0 < u.1 →
    (map ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩).1 ∈ interior P

/-- A nonempty regular-width set is a conclusion of the actual corner theorem. -/
theorem exists_stage : ∃ s : ℝ, Nonempty (D.Stage s) := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  obtain ⟨s, hs, F, hd, hb, hm, hi, _, _, hc⟩ :=
    point_exists_positive_corner_uniform_translated_strip ha y D.ambient D.region_eq
      D.toPointRetainedSignedHalfplaneState.isClosed D.pieces D.boundary_cover
      D.budget D.boundary_formula D.interior_marked D.ray D.ray_metric
      D.ray_frontier D.ray_clean D.corner D.corner_admissible D.corner_lt_pi
  refine ⟨s, ⟨⟨hs, F, Isometry.of_dist_eq hd, hb, ?_, hm, hi⟩⟩⟩
  intro u
  have hmem : (F (translatedStripEdge u)).1 ∈ range (fun z ↦ (F z).1) ∩ frontier P := by
    rw [hc]
    exact Or.inr ⟨u, rfl⟩
  exact hmem.2

namespace Stage
variable {D} {s t : ℝ}

theorem real_bottom (T : D.Stage s) (r : NNReal)
    (hr : (r : ℂ) ∈ flatShearedStrip (conePhase D.angle) s) :
    T.map ⟨(r : ℂ), hr⟩ = D.ray r := by
  have he : (⟨(r : ℂ), hr⟩ : flatShearedStrip (conePhase D.angle) s) =
      translatedStripBottom T.positive.le r := by
    apply Subtype.ext
    simp only [translatedStripBottom, flatShearedPoint_zero]
  rw [he, T.bottom]

theorem exact_contact (T : D.Stage s) :
    range (fun z ↦ (T.map z).1) ∩ frontier P =
      range (fun r ↦ (T.map (translatedStripBottom T.positive.le r)).1) ∪
      range (fun u ↦ (T.map (translatedStripEdge u)).1) := by
  ext x
  constructor
  · rintro ⟨⟨z, rfl⟩, hzfront⟩
    obtain ⟨r, hr, u, hu, hz⟩ := z.2
    by_cases hr0 : r = 0
    · right
      refine ⟨⟨u, hu⟩, ?_⟩
      apply congrArg (fun z ↦ (T.map z).1)
      apply Subtype.ext
      change flatShearedPoint (conePhase D.angle) 0 u = z.1
      simpa only [hr0] using hz.symm
    · by_cases hu0 : u = 0
      · left
        refine ⟨⟨r, hr⟩, ?_⟩
        apply congrArg (fun z ↦ (T.map z).1)
        apply Subtype.ext
        change flatShearedPoint (conePhase D.angle) r 0 = z.1
        simpa only [hu0] using hz.symm
      · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
        have hupos : 0 < u := lt_of_le_of_ne hu.1 (Ne.symm hu0)
        have he : z = ⟨flatShearedPoint (conePhase D.angle) r u, r, hr, u, hu, rfl⟩ :=
          Subtype.ext hz
        exact False.elim (hzfront.2 (he.symm ▸ T.positive_interior ⟨r, hr⟩ hrpos ⟨u, hu⟩ hupos))
  · rintro (⟨r, rfl⟩ | ⟨u, rfl⟩)
    · refine ⟨mem_range_self _, ?_⟩
      change (T.map (translatedStripBottom T.positive.le r)).1 ∈ frontier P
      rw [T.bottom]
      exact D.ray_frontier r
    · exact ⟨mem_range_self _, T.edge_frontier u⟩

theorem closed_proper (T : D.Stage s) :
    IsClosedEmbedding (fun z ↦ (T.map z).1) ∧ IsProperMap (fun z ↦ (T.map z).1) := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  exact pointTranslatedStrip_closed_proper ha y D.direction_im_ne_zero T.map
    (fun x z ↦ T.metric.dist_eq x z)

/-- Clean full-disk charts are derived from actual stage image regularity. -/
theorem positive_flatChart (T : D.Stage s) (r : NNReal) (hr : 0 < r)
    (u : Icc (0 : ℝ) s) (hu : 0 < u.1) :
    Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P)
      (T.map ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩)) := by
  let q : flatShearedStrip (conePhase D.angle) s :=
    ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩
  have hi : (T.map q).1 ∈ interior P := T.positive_interior r hr u hu
  have hp : (T.map q).1 ≠ (D.ray 0).1 := fun he ↦ (D.ray_frontier 0).2 (he ▸ hi)
  have hm : (T.map q).1 ∉ pointSignedMarked ν α := fun hm ↦ T.unmarked q ⟨hm, hp⟩
  have he : coalescedPointExponent a y (T.map q).1 = 0 := by
    by_contra hn
    exact hm (D.interior_marked _ hi hn)
  exact exists_pointInterior_zeroExponent_flatDiskChart ha y hi he

/-- Restricting an actual regular strip gives another actual regular strip. -/
def restrict (T : D.Stage t) (hs : 0 < s) (hst : s ≤ t) : D.Stage s where
  positive := hs
  map := T.map ∘ Set.inclusion (flatShearedStrip_mono hst)
  metric := by
    let M := pointRegionMetricSpace ha y P
    letI : MetricSpace P := M
    letI : PseudoMetricSpace P := M.toPseudoMetricSpace
    letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
    exact T.metric.comp (show Isometry (Set.inclusion (flatShearedStrip_mono hst)) from fun _ _ ↦ rfl)
  bottom := T.bottom
  edge_frontier := fun u ↦ T.edge_frontier ⟨u.1, u.2.1, u.2.2.trans hst⟩
  unmarked := fun z ↦ T.unmarked _
  positive_interior := fun r hr u hu ↦ T.positive_interior r hr ⟨u.1, u.2.1, u.2.2.trans hst⟩ hu

end Stage

/-- Compatibility is proved, never supplied. The finite rectangle needed for
the anchored uniqueness theorem is cut from the actual unbounded strip. -/
theorem stages_agree {s t : ℝ} (F : D.Stage s) (G : D.Stage t) (hst : s ≤ t) :
    ∀ z : flatShearedStrip (conePhase D.angle) s,
      F.map z = G.map ⟨z.1, flatShearedStrip_mono hst z.2⟩ := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  intro z
  obtain ⟨r, hr, u, hu, hz⟩ := z.2
  let R := r + 1
  have hR : 0 < R := by dsimp [R]; linarith
  have hrect : flatShearedRectangle (conePhase D.angle) R s ⊆ flatShearedStrip (conePhase D.angle) s := by
    rintro w ⟨q, hq, v, hv, rfl⟩
    exact ⟨q, hq.1, v, hv, rfl⟩
  let f := F.map ∘ Set.inclusion hrect
  have hf : Isometry f := F.metric.comp (show Isometry (Set.inclusion hrect) from fun _ _ ↦ rfl)
  have hKL := hrect.trans (flatShearedStrip_mono hst)
  obtain ⟨C⟩ := pointCleanRay_exists_actual_retained_halfDisk ha y D.boundary_formula
    D.ray D.ray_metric D.ray_frontier D.ray_clean (⟨R / 2, (half_pos hR).le⟩ : NNReal) (half_pos hR)
  have hw : ∀ q ∈ Icc (R / 2 - R / 4) (R / 2 + R / 4),
      (q : ℂ) ∈ flatShearedRectangle (conePhase D.angle) R s := by
    intro q hq
    refine ⟨q, ⟨by linarith [hq.1], by linarith [hq.2]⟩, 0, ⟨le_rfl, F.positive.le⟩, ?_⟩
    simp only [flatShearedPoint_zero]
  have hregular (w : flatShearedRectangle (conePhase D.angle) R s)
      (hw : w.1 ∈ interior (flatShearedRectangle (conePhase D.angle) R s)) :
      Nonempty (MetricFlatDiskChart P (f w)) := by
    rw [flatShearedRectangle_interior D.direction_im_ne_zero] at hw
    obtain ⟨⟨q, v⟩, ⟨hq, hv⟩, he⟩ := hw
    have hew : w = ⟨flatShearedPoint (conePhase D.angle) q v,
        q, ⟨hq.1.le, hq.2.le⟩, v, ⟨hv.1.le, hv.2.le⟩, rfl⟩ := Subtype.ext he.symm
    rw [hew]
    exact F.positive_flatChart ⟨q, hq.1.le⟩ hq.1 ⟨v, hv.1.le, hv.2.le⟩ hv.1
  have hagree := metricRay_stages_agree D.ray D.ray_metric
    (by linarith : 0 < R / 4) (by linarith : R / 4 < R / 2) C
    (flatShearedRectangle_convex _ _ _) (flatShearedRectangle_compact _ _ _).isClosed
    (flatShearedRectangle_interior_nonempty D.direction_im_ne_zero hR F.positive)
    hKL hw f G.map hf G.metric
    (fun q hq ↦ F.real_bottom q (hrect hq)) (Stage.real_bottom G) hregular
  have hzrect : z.1 ∈ flatShearedRectangle (conePhase D.angle) R s :=
    ⟨r, ⟨hr, by dsimp [R]; linarith⟩, u, hu, hz⟩
  exact hagree ⟨z.1, hzrect⟩

/-- The actual widths, defined by existential quantification over all literal
regular maps. No chosen sequence or extension property is an input. -/
def regularWidths : Set ℝ := {s | Nonempty (D.Stage s)}

theorem regularWidths_nonempty : D.regularWidths.Nonempty := D.exists_stage

theorem regularWidths_positive : ∀ s ∈ D.regularWidths, 0 < s := by
  rintro s ⟨T⟩
  exact T.positive

end PointTranslatedRegularData
end RepulsiveCoulomb
