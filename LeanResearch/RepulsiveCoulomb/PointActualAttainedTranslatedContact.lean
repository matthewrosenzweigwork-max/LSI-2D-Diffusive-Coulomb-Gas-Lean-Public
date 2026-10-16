import LeanResearch.RepulsiveCoulomb.PointActualFiniteMaximalWidth
import LeanResearch.RepulsiveCoulomb.PointTranslatedUnmarkedLimitRegular
import LeanResearch.RepulsiveCoulomb.PointTranslatedRegularStripExtension
import LeanResearch.RepulsiveCoulomb.PointTranslatedContactAngle

/-! SOURCE-ONLY, UNCOMPILED. Actual finite maximal-width marked-contact
attainment. The width set, nonempty initial strip, compatibility, finite bound,
Cauchy limit, no-mark top regularization, actual residual construction, extra
uniform strip and seam glue are all constructed by the selected dependencies.
No stage family, extension certificate, limiting map, first-contact gap or
marked-contact premise is an original input.

This endpoint still starts with genuine clean outward ray/positive corner
data. It does not select that ray from an arbitrary marked boundary, and does
not claim exact old-boundary contact or positive residual angle at a marked
limiting attachment. Those are separately named remaining obligations. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb.PointTranslatedRegularData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j,0≤a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} (D : PointTranslatedRegularData a y ha P ν α)

namespace FiniteWidthLimit
variable {D} (K : D.FiniteWidthLimit)

/-- The attained closed map has a genuinely new marked point, rather than
only a sequence of regular widths tending toward one. -/
theorem exists_new_marked_point :
    ∃ q : flatShearedStrip (conePhase D.angle) (sSup D.regularWidths),
      (K.map q).1∈(↑(pointSignedMarked ν α):Set ℂ)\{(D.ray 0).1} := by
  by_contra hn
  push_neg at hn
  obtain ⟨t,ht,⟨T⟩⟩ := (K.toRegularStage hn).exists_wider
  have hle : t ≤ sSup D.regularWidths := le_csSup K.bounded (show t∈D.regularWidths from ⟨T⟩)
  exact (not_lt_of_ge hle) ht

/-- The contact lies on the actual free ray; every point below it is already
proved unmarked, including the open compact edge. -/
theorem exists_new_marked_top_contact : ∃ r : NNReal,
    (K.map (translatedStripTop K.positive.le r)).1∈
      (↑(pointSignedMarked ν α):Set ℂ)\{(D.ray 0).1} := by
  obtain ⟨q,hq⟩ := K.exists_new_marked_point
  obtain ⟨r,hr⟩ := K.new_marked_on_top (mem_range_self q) hq
  change (K.map (translatedStripTop K.positive.le r)).1 = (K.map q).1 at hr
  refine ⟨r, ?_⟩
  rw [hr]
  exact hq

end FiniteWidthLimit

/-- Original genuine corner inputs now construct finite positive width,
its actual closed proper all-pairs isometry, and attained new marked contact.
All compatibility and continuation data remain produced internally. -/
theorem construct_attained_translated_contact :
    ∃ K : D.FiniteWidthLimit, ∃ r : NNReal,
      (K.map (translatedStripTop K.positive.le r)).1∈
        (↑(pointSignedMarked ν α):Set ℂ)\{(D.ray 0).1} := by
  obtain ⟨K⟩ := D.construct_finite_maximal_width
  exact ⟨K,K.exists_new_marked_top_contact⟩


/-- The attained contact also carries a genuinely selected old corner chart,
its exact signed coefficient and nonnegative remaining angle. Positive budget
at that corner already gives strictness. The zero-budget case is not hidden. -/
theorem construct_attained_contact_with_corner_bound :
    ∃ K : D.FiniteWidthLimit,
      (∃ r : NNReal,(K.map (translatedStripTop K.positive.le r)).1∈
        (↑(pointSignedMarked ν α):Set ℂ)\{(D.ray 0).1}) ∧
      ∃ C : PointRetainedConeNeighborhood a y P
        (K.map (translatedStripTop K.positive.le 0)).1,
        C.Admissible ∧
        ν (K.map (translatedStripTop K.positive.le 0)).1=Real.pi-C.flatPhysicalWidth ∧
        Real.pi-D.angle≤C.flatPhysicalWidth ∧
        (0<α (K.map (translatedStripTop K.positive.le 0)).1 →
          Real.pi-D.angle<C.flatPhysicalWidth) := by
  obtain ⟨K,hcontact⟩ := D.construct_attained_translated_contact
  obtain ⟨C,hC,hνC⟩ := D.boundary_coeff _ K.contact_origin_frontier
  exact ⟨K,hcontact,C,hC,hνC,
    sub_nonneg.mp (K.corner_residual_nonnegative C hC),
    K.corner_residual_positive_of_budget_positive C hC⟩

end RepulsiveCoulomb.PointTranslatedRegularData
