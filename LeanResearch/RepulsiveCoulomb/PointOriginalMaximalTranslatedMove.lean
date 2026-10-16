module

public import LeanResearch.RepulsiveCoulomb.PointOriginalAttainedTranslatedContact
public import LeanResearch.RepulsiveCoulomb.PointOriginalStrictTranslatedCorner
public import LeanResearch.RepulsiveCoulomb.PointTranslatedNextGeometricState

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. A genuine maximal translated-strip move from the
current signed halfplane, marked frontier and absence of a clean budget ray.
The endpoint constructs the extreme ray/corner, finite positive maximal width,
attained new marked contact, strict residual angle, exact old-boundary contact,
literal residual and next reusable current state. No future geometry or
continuation certificate is an input. Inner-rank descent and finite repeated
preparation are separate subsequent results. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

namespace PointTranslatedRegularData.FiniteWidthLimit
variable {m : ℕ} {a : Fin m→ℝ} {y : Fin m→ℂ} {ha : ∀ j,0≤a j}
  {P : Set ℂ} {ν α : ℂ→₀ℝ} {D : PointTranslatedRegularData a y ha P ν α}

def cutImage (L : D.FiniteWidthLimit) : Set ℂ := range (fun q ↦ (L.map q).1)
def cutRay (L : D.FiniteWidthLimit) : NNReal→ℂ := fun r ↦ (L.map (translatedStripTop L.positive.le r)).1
def cutRegion (L : D.FiniteWidthLimit) : Set ℂ := closure (P\L.cutImage)
def cutApex (L : D.FiniteWidthLimit) : ℂ := (L.map (translatedStripBottom L.positive.le 0)).1
def cutCurvature (L : D.FiniteWidthLimit) : ℂ→₀ℝ := BoundaryPreparation.transfer ν L.cutApex (L.cutRay 0)

end PointTranslatedRegularData.FiniteWidthLimit

/-- An output package of constructed geometry. The final producer below
constructs every field from the original current region; callers do not
supply a stage, limiting map, contact, positive angle or residual state. -/
structure PointConstructedTranslatedMove {m : ℕ} (a : Fin m→ℝ) (y : Fin m→ℂ)
    (ha : ∀ j,0≤a j) (P : Set ℂ) (ν α : ℂ→₀ℝ) where
  data : PointTranslatedRegularData a y ha P ν α
  limit : data.FiniteWidthLimit
  corner : PointRetainedConeNeighborhood a y P (limit.cutRay 0)
  corner_admissible : corner.Admissible
  remaining_positive : Real.pi-data.angle<corner.flatPhysicalWidth
  attained : ∃ r : NNReal,limit.cutRay r∈(↑(pointSignedMarked ν α):Set ℂ)\{limit.cutApex}
  exact_old_contact : limit.cutImage∩frontier P=
    range (fun r ↦ (limit.map (translatedStripBottom limit.positive.le r)).1) ∪
    range (fun u ↦ (limit.map (translatedStripEdge u)).1)
  residual : PointTranslatedStripIterationOutput a y P limit.cutImage limit.cutRegion limit.cutRay
    limit.cutApex ν limit.cutCurvature α (Real.pi-data.angle) corner
  next : PointGeometricCutState a y limit.cutRegion limit.cutCurvature α
  next_state : next.toPointRetainedSignedHalfplaneState=residual.state
  next_pieceCount : next.pieceCount=data.pieceCount+1
  bottom_removed : ∀ r,(limit.map (translatedStripBottom limit.positive.le r)).1∉limit.cutRegion
  open_edge_removed : ∀ u : Icc (0:ℝ) (sSup data.regularWidths),u.1<sSup data.regularWidths→
    (limit.map (translatedStripEdge u)).1∉limit.cutRegion

/-- Original Pro maximal translated-strip move. Every load-bearing geometric
fact is constructed before the next state is packaged. This does not yet claim
that iterating these moves terminates or that a complete allocation follows. -/
theorem PointGeometricCutState.construct_maximal_translated_move
    {m : ℕ} {a : Fin m→ℝ} (ha : ∀ j,0≤a j) (y : Fin m→ℂ)
    {P : Set ℂ} {ν α : ℂ→₀ℝ} (K : PointGeometricCutState a y P ν α)
    (hmarked : ∃ x,x∈pointSignedMarked ν α ∧ x∈frontier P)
    (hno : ¬ Nonempty K.CleanRay) :
    Nonempty (PointConstructedTranslatedMove a y ha P ν α) := by
  obtain ⟨R⟩ := K.exists_positive_extreme_boundary_ray ha y hmarked hno
  let D := K.translatedDataOfExtreme ha R
  obtain ⟨L,hcontact⟩ := D.construct_attained_translated_contact
  obtain ⟨C,hC,hνC⟩ := D.boundary_coeff _ L.contact_origin_frontier
  have hremain := L.corner_residual_positive_of_no_clean (K.no_clean_iff_literal.mp hno) C hC
  have hexact := L.exact_old_contact_of_positive_residual C hC hremain
  obtain ⟨⟨O⟩,hbottom,hedge⟩ := L.construct_actual_residual_of_positive_angle C hC hremain
  change PointTranslatedStripIterationOutput a y P L.cutImage L.cutRegion L.cutRay
    L.cutApex ν L.cutCurvature α (Real.pi-D.angle) C at O
  obtain ⟨J,hJ,hN⟩ := O.exists_next_geometric_state ha
    D.toPointRetainedSignedHalfplaneState.isClosed D.pieces D.boundary_cover D.budget
  have hattained : ∃ r : NNReal,L.cutRay r∈(↑(pointSignedMarked ν α):Set ℂ)\{L.cutApex} := by
    simpa only [PointTranslatedRegularData.FiniteWidthLimit.cutRay,
      PointTranslatedRegularData.FiniteWidthLimit.cutApex,L.bottom] using hcontact
  exact ⟨{
    data := D
    limit := L
    corner := C
    corner_admissible := hC
    remaining_positive := hremain
    attained := hattained
    exact_old_contact := hexact
    residual := O
    next := J
    next_state := hJ
    next_pieceCount := hN
    bottom_removed := hbottom
    open_edge_removed := hedge }⟩

end RepulsiveCoulomb
