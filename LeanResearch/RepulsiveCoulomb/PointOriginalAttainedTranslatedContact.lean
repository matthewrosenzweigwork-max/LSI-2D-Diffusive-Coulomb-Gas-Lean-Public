module

public import LeanResearch.RepulsiveCoulomb.PointOriginalExtremeBoundaryRay
public import LeanResearch.RepulsiveCoulomb.PointActualAttainedTranslatedContact

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The actual current-region marked-boundary and
no-clean-budget-ray obstruction now produces the extreme marked corner, its
complete clean minimizing outward ray, and the attained finite maximal-width
translated strip. No ray, corner, edge, initial strip, development family,
extension certificate, supremum bound or marked-contact witness is an input.
Strict zero-allocation residual angle and exact marked-limit old-boundary
contact remain separate geometric work, not claimed by this producer. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb.PointGeometricCutState
variable {m : ℕ} {a : Fin m→ℝ} {y : Fin m→ℂ}
  {P : Set ℂ} {ν α : ℂ→₀ℝ}

/-- Convert the constructed extreme end to exactly the genuine-input strip
producer. This does not postulate either of its fields: every field is taken
from the actual current region or the constructed extreme-end output. -/
def translatedDataOfExtreme (K : PointGeometricCutState a y P ν α)
    (ha : ∀ j,0≤a j) {β : ℝ→ℂ} {clock : ℂ→ℝ}
    (R : PointExtremeBoundaryRay a y P ν α β clock) :
    PointTranslatedRegularData a y ha P ν α := by
  let ρ : NNReal→P := fun t ↦
    ⟨R.ray t,K.toPointRetainedSignedHalfplaneState.isClosed.frontier_subset (R.frontier t)⟩
  let C : PointRetainedConeNeighborhood a y P (ρ 0).1 := by
    change PointRetainedConeNeighborhood a y P (R.ray 0)
    exact R.start.symm ▸ R.chart
  have hcastAdmissible {p q : ℂ} (B : PointRetainedConeNeighborhood a y P p) (he : p = q) :
      (he ▸ B : PointRetainedConeNeighborhood a y P q).Admissible ↔ B.Admissible := by
    cases he
    rfl
  have hcastWidth {p q : ℂ} (B : PointRetainedConeNeighborhood a y P p) (he : p = q) :
      (he ▸ B : PointRetainedConeNeighborhood a y P q).flatPhysicalWidth = B.flatPhysicalWidth := by
    cases he
    rfl
  have hC : C.Admissible := (hcastAdmissible R.chart R.start.symm).mpr R.admissible
  have hCπ : C.flatPhysicalWidth<Real.pi := by
    have hwidth : C.flatPhysicalWidth = R.chart.flatPhysicalWidth := hcastWidth R.chart R.start.symm
    exact hwidth.trans_lt R.width_lt_pi
  exact {
    toPointRetainedSignedHalfplaneState := K.toPointRetainedSignedHalfplaneState
    budget := K.budget
    pieceCount := K.pieceCount
    pieces := K.pieces
    boundary_cover := K.boundary_cover
    ray := ρ
    ray_metric := by
      let M := pointRegionMetricSpace ha y P
      letI : MetricSpace P := M
      letI : PseudoMetricSpace P := M.toPseudoMetricSpace
      letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
      exact Isometry.of_dist_eq R.metric
    ray_frontier := R.frontier
    ray_clean := by simpa only [ρ,R.start] using R.clean
    corner := C
    corner_admissible := hC
    corner_lt_pi := hCπ
    apex_budget_zero := by simpa only [ρ,R.start] using R.allocation_zero }

@[simp] theorem translatedDataOfExtreme_ray_val (K : PointGeometricCutState a y P ν α)
    (ha : ∀ j,0≤a j) {β : ℝ→ℂ} {clock : ℂ→ℝ}
    (R : PointExtremeBoundaryRay a y P ν α β clock) (t : NNReal) :
    ((K.translatedDataOfExtreme ha R).ray t).1=R.ray t := rfl

/-- Actual original-current-region finite maximal-strip marked-contact
producer. The selected extreme point and ray remain available in the output
for the subsequent zero-residual-angle argument. -/
theorem construct_original_attained_translated_contact
    (ha : ∀ j,0≤a j) (y : Fin m→ℂ)
    {P : Set ℂ} {ν α : ℂ→₀ℝ} (K : PointGeometricCutState a y P ν α)
    (hmarked : ∃ x,x∈pointSignedMarked ν α ∧ x∈frontier P)
    (hno : ¬ Nonempty K.CleanRay) :
    ∃ R : PointExtremeBoundaryRay a y P ν α
        (pointHalfplaneBoundaryClock K.ambient) (fun x ↦ (K.ambient x).re),
      ∃ L : (K.translatedDataOfExtreme ha R).FiniteWidthLimit,
        ∃ t : NNReal,(L.map (translatedStripTop L.positive.le t)).1∈
          (↑(pointSignedMarked ν α):Set ℂ)\{R.point} := by
  obtain ⟨R⟩ := K.exists_positive_extreme_boundary_ray ha y hmarked hno
  obtain ⟨L,t,ht⟩ := (K.translatedDataOfExtreme ha R).construct_attained_translated_contact
  refine ⟨R,L,t,?_⟩
  simpa only [translatedDataOfExtreme_ray_val,R.start] using ht

end RepulsiveCoulomb.PointGeometricCutState
