import LeanResearch.RepulsiveCoulomb.PointConstructedIncidentSurgeryChart
import LeanResearch.RepulsiveCoulomb.PointNoIncidentSurgeryChart
import LeanResearch.RepulsiveCoulomb.PointSectorInteriorOpenChart
import LeanResearch.RepulsiveCoulomb.PointOriginalPlaneFiniteAllocation

/-! SOURCE-ONLY, UNCOMPILED. Exhaustive original-plane local surgery charts.
The actual sector-interior, incident-boundary and no-incident cases are all
constructed. This supplies open local charts, not yet rigid overlap proofs
or a complete surgery metric. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ} {c : ℝ}

theorem pointActualSectorInteriorOpenChart_apply
    (ha : ∀ j, 0 ≤ a j) (S : PointActualAllocatedSector a y)
    (hc : 0 < c) (hc1 : c ≤ 1) (hS : IsOpen S.openImage)
    (z : ℂ) (hz : z ∈ S.openImage) :
    pointActualSectorInteriorOpenChart ha S hc hc1 hS z =
      (pointActualSectorContractionChart ha S hc hc1
        ⟨z, S.openImage_subset_range hz⟩ : ℂ) := by
  classical
  change (if hx : z ∈ S.openImage then
    (pointActualSectorInteriorHomeomorph ha S hc hc1 ⟨z, hx⟩).1 else 0) = _
  rw [dif_pos hz]
  rfl

theorem pointActualSectorInteriorOpenChart_dist_bounds
    (ha : ∀ j, 0 ≤ a j) (S : PointActualAllocatedSector a y)
    (hc : 0 < c) (hc1 : c ≤ 1) (hS : IsOpen S.openImage)
    (z w : ℂ) (hz : z ∈ S.openImage) (hw : w ∈ S.openImage) :
    c * (pointSmoothConformalEDist a y z w).toReal ≤
      dist (pointActualSectorInteriorOpenChart ha S hc hc1 hS z)
        (pointActualSectorInteriorOpenChart ha S hc hc1 hS w) ∧
    dist (pointActualSectorInteriorOpenChart ha S hc hc1 hS z)
      (pointActualSectorInteriorOpenChart ha S hc hc1 hS w) ≤
        (pointSmoothConformalEDist a y z w).toReal := by
  rw [pointActualSectorInteriorOpenChart_apply ha S hc hc1 hS z hz,
    pointActualSectorInteriorOpenChart_apply ha S hc hc1 hS w hw]
  exact pointActualSectorContractionChart_dist_bounds ha S hc hc1
    ⟨z, S.openImage_subset_range hz⟩ ⟨w, S.openImage_subset_range hw⟩

/-- A choice of actual constructed local model, preserving its provenance. -/
inductive PointFiniteSurgeryLocalModel
    (ha : ∀ j, 0 ≤ a j) (L : List (PointActualAllocatedSector a y))
    (p : ℂ) (c : ℝ) (hc : 0 < c) (hc1 : c ≤ 1) where
  | sectorInterior (i : Fin L.length) (hopen : IsOpen (L.get i).openImage)
      (mem : p ∈ (L.get i).openImage)
  | unchanged (data : PointNoIncidentSurgeryChart L p)
  | incident (data : PointConstructedIncidentSurgeryChart ha L p c hc hc1)

namespace PointFiniteSurgeryLocalModel
variable {ha : ∀ j, 0 ≤ a j} {L : List (PointActualAllocatedSector a y)}
    {hc : 0 < c} {hc1 : c ≤ 1}

def chart (D : PointFiniteSurgeryLocalModel ha L p c hc hc1) : OpenPartialHomeomorph ℂ ℂ :=
  match D with
  | .sectorInterior i hopen _ => pointActualSectorInteriorOpenChart ha (L.get i) hc hc1 hopen
  | .unchanged data => data.chart
  | .incident data => data.chart

theorem center_mem (D : PointFiniteSurgeryLocalModel ha L p c hc hc1) : p ∈ D.chart.source := by
  cases D with
  | sectorInterior i hopen hp => exact hp
  | unchanged data => exact data.center_mem
  | incident data => exact data.center_mem

end PointFiniteSurgeryLocalModel

/-- Every point of the original plane has an actual surgery chart. Incident
boundary charts are the derived finite paste; no-incident charts use budget
flatness; selected interiors use their actual angular contraction. -/
theorem exists_pointFiniteSurgeryLocalModel
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (L : List (PointActualAllocatedSector a y)) (p : ℂ)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hdis : L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage))
    (hregular : ∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
      z.1 ∈ interior (closedEuclideanSector S.beta) → coalescedPointExponent a y (S.map z) = 0)
    (hbalance : (1-c) * pointActualAllocatedBudget L p = Real.pi * coalescedPointExponent a y p) :
    Nonempty (PointFiniteSurgeryLocalModel ha L p c hc hc1) := by
  classical
  by_cases hopen : ∃ i : Fin L.length, p ∈ (L.get i).openImage
  · obtain ⟨i, hi⟩ := hopen
    exact ⟨.sectorInterior i (pointFlatEmbedding_isOpen_openImage ha y
      (L.get i).map (L.get i).metric (hregular _ (List.get_mem L i))) hi⟩
  have hseam : ∀ i : Fin L.length, p ∉ (L.get i).openImage := fun i hi ↦ hopen ⟨i, hi⟩
  by_cases hinc : ∃ i : Fin L.length, p ∈ range (L.get i).map
  · obtain ⟨i, hi⟩ := hinc
    obtain ⟨D⟩ := exists_pointConstructedIncidentSurgeryChart ha y L p hc hc1
      hdis hregular hbalance hseam ⟨i, hi⟩
    exact ⟨.incident D⟩
  · obtain ⟨D⟩ := exists_pointNoIncidentSurgeryChart ha y L p c hbalance
      (fun i hi ↦ hinc ⟨i, hi⟩)
    exact ⟨.unchanged D⟩

/-- Original-input chart family, including zero mass. Actual allocation and
all three geometric point cases are outputs. Rigid overlap remains the next
separate construction and is deliberately not asserted by this endpoint. -/
theorem point_original_plane_finite_surgery_local_charts
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    ∃ c : ℝ, ∃ L : List (PointActualAllocatedSector a y),
      c = 1 / (1 + pointExteriorHalfMass a) ∧
      ∃ hc : 0 < c, ∃ hc1 : c ≤ 1,
      L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage) ∧
      (∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
        z.1 ∈ interior (closedEuclideanSector S.beta) → coalescedPointExponent a y (S.map z) = 0) ∧
      (∀ p, (1-c) * pointActualAllocatedBudget L p = Real.pi * coalescedPointExponent a y p) ∧
      ∃ model : ∀ p : ℂ, PointFiniteSurgeryLocalModel ha L p c hc hc1,
        ∀ p, p ∈ (model p).chart.source := by
  classical
  obtain ⟨c, L, hcdef, hc, hc1, hdis, hregular, hbalance, _⟩ :=
    point_original_plane_finite_actual_allocation ha y
  let model := fun p : ℂ ↦ Classical.choice
    (exists_pointFiniteSurgeryLocalModel ha y L p hc hc1 hdis hregular (hbalance p))
  exact ⟨c, L, hcdef, hc, hc1, hdis, hregular, hbalance, model, fun p ↦ (model p).center_mem⟩

end RepulsiveCoulomb
