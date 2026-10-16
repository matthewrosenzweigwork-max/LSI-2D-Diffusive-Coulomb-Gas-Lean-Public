import LeanResearch.RepulsiveCoulomb.PointNoIncidentBudgetFlatness
import LeanResearch.RepulsiveCoulomb.PointFiniteSurgeryIncidentData
import LeanResearch.RepulsiveCoulomb.PointConeBallClosedPieceCover

/-! SOURCE-ONLY, UNCOMPILED. Genuine unchanged open disk charts at points
incident to no allocated sector. Budget exhaustion proves zero curvature;
finite closed-range clearance ensures the whole chart misses all sectors. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ}

/-- Restrict the genuine cone chart to the exact old open metric disk and
exact target Euclidean disk, using its constructed closed-disk surjectivity. -/
def pointConeOpenDiskChart (C : PointFlatLinkConeDisk a y p)
    {R : ℝ} (hRC : R ≤ C.radius) : OpenPartialHomeomorph ℂ ℂ := by
  have htarget : ball (0 : ℂ) R ⊆ C.chart.target := by
    intro z hz
    have hn : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
    obtain ⟨x, hx, he⟩ := C.onto.surjOn (hn.le.trans hRC)
    exact he ▸ C.chart.map_source (C.source hx)
  have hinverse : ∀ z ∈ ball (0 : ℂ) R, C.chart.symm z ∈ pointConeOpenBall C R := by
    intro z hz
    exact ⟨C.chart.map_target (htarget hz), by
      change C.chart (C.chart.symm z) ∈ ball 0 R
      rwa [C.chart.right_inv (htarget hz)]⟩
  exact {
    toFun := C.chart, invFun := C.chart.symm,
    source := pointConeOpenBall C R, target := ball 0 R,
    map_source' := fun _ hz ↦ hz.2,
    map_target' := fun _ hz ↦ hinverse _ hz,
    left_inv' := fun _ hz ↦ C.chart.left_inv hz.1,
    right_inv' := fun _ hz ↦ C.chart.right_inv (htarget hz),
    open_source := pointConeOpenBall_isOpen C R, open_target := isOpen_ball,
    continuousOn_toFun := C.chart.continuousOn.mono inter_subset_left,
    continuousOn_invFun := C.chart.symm.continuousOn.mono htarget
  }

structure PointNoIncidentSurgeryChart
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) where
  cone : PointFlatLinkConeDisk a y p
  radius : ℝ
  radius_pos : 0 < radius
  radius_cone : radius ≤ cone.radius
  flat : coalescedPointExponent a y p = 0
  clear : ∀ i : Fin L.length, ∀ z ∈ pointConeOpenBall cone radius, z ∉ range (L.get i).map

namespace PointNoIncidentSurgeryChart

def chart {L : List (PointActualAllocatedSector a y)}
    (D : PointNoIncidentSurgeryChart L p) : OpenPartialHomeomorph ℂ ℂ :=
  pointConeOpenDiskChart D.cone D.radius_cone

theorem center_mem {L : List (PointActualAllocatedSector a y)}
    (D : PointNoIncidentSurgeryChart L p) : p ∈ D.chart.source :=
  pointConeOpenBall_center D.cone D.radius_pos

theorem metric {L : List (PointActualAllocatedSector a y)}
    (D : PointNoIncidentSurgeryChart L p) (z w : ℂ)
    (hz : z ∈ D.chart.source) (hw : w ∈ D.chart.source) :
    dist (D.chart z) (D.chart w) = (pointSmoothConformalEDist a y z w).toReal := by
  have hzC := ((mem_pointConeOpenBall_iff D.cone D.radius_cone z).mp hz).le.trans D.radius_cone
  have hwC := ((mem_pointConeOpenBall_iff D.cone D.radius_cone w).mp hw).le.trans D.radius_cone
  change dist (D.cone.chart z) (D.cone.chart w) = _
  rw [D.cone.metric z hzC w hwC, pointClassicalConeDist_eq_euclidean_of_zero y D.flat]

end PointNoIncidentSurgeryChart

theorem exists_pointNoIncidentSurgeryChart
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (L : List (PointActualAllocatedSector a y)) (p : ℂ) (c : ℝ)
    (hbalance : (1-c) * pointActualAllocatedBudget L p = Real.pi * coalescedPointExponent a y p)
    (hno : ∀ i : Fin L.length, p ∉ range (L.get i).map) :
    Nonempty (PointNoIncidentSurgeryChart L p) := by
  classical
  obtain ⟨C⟩ := exists_pointFlatLinkConeDisk ha y p
  have hseam : ∀ i : Fin L.length, p ∉ (L.get i).openImage :=
    fun i hp ↦ hno i ((L.get i).openImage_subset_range hp)
  obtain ⟨R, hR, hRC, lo, hmodel⟩ :=
    exists_pointFiniteSector_common_incident_link ha y (fun i : Fin L.length ↦ L.get i) p hseam C
  have hno' : ∀ S ∈ L, p ∉ range S.map := by
    intro S hS
    obtain ⟨i, hi⟩ := List.mem_iff_get.mp hS
    exact hi ▸ hno i
  refine ⟨{
    cone := C, radius := R, radius_pos := hR, radius_cone := hRC,
    flat := pointExponent_eq_zero_of_exact_budget_no_incident L p c hbalance hno',
    clear := ?_
  }⟩
  intro i z hz hzi
  exact hno i ((hmodel i z ((mem_pointConeOpenBall_iff C hRC z).mp hz).le).mp hzi).1

end RepulsiveCoulomb
