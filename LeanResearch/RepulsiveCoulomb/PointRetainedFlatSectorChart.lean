import LeanResearch.RepulsiveCoulomb.ClassicalConeClosedHalfSector
import LeanResearch.RepulsiveCoulomb.PointRetainedConeNeighborhood

/-! Construct actual inverse flat charts from genuine retained interval links.
A boundary interval of physical width pi is flat even if the ambient cone is
singular. The target is the literal retained subset P, with the old metric.
This is a local chart construction, not a positive-width strip certificate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Closed Euclidean sector disk used by the concrete inverse chart. -/
def retainedFlatSectorDisk (β R : ℝ) : Set ℂ :=
  closedEuclideanSector β ∩ {z | ‖z‖ ≤ R}

/-- For an intrinsically regular boundary point this source is a literal
closed upper halfdisk, not an abstract interval-cone metric space. -/
theorem retainedFlatSectorDisk_pi (R : ℝ) :
    retainedFlatSectorDisk Real.pi R = {z : ℂ | 0 ≤ z.im ∧ ‖z‖ ≤ R} := by
  ext z
  simp only [retainedFlatSectorDisk, closedEuclideanSector, mem_inter_iff, mem_setOf_eq,
    Complex.arg_nonneg_iff, Complex.arg_le_pi, and_true]

namespace PointRetainedConeNeighborhood
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}

/-- The physical retained angle, rather than the coordinate angular width. -/
def flatPhysicalWidth (C : PointRetainedConeNeighborhood a y P p) : ℝ :=
  (coalescedPointExponent a y p / 2 + 1) * (C.hi - C.lo)

theorem flatPhysicalWidth_pos (C : PointRetainedConeNeighborhood a y P p) :
    0 < C.flatPhysicalWidth := by
  apply mul_pos _ (sub_pos.mpr C.width_pos)
  linarith [coalescedPointExponent_nonneg a y p]

/-- The actual coordinate formula; the ambient cone opening is divided out. -/
def flatInverseCoordinate (C : PointRetainedConeNeighborhood a y P p) (z : ℂ) : ℂ :=
  conePhase C.lo * sectorAngularMap (coalescedPointExponent a y p / 2 + 1)⁻¹ z

/-- The actual inverse chart map in the original point-conformal plane. -/
def flatInverse (C : PointRetainedConeNeighborhood a y P p) (z : ℂ) : ℂ :=
  C.chart.symm (C.flatInverseCoordinate z)

theorem flatInverseCoordinate_norm (C : PointRetainedConeNeighborhood a y P p)
    (z : ℂ) : ‖C.flatInverseCoordinate z‖ = ‖z‖ := by
  rw [flatInverseCoordinate, norm_mul, conePhase_norm, one_mul, sectorAngularMap_norm]

/-- Inverse chart targets are actually in the original metric disk. -/
theorem inverse_metricBall (C : PointRetainedConeNeighborhood a y P p)
    {w : ℂ} (hw : ‖w‖ ≤ C.radius) :
    (pointSmoothConformalEDist a y (C.chart.symm w) p).toReal ≤ C.radius ∧
      C.chart (C.chart.symm w) = w := by
  obtain ⟨x, hx, hxw⟩ := C.onto.surjOn hw
  have hinv : C.chart.symm w = x := by rw [← hxw, C.chart.left_inv (C.source hx)]
  rw [hinv]
  exact ⟨hx, hxw⟩

theorem flatInverseCoordinate_mem (C : PointRetainedConeNeighborhood a y P p)
    {z : ℂ} (hz : z ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius) :
    C.flatInverseCoordinate z ∈ pointClosedRadialInterval C.radius C.lo C.hi := by
  have hα : 0 ≤ coalescedPointExponent a y p / 2 :=
    div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  obtain ⟨r, hr, θ, hθ, he⟩ :=
    rotated_sectorAngularMap_radial_representative_le_pi hα C.lo hz.1 hz.2
  have hp : coalescedPointExponent a y p / 2 + 1 ≠ 0 := by linarith
  have htop : C.lo + (coalescedPointExponent a y p / 2 + 1)⁻¹ * C.flatPhysicalWidth =
      C.hi := by
    unfold flatPhysicalWidth
    rw [← mul_assoc, inv_mul_cancel₀ hp, one_mul]
    ring
  refine ⟨r, hr, θ, ?_, he⟩
  rwa [htop] at hθ

theorem flatInverse_mem_and_radius (C : PointRetainedConeNeighborhood a y P p)
    {z : ℂ} (hz : z ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius) :
    C.flatInverse z ∈ P ∧
      (pointSmoothConformalEDist a y (C.flatInverse z) p).toReal ≤ C.radius := by
  obtain ⟨hR, hright⟩ := C.inverse_metricBall
    ((C.flatInverseCoordinate_norm z).trans_le hz.2)
  refine ⟨(C.retained _ hR).mpr ?_, hR⟩
  rw [hright]
  exact C.flatInverseCoordinate_mem hz

/-- All pair distances, including radial edges and center, are proved from
actual cone metric identities. Injectivity is not an input. -/
theorem flatInverse_dist (C : PointRetainedConeNeighborhood a y P p)
    (hwidth : C.flatPhysicalWidth ≤ Real.pi)
    {x z : ℂ} (hx : x ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius)
    (hz : z ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius) :
    (pointSmoothConformalEDist a y (C.flatInverse x) (C.flatInverse z)).toReal = dist x z := by
  obtain ⟨hxR, hrightx⟩ := C.inverse_metricBall
    ((C.flatInverseCoordinate_norm x).trans_le hx.2)
  obtain ⟨hzR, hrightz⟩ := C.inverse_metricBall
    ((C.flatInverseCoordinate_norm z).trans_le hz.2)
  change (pointSmoothConformalEDist a y (C.chart.symm (C.flatInverseCoordinate x))
    (C.chart.symm (C.flatInverseCoordinate z))).toReal = dist x z
  rw [C.metric _ hxR _ hzR, hrightx, hrightz]
  exact (rotated_sectorAngularMap_classicalCone_dist_le_pi
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) hwidth C.lo hx.1 hz.1).trans
    (dist_eq_norm x z).symm

/-- The constructed local map has values in the literal old region. -/
def flatSectorChart (C : PointRetainedConeNeighborhood a y P p) :
    retainedFlatSectorDisk C.flatPhysicalWidth C.radius → P :=
  fun z ↦ ⟨C.flatInverse z.1, (C.flatInverse_mem_and_radius z.2).1⟩

theorem flatSectorChart_isometry (ha : ∀ j, 0 ≤ a j)
    (C : PointRetainedConeNeighborhood a y P p)
    (hwidth : C.flatPhysicalWidth ≤ Real.pi) :
    @Isometry (retainedFlatSectorDisk C.flatPhysicalWidth C.radius) P
      (inferInstance : PseudoEMetricSpace (retainedFlatSectorDisk C.flatPhysicalWidth C.radius))
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace C.flatSectorChart := by
  apply @Isometry.of_dist_eq _ P _ (pointRegionMetricSpace ha y P).toPseudoMetricSpace
  intro x z
  exact C.flatInverse_dist hwidth x.2 z.2

@[simp] theorem flatInverse_zero (C : PointRetainedConeNeighborhood a y P p) :
    C.flatInverse 0 = p := by
  have hpR : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  unfold flatInverse flatInverseCoordinate
  rw [sectorAngularMap_zero, mul_zero, ← C.center, C.chart.left_inv (C.source hpR)]

/-- Each actual radial germ has its prescribed physical arclength and direction. -/
theorem flatInverse_polar (C : PointRetainedConeNeighborhood a y P p)
    {r θ : ℝ} (hr : 0 ≤ r) (hθ : θ ∈ Ioc (-Real.pi) Real.pi) :
    C.flatInverse (sectorPolar r θ) = C.chart.symm
      (pointRadialSectorPoint r (C.lo + (coalescedPointExponent a y p / 2 + 1)⁻¹ * θ)) := by
  unfold flatInverse flatInverseCoordinate
  rw [sectorAngularMap_polar hr hθ, conePhase_mul_sectorPolar,
    sectorPolar_eq_pointRadialSectorPoint]

/-- The inverse map covers the entire literal retained metric patch. Thus it
is a genuine chart, not just a map of a smaller sector into P. -/
theorem flatInverse_surjOn (C : PointRetainedConeNeighborhood a y P p)
    (hwidth : C.flatPhysicalWidth ≤ Real.pi) :
    SurjOn C.flatInverse (retainedFlatSectorDisk C.flatPhysicalWidth C.radius)
      (P ∩ {w | (pointSmoothConformalEDist a y w p).toReal ≤ C.radius}) := by
  intro w hw
  obtain ⟨r, hr, θ, hθ, hwθ⟩ := (C.retained w hw.2).mp hw.1
  let A := coalescedPointExponent a y p / 2 + 1
  have hA : 0 < A := by dsimp [A]; linarith [coalescedPointExponent_nonneg a y p]
  let φ := A * (θ - C.lo)
  have hφ0 : 0 ≤ φ := mul_nonneg hA.le (sub_nonneg.mpr hθ.1)
  have hφβ : φ ≤ C.flatPhysicalWidth := by
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hθ.2 C.lo) hA.le
  have hφwin : φ ∈ Ioc (-Real.pi) Real.pi :=
    ⟨(neg_neg_of_pos Real.pi_pos).trans_le hφ0, hφβ.trans hwidth⟩
  have hsector : sectorPolar r φ ∈ closedEuclideanSector C.flatPhysicalWidth := by
    by_cases hr0 : r = 0
    · simp [hr0, sectorPolar_zero, closedEuclideanSector, C.flatPhysicalWidth_pos.le]
    · change 0 ≤ Complex.arg (sectorPolar r φ) ∧
        Complex.arg (sectorPolar r φ) ≤ C.flatPhysicalWidth
      rw [sectorPolar_arg (lt_of_le_of_ne hr.1 (Ne.symm hr0)) hφwin]
      exact ⟨hφ0, hφβ⟩
  refine ⟨sectorPolar r φ, ⟨hsector, ?_⟩, ?_⟩
  · simpa only [mem_setOf_eq, sectorPolar_norm hr.1] using hr.2
  · have hangle : C.lo + A⁻¹ * φ = θ := by
      dsimp [φ]
      rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
      ring
    rw [C.flatInverse_polar hr.1 hφwin]
    change C.chart.symm (pointRadialSectorPoint r (C.lo + A⁻¹ * φ)) = w
    rw [hangle, ← hwθ, C.chart.left_inv (C.source hw.2)]

/-- Literal image equality for both corner disks and regular halfdisks. -/
theorem flatInverse_image (C : PointRetainedConeNeighborhood a y P p)
    (hwidth : C.flatPhysicalWidth ≤ Real.pi) :
    C.flatInverse '' retainedFlatSectorDisk C.flatPhysicalWidth C.radius =
      P ∩ {w | (pointSmoothConformalEDist a y w p).toReal ≤ C.radius} := by
  apply Subset.antisymm
  · rintro w ⟨z, hz, rfl⟩
    exact C.flatInverse_mem_and_radius hz
  · exact C.flatInverse_surjOn hwidth

end PointRetainedConeNeighborhood
end RepulsiveCoulomb
