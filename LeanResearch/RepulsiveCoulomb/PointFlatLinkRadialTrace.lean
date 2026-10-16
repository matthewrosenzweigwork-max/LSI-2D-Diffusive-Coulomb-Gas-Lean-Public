module

public import LeanResearch.RepulsiveCoulomb.PointFlatLinkConeDisk
public import LeanResearch.RepulsiveCoulomb.FlatLinkSectorDisk

@[expose] public section

/-! Isolated, uncompiled author draft. Radiality and the actual positive-radius
trace are derived from the input isometry. No link model is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

section
variable {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)

include ha hd

theorem continuous_pointFlatLinkDiskMap : Continuous f := by
  have hi : @Isometry (flatLinkSectorDisk β L) ℂ
      (inferInstance : PseudoEMetricSpace (flatLinkSectorDisk β L))
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace f := by
    apply @Isometry.of_dist_eq (flatLinkSectorDisk β L) ℂ _
      (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
    exact hd
  have hc := @Isometry.continuous (flatLinkSectorDisk β L) ℂ
    (inferInstance : PseudoEMetricSpace (flatLinkSectorDisk β L))
    (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace f hi
  change @Continuous (flatLinkSectorDisk β L) ℂ inferInstance
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace f at hc
  rwa [pointSmoothConformalMetricSpace_topology ha y] at hc

omit ha

theorem pointFlatLinkDiskMap_dist_apex (x : flatLinkSectorDisk β L) :
    (pointSmoothConformalEDist a y (f x) (f (flatLinkSectorDiskApex hβ.le hL.le))).toReal =
      ‖x.1‖ := by
  rw [hd]
  change dist x.1 (0 : ℂ) = ‖x.1‖
  exact dist_zero_right _

/-- Every source radial segment is sent to the exact target radial segment in
one common full cone chart. No choice of geodesic continuation is involved. -/
theorem pointFlatLinkDiskMap_radial
    (C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex hβ.le hL.le)))
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (s t : unitInterval) :
    C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ * s.1)
      ⟨mul_nonneg hρ.le s.2.1, (mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t)) =
      s.1 • C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le, hρL⟩ t)) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let q (u : unitInterval) := flatLinkSectorDiskPoint hβ.le hβπ (ρ * u.1)
    ⟨mul_nonneg hρ.le u.2.1, (mul_le_of_le_one_right hρ.le u.2.2).trans hρL⟩ t
  let w := flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le, hρL⟩ t
  have hq0 : q ⟨0, by norm_num⟩ = flatLinkSectorDiskApex hβ.le hL.le := by
    apply Subtype.ext
    change sectorPolar (ρ * 0) (β * t.1) = 0
    rw [mul_zero, sectorPolar_zero]
  have hq1 : q ⟨1, by norm_num⟩ = w := by
    apply Subtype.ext
    change sectorPolar (ρ * 1) (β * t.1) = sectorPolar ρ (β * t.1)
    rw [mul_one]
  have hbound (u : unitInterval) : (pointSmoothConformalEDist a y (f (q u)) p).toReal ≤ C.radius := by
    rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    change ‖sectorPolar (ρ * u.1) (β * t.1)‖ ≤ C.radius
    rw [sectorPolar_norm (mul_nonneg hρ.le u.2.1)]
    exact (mul_le_of_le_one_right hρ.le u.2.2).trans hρC
  have hwbound : (pointSmoothConformalEDist a y (f w) p).toReal ≤ C.radius := by
    simpa only [hq1] using hbound ⟨1, by norm_num⟩
  have hwnorm : ‖C.chart (f w)‖ = ρ := by
    rw [C.norm_chart hwbound, pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    exact sectorPolar_norm hρ.le _
  apply classicalCone_geodesic_from_apex_nonneg
    (α := coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
    (fun u ↦ C.chart (f (q u))) (C.chart (f w))
    (by rw [hq0]; exact C.center) (by rw [hq1])
  intro u v
  change pointClassicalConeDist a y p (C.chart (f (q u))) (C.chart (f (q v))) = _
  rw [← C.metric (f (q u)) (hbound u) (f (q v)) (hbound v), hd, hwnorm]
  change dist (sectorPolar (ρ * u.1) (β * t.1)) (sectorPolar (ρ * v.1) (β * t.1)) =
    |v.1 - u.1| * ρ
  rw [dist_eq_norm, sectorPolar_same_ray_dist, ← mul_sub, abs_mul, abs_of_pos hρ, abs_sub_comm, mul_comm]

end
end RepulsiveCoulomb
