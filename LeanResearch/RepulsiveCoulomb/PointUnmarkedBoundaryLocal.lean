import LeanResearch.RepulsiveCoulomb.PointRetainedFrontierEndpoint
import LeanResearch.RepulsiveCoulomb.MetricFlatHalfDiskChart
import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicAmbientConvexity
import Mathlib.Analysis.Complex.ReImTopology

/-! SOURCE-ONLY, UNCOMPILED. A physically flat retained boundary has literal
local minimizing diameter segments. Positive ambient cone exponents are allowed.
No complete line, boundary arclength, or continuation certificate is an input. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb
namespace PointRetainedConeNeighborhood
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}

/-- Physical width pi implies coordinate width at most pi, without asserting
that the ambient exponent vanishes. -/
theorem boundaryFlat_coordinate_width_le_pi
    (C : PointRetainedConeNeighborhood a y P p)
    (hw : C.flatPhysicalWidth = Real.pi) : C.hi - C.lo ≤ Real.pi := by
  have hA : 1 ≤ coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  unfold flatPhysicalWidth at hw
  nlinarith [C.width_pos]

/-- A raw endpoint cannot be an interior point: its whole local retained set
lies on one side of an actual supporting line in the ambient chart. -/
theorem boundaryFlat_endpoint_not_interior
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (C : PointRetainedConeNeighborhood a y P p)
    (hw : C.flatPhysicalWidth = Real.pi) {z : ℂ}
    (hzR : (pointSmoothConformalEDist a y z p).toReal < C.radius)
    {r θ : ℝ} (he : C.chart z = pointRadialSectorPoint r θ)
    (hθ : θ = C.lo ∨ θ = C.hi) : z ∉ interior P := by
  intro hzI
  let B : Set ℂ := {w | (pointSmoothConformalEDist a y w p).toReal < C.radius}
  have hB : IsOpen B := by
    have h := @Metric.isOpen_ball ℂ
      (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace p C.radius
    change @IsOpen ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace B at h
    rwa [pointSmoothConformalMetricSpace_topology ha y] at h
  let U : Set ℂ := interior P ∩ B
  have hU : IsOpen U := isOpen_interior.inter hB
  have hUsrc : U ⊆ C.chart.source := by
    intro w hw
    have hwr : (pointSmoothConformalEDist a y w p).toReal < C.radius := hw.2
    exact C.source hwr.le
  let e := Homeomorph.mulLeft₀ (conePhase (-θ)) (Complex.exp_ne_zero _)
  let V := e '' (C.chart '' U)
  have hV : IsOpen V := e.isOpenMap _ (C.chart.isOpen_image_of_subset_source hU hUsrc)
  have hzV : e (C.chart z) ∈ V := ⟨C.chart z, ⟨z, ⟨hzI, hzR⟩, rfl⟩, rfl⟩
  have hzero : (e (C.chart z)).im = 0 := by
    change (conePhase (-θ) * C.chart z).im = 0
    rw [he, sectorReturn_rotate_radial_point, sub_self,
      ← sectorPolar_eq_pointRadialSectorPoint, sectorPolar_im, Real.sin_zero, mul_zero]
  have hwidth := C.boundaryFlat_coordinate_width_le_pi hw
  rcases hθ with hθ | hθ
  · have hsub : V ⊆ {w : ℂ | 0 ≤ w.im} := by
      rintro w ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      obtain ⟨s, hs, φ, hφ, hφe⟩ := (C.retained u hu.2.le).mp (interior_subset hu.1)
      change 0 ≤ (conePhase (-θ) * C.chart u).im
      rw [hφe, sectorReturn_rotate_radial_point, hθ,
        ← sectorPolar_eq_pointRadialSectorPoint, sectorPolar_im]
      exact mul_nonneg hs.1 (Real.sin_nonneg_of_mem_Icc
        ⟨sub_nonneg.mpr hφ.1, by linarith [hφ.2]⟩)
    have hmem := interior_mono hsub (hV.interior_eq.symm ▸ hzV)
    rw [Complex.interior_setOfPred_le_im] at hmem
    exact (lt_irrefl (0 : ℝ)) (by simpa only [mem_setOf_eq, hzero] using hmem)
  · have hsub : V ⊆ {w : ℂ | w.im ≤ 0} := by
      rintro w ⟨v, ⟨u, hu, rfl⟩, rfl⟩
      obtain ⟨s, hs, φ, hφ, hφe⟩ := (C.retained u hu.2.le).mp (interior_subset hu.1)
      change (conePhase (-θ) * C.chart u).im ≤ 0
      rw [hφe, sectorReturn_rotate_radial_point, hθ,
        ← sectorPolar_eq_pointRadialSectorPoint, sectorPolar_im]
      have hsin : 0 ≤ Real.sin (C.hi - φ) := Real.sin_nonneg_of_mem_Icc
        ⟨sub_nonneg.mpr hφ.2, by linarith [hφ.1]⟩
      have hn : Real.sin (φ - C.hi) ≤ 0 := by
        rw [show φ - C.hi = -(C.hi - φ) by ring, Real.sin_neg]
        exact neg_nonpos.mpr hsin
      exact mul_nonpos_of_nonneg_of_nonpos hs.1 hn
    have hmem := interior_mono hsub (hV.interior_eq.symm ▸ hzV)
    rw [Complex.interior_setOfPred_im_le] at hmem
    exact (lt_irrefl (0 : ℝ)) (by simpa only [mem_setOf_eq, hzero] using hmem)

/-- Exact angular formula for the constructed flat inverse, retaining the full
raw interval. -/
theorem boundaryFlat_inverse_coordinate
    (C : PointRetainedConeNeighborhood a y P p)
    {z : ℂ} (hz : ‖z‖ ≤ C.radius) :
    C.chart (C.flatInverse z) = pointRadialSectorPoint ‖z‖
      (C.lo + (coalescedPointExponent a y p / 2 + 1)⁻¹ * Complex.arg z) := by
  calc
    C.chart (C.flatInverse z) = C.flatInverseCoordinate z :=
      (C.inverse_metricBall ((C.flatInverseCoordinate_norm z).trans_le hz)).2
    _ = _ := by
      unfold flatInverseCoordinate sectorAngularMap
      rw [conePhase_mul_sectorPolar, sectorPolar_eq_pointRadialSectorPoint]

/-- The genuine retained halfdisk meets the old frontier exactly in its real
diameter, including the cone apex. -/
theorem boundaryFlat_inverse_frontier_iff
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (C : PointRetainedConeNeighborhood a y P p)
    (hp : p ∈ frontier P) (hw : C.flatPhysicalWidth = Real.pi)
    {z : ℂ} (hzR : ‖z‖ < C.radius) (hzU : 0 ≤ z.im) :
    C.flatInverse z ∈ frontier P ↔ z.im = 0 := by
  have hz : z ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius := by
    rw [hw, retainedFlatSectorDisk_pi]
    exact ⟨hzU, hzR.le⟩
  have hdist : (pointSmoothConformalEDist a y (C.flatInverse z) p).toReal < C.radius := by
    rw [C.flatInverse_center_distance hw.le hz]
    exact hzR
  let A := coalescedPointExponent a y p / 2 + 1
  have hA : 0 < A := by dsimp [A]; linarith [coalescedPointExponent_nonneg a y p]
  have htop : C.lo + A⁻¹ * Real.pi = C.hi := by
    rw [← hw]
    change C.lo + A⁻¹ * (A * (C.hi - C.lo)) = C.hi
    rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
    ring
  have harg : Complex.arg z ∈ Icc (0 : ℝ) Real.pi :=
    ⟨Complex.arg_nonneg_iff.mpr hzU, Complex.arg_le_pi z⟩
  have hθ : C.lo + A⁻¹ * Complex.arg z ∈ Icc C.lo C.hi := by
    constructor
    · exact le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hA.le) harg.1)
    · rw [← htop]
      linarith [mul_le_mul_of_nonneg_left harg.2 (inv_nonneg.mpr hA.le)]
  have hc := C.boundaryFlat_inverse_coordinate hzR.le
  by_cases hz0 : z = 0
  · subst z
    constructor
    · intro _
      rfl
    · intro _
      simpa only [C.flatInverse_zero] using hp
  have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  constructor
  · intro hfront
    rcases C.frontier_radial_coordinate_endpoint hfront hdist hn hθ hc with he | he
    · have ha0 : Complex.arg z = 0 := by
        have hprod : A⁻¹ * Complex.arg z = 0 := by linarith
        exact (mul_eq_zero.mp hprod).resolve_left (inv_ne_zero hA.ne')
      have hs := Complex.norm_mul_sin_arg z
      simpa only [ha0, Real.sin_zero, mul_zero] using hs.symm
    · have hapi : Complex.arg z = Real.pi := by
        have hprod : A⁻¹ * Complex.arg z = A⁻¹ * Real.pi := by linarith
        exact mul_left_cancel₀ (inv_ne_zero hA.ne') hprod
      have hs := Complex.norm_mul_sin_arg z
      simpa only [hapi, Real.sin_pi, mul_zero] using hs.symm
  · intro hreal
    have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hreal]
    have hend : C.lo + A⁻¹ * Complex.arg z = C.lo ∨
        C.lo + A⁻¹ * Complex.arg z = C.hi := by
      by_cases hre : 0 ≤ z.re
      · left
        rw [hzreal, Complex.arg_ofReal_of_nonneg hre, mul_zero, add_zero]
      · right
        rw [hzreal, Complex.arg_ofReal_of_neg (lt_of_not_ge hre)]
        exact htop
    exact ⟨subset_closure (C.flatInverse_mem_and_radius hz).1,
      C.boundaryFlat_endpoint_not_interior ha y hw hdist hc hend⟩

/-- Construct the actual minimizing chord between ANY two sufficiently near
old-boundary points. Its entire image lies in the actual old frontier. -/
theorem boundaryFlat_exists_chord
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hP : IsClosed P)
    (C : PointRetainedConeNeighborhood a y P p)
    (hp : p ∈ frontier P) (hw : C.flatPhysicalWidth = Real.pi)
    {x z : ℂ} (hx : x ∈ frontier P) (hz : z ∈ frontier P)
    (hxR : (pointSmoothConformalEDist a y x p).toReal < C.radius)
    (hzR : (pointSmoothConformalEDist a y z p).toReal < C.radius) :
    ∃ γ : unitInterval → ℂ, γ 0 = x ∧ γ 1 = z ∧ Continuous γ ∧
      (∀ t, γ t ∈ frontier P) ∧ ∀ s t,
        (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
          |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal := by
  obtain ⟨X, hX, hXi⟩ := C.flatInverse_surjOn hw.le
    ⟨hP.frontier_subset hx, hxR.le⟩
  obtain ⟨Z, hZ, hZi⟩ := C.flatInverse_surjOn hw.le
    ⟨hP.frontier_subset hz, hzR.le⟩
  have hXnorm : ‖X‖ < C.radius := by
    rw [← C.flatInverse_center_distance hw.le hX, hXi]
    exact hxR
  have hZnorm : ‖Z‖ < C.radius := by
    rw [← C.flatInverse_center_distance hw.le hZ, hZi]
    exact hzR
  have hXupper : 0 ≤ X.im := by
    have h := hX
    rw [hw, retainedFlatSectorDisk_pi] at h
    exact h.1
  have hZupper : 0 ≤ Z.im := by
    have h := hZ
    rw [hw, retainedFlatSectorDisk_pi] at h
    exact h.1
  have hXreal : X.im = 0 := (C.boundaryFlat_inverse_frontier_iff ha y hp hw hXnorm hXupper).mp (hXi.symm ▸ hx)
  have hZreal : Z.im = 0 := (C.boundaryFlat_inverse_frontier_iff ha y hp hw hZnorm hZupper).mp (hZi.symm ▸ hz)
  let σ : unitInterval → ℂ := fun t ↦ AffineMap.lineMap X Z t.1
  have hσR (t : unitInterval) : ‖σ t‖ < C.radius := by
    have h := (convex_ball (0 : ℂ) C.radius).lineMap_mem
      (show X ∈ ball 0 C.radius by simpa only [mem_ball, dist_zero_right] using hXnorm)
      (show Z ∈ ball 0 C.radius by simpa only [mem_ball, dist_zero_right] using hZnorm) t.2
    simpa only [mem_ball, dist_zero_right] using h
  have hσreal (t : unitInterval) : (σ t).im = 0 := by
    simp [σ, AffineMap.lineMap_apply_module, Complex.smul_im, hXreal, hZreal]
  have hσ (t : unitInterval) : σ t ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius := by
    rw [hw, retainedFlatSectorDisk_pi]
    exact ⟨(hσreal t).ge, (hσR t).le⟩
  let γ : unitInterval → ℂ := fun t ↦ C.flatInverse (σ t)
  have h0 : γ 0 = x := by simp [γ, σ, hXi]
  have h1 : γ 1 = z := by simp [γ, σ, hZi]
  have hd (s t : unitInterval) :
      (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal := by
    rw [C.flatInverse_dist hw.le (hσ s) (hσ t)]
    change dist (AffineMap.lineMap X Z s.1) (AffineMap.lineMap X Z t.1) = _
    rw [dist_lineMap_lineMap, ← hXi, ← hZi, C.flatInverse_dist hw.le hX hZ,
      Real.dist_eq, abs_sub_comm]
  have hLip : @LipschitzWith unitInterval ℂ _
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace
      ⟨(pointSmoothConformalEDist a y x z).toReal, ENNReal.toReal_nonneg⟩ γ := by
    apply @LipschitzWith.of_dist_le_mul unitInterval ℂ _
      (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
    intro s t
    change (pointSmoothConformalEDist a y (γ s) (γ t)).toReal ≤ _
    rw [hd]
    change |t.1 - s.1| * _ ≤ _ * dist s.1 t.1
    rw [Real.dist_eq, abs_sub_comm, mul_comm]
    exact le_rfl
  have hc := @LipschitzWith.continuous unitInterval ℂ _
    (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace _ γ hLip
  rw [pointSmoothConformalMetricSpace_topology ha y] at hc
  exact ⟨γ, h0, h1, hc, fun t ↦
    (C.boundaryFlat_inverse_frontier_iff ha y hp hw (hσR t) (hσreal t).ge).mpr (hσreal t), hd⟩

end PointRetainedConeNeighborhood
end RepulsiveCoulomb
