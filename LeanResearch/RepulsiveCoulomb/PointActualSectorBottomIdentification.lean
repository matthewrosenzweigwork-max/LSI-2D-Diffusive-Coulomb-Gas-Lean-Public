import LeanResearch.RepulsiveCoulomb.PointActualClosedSectorConstruction
import Mathlib.Analysis.Complex.ReImTopology

/-! ISOLATED SOURCE-ONLY DRAFT. Identify the actual completed sector's bottom
with the given clean ray using derived intrinsic boundary flatness, and give
the literal ambient-open source interior clearance statement. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem closedEuclideanSector_interior_strict_arg {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    {z : ℂ} (hz : z ∈ interior (closedEuclideanSector β)) : Complex.arg z ∈ Ioo (0 : ℝ) β := by
  have hmem := interior_subset hz
  have hupper : closedEuclideanSector β ⊆ {z : ℂ | 0 ≤ z.im} :=
    fun z hz ↦ Complex.arg_nonneg_iff.mp hz.1
  have him : 0 < z.im := by
    have h := interior_mono hupper hz
    simpa only [Complex.interior_setOfPred_le_im, mem_setOf_eq] using h
  let e := Homeomorph.mulLeft₀ (conePhase (-β)) (Complex.exp_ne_zero _)
  have he (w : ℂ) : (e w).im = Real.cos β * w.im - Real.sin β * w.re := by
    change (conePhase (-β) * w).im = _
    rw [Complex.mul_im, conePhase_re, conePhase_im, Real.cos_neg, Real.sin_neg]
    ring
  have hsub : closedEuclideanSector β ⊆ e ⁻¹' {w : ℂ | w.im ≤ 0} := by
    intro w hw
    rw [closedEuclideanSector_eq_halfplanes hβ hβπ] at hw
    change (e w).im ≤ 0
    rw [he]
    exact hw.2
  have hside : Real.cos β * z.im - Real.sin β * z.re < 0 := by
    have h := interior_mono hsub hz
    rw [← e.preimage_interior, Complex.interior_setOfPred_im_le] at h
    exact (he z) ▸ h
  constructor
  · have hn : Complex.arg z ≠ 0 := by
      intro h0
      have h := Complex.norm_mul_sin_arg z
      rw [h0, Real.sin_zero, mul_zero] at h
      linarith
    exact lt_of_le_of_ne hmem.1 (Ne.symm hn)
  · have hn : Complex.arg z ≠ β := by
      intro heq
      rw [complex_support_side, heq, sub_self, Real.sin_zero, mul_zero] at hside
      exact lt_irrefl _ hside
    exact lt_of_le_of_ne hmem.2 hn

namespace PointActualSectorData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j} {P : Set ℂ}
    (D : PointActualSectorData a y ha P)

/-- This is an identification theorem for the already constructed closed map.
Its bottom ray is forced by actual clean-boundary flat continuation, including
clean points with positive ambient cone exponent. -/
theorem completed_map_bottom
    (F : closedEuclideanSector D.beta → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z)
    (hseed : ∀ z, ‖z.1‖ ≤ D.chart.radius → (F z).1 = D.chart.flatInverse z.1)
    (r : NNReal) (hr : (r : ℂ) ∈ closedEuclideanSector D.beta) :
    (F ⟨(r : ℂ), hr⟩).1 = D.ray r := by
  have h0 : (0 : ℂ) ∈ closedEuclideanSector D.beta := by
    simp only [closedEuclideanSector, mem_setOf_eq, Complex.arg_zero]
    exact ⟨le_rfl, D.beta_pos.le⟩
  have hcenter : (F ⟨0, h0⟩).1 = D.ray 0 := by
    rw [hseed ⟨0, h0⟩ (by simpa only [norm_zero] using D.chart.radius_pos.le), D.chart.flatInverse_zero]
  by_cases hr0 : r = 0
  · subst r
    exact hcenter
  let q : closedEuclideanSector D.beta := ⟨(r : ℂ), hr⟩
  have hq : q.1 ≠ 0 := Complex.ofReal_ne_zero.mpr (show (r : ℝ) ≠ 0 from fun h ↦ hr0 (Subtype.ext h))
  let hconv := closedEuclideanSector_convex D.beta_pos D.beta_pi
  let E := pointConvexRadialEdgeAt ha y hconv h0 F hd hcenter q hq
  have hEP := pointConvexRadialEdgeAt_mem ha y hconv h0 F hd hcenter q hq
  let G := pointRayComparisonEdge ha y D.ray D.ray_metric E
  have hGP : ∀ t, G.curve t ∈ P := fun _ ↦ D.ray_mem _
  have hrawE : D.chart.actualInitialRawAngle ha y D.admissible E rfl hEP = D.chart.lo := by
    have h := D.chart.actualRawAngle_of_capped_seed_stage_at ha y hconv h0 F hd hcenter
      D.admissible D.beta_width subset_rfl hseed q hq
    simpa only [E, q, Complex.arg_ofReal_of_nonneg
      (show (0 : ℝ) ≤ (r : ℝ) from r.2), mul_zero, add_zero] using h
  have hrawG := D.comparisonEdge_raw_lower E
  have hspeed : (pointSmoothConformalEDist a y E.start E.finish).toReal =
      (pointSmoothConformalEDist a y G.start G.finish).toReal :=
    (pointRayComparisonEdge_length ha y D.ray D.ray_metric E).symm
  have hflat : ∀ t : unitInterval, 0 < t.1 →
      ∃ C : PointRetainedConeNeighborhood a y P (G.curve t), C.flatPhysicalWidth ≤ Real.pi := by
    intro t ht
    let u : NNReal := ⟨pointActualEdgeLength E * t.1,
      mul_nonneg (pointActualEdgeLength_pos ha y E).le t.2.1⟩
    have hu : 0 < u := mul_pos (pointActualEdgeLength_pos ha y E) ht
    have hoff := pointMetricRay_positive_not_marked y D.ray D.ray_metric D.ray_clean u hu
    obtain ⟨C, hC⟩ := D.boundary_atom (D.ray u) (D.ray_frontier u)
    have hνC : D.nu (D.ray u) = Real.pi - C.flatPhysicalWidth := by
      unfold PointRetainedConeNeighborhood.flatPhysicalWidth
      nlinarith [hC]
    exact ⟨C, (pointSigned_clean_boundary_physical_width_pi C hoff hνC).le⟩
  have hoverlap := D.chart.actual_edges_overlap_of_initial_angle_eq ha y D.admissible
    E G rfl rfl hEP hGP hspeed (hrawE.trans hrawG.symm)
  have heq := pointActualEdges_eq_of_initial_overlap_flat ha y E G hEP hGP rfl hspeed hflat hoverlap
  have hlength : pointActualEdgeLength E = (r : ℝ) := by
    change (pointSmoothConformalEDist a y (D.ray 0) (F q).1).toReal = r
    rw [← hcenter, hd]
    change dist (0 : ℂ) (r : ℂ) = r
    simp only [dist_zero_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (show (0 : ℝ) ≤ (r : ℝ) from r.2)]
  have h := congrFun heq (⟨1, by norm_num⟩ : unitInterval)
  rw [E.curve_finish, G.curve_finish] at h
  change (F q).1 = D.ray ⟨pointActualEdgeLength E, _⟩ at h
  have htime : (⟨pointActualEdgeLength E, (pointActualEdgeLength_pos ha y E).le⟩ : NNReal) = r :=
    Subtype.ext hlength
  rwa [htime] at h

/-- Actual closed-sector existence with the exact prescribed whole bottom,
ambient and intrinsic all-pairs isometry, literal open-interior clearance,
properness and every rectifiable-curve metric length preserved. -/
theorem exists_actual_closed_sector_with_bottom :
    ∃ F : closedEuclideanSector D.beta → P,
      (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
      (∀ x z, (pointRegionIntrinsicEDist ha y P (F x).1 (F z).1).toReal = dist x z) ∧
      (∀ r : NNReal, ∀ hr : (r : ℂ) ∈ closedEuclideanSector D.beta, (F ⟨(r : ℂ), hr⟩).1 = D.ray r) ∧
      (∀ z, z.1 ∈ interior (closedEuclideanSector D.beta) →
        (F z).1 ∈ interior P ∧ (F z).1 ∉ pointSignedMarked D.nu D.alpha) ∧
      Topology.IsClosedEmbedding (fun z ↦ (F z).1) ∧ IsProperMap (fun z ↦ (F z).1) ∧
      (∀ z, ‖z.1‖ ≤ D.chart.radius → (F z).1 = D.chart.flatInverse z.1) ∧
      ∀ γ : ℝ → closedEuclideanSector D.beta, ∀ s t,
        pointConformalMetricLength ha y (fun r ↦ (F (γ r)).1) s t = eVariationOn γ (Icc s t) := by
  obtain ⟨F, hd, hi, hseed, hreg, hclosed, hproper, hlength⟩ := D.exists_actual_closed_sector_map
  exact ⟨F, hd, hi, D.completed_map_bottom F hd hseed,
    fun z hz ↦ hreg z (closedEuclideanSector_interior_strict_arg D.beta_pos D.beta_pi hz),
    hclosed, hproper, hseed, hlength⟩

end PointActualSectorData
end RepulsiveCoulomb
