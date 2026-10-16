import LeanResearch.RepulsiveCoulomb.PointRetainedRegionIntrinsicMetric

/-! Actual radial legs of an intrinsic minimizer issuing from a retained chart
center. Endpoint saturation forces ambient minimality on each individual leg.
No through-vertex ambient minimality or residual ambient convexity is assumed. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

theorem PointRetainedConeNeighborhood.intrinsic_center_eq {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hp : p ∈ P) (hz : z ∈ P)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius) :
    pointRegionIntrinsicEDist ha y P p z = pointSmoothConformalEDist a y p z := by
  obtain ⟨γ, hc, h0, h1, hP, hlen⟩ := C.exists_radial_path ha y hp hz hzR
  apply le_antisymm
  · exact (iInf_le _ ⟨γ, h0, h1, hc.continuousOn, hP⟩).trans_eq hlen
  · rw [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y]
    exact @edist_le_metricRegionPathEDist ℂ (pointSmoothConformalMetricSpace ha y) P p z

theorem PointRetainedConeNeighborhood.intrinsic_geodesic_from_center_radial
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p))
    {p z : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (γ : unitInterval → ℂ) (h0 : γ 0 = p) (h1 : γ 1 = z) (hP : ∀ t, γ t ∈ P)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius)
    (hd : ∀ s t, (pointRegionIntrinsicEDist ha y P (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointRegionIntrinsicEDist ha y P p z).toReal) :
    (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal) ∧
      ∀ t, C.chart (γ t) = t.1 • C.chart z := by
  have hp : p ∈ P := h0 ▸ hP 0
  have hz : z ∈ P := h1 ▸ hP 1
  have hcenter := C.intrinsic_center_eq ha y hp hz hzR
  have hconn' : @IsPreconnected ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hradialPaths := pointRetainedConeNeighborhoods_radialPaths ha y hcharts
  have hupper (s t : unitInterval) :
      (pointSmoothConformalEDist a y (γ s) (γ t)).toReal ≤
        (pointRegionIntrinsicEDist ha y P (γ s) (γ t)).toReal := by
    rw [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y]
    exact ENNReal.toReal_mono
      (@metricRegionPathEDist_lt_top_of_connected ℂ (pointSmoothConformalMetricSpace ha y)
        P hconn' hradialPaths _ _ (hP s) (hP t)).ne
      (@edist_le_metricRegionPathEDist ℂ (pointSmoothConformalMetricSpace ha y) P (γ s) (γ t))
  let c := (pointSmoothConformalEDist a y p z).toReal
  have hordered : ∀ s t : unitInterval, s ≤ t →
      (pointSmoothConformalEDist a y (γ s) (γ t)).toReal ≤ c * (t.1 - s.1) := by
    intro s t hst
    have h := hupper s t
    rw [hd s t, hcenter, abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from hst))] at h
    exact h.trans_eq (mul_comm _ _)
  have hfull : (pointSmoothConformalEDist a y (γ 0) (γ 1)).toReal = c := by rw [h0, h1]
  have heq := @metricInterval_distance_of_endpoint_eq ℂ
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace c γ hordered hfull
  have hgeo : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal := by
    intro s t
    exact (heq s t).trans (mul_comm _ _)
  refine ⟨hgeo, ?_⟩
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hL : (pointSmoothConformalEDist a y p z).toReal = ‖C.chart z‖ := by
    rw [pointSmoothConformalEDist_comm a y p z, C.metric z hzR p hpp,
      C.center, pointClassicalConeDist_apex]
  have hball (t : unitInterval) : (pointSmoothConformalEDist a y (γ t) p).toReal ≤ C.radius := by
    have h := hgeo t 0
    rw [h0] at h
    change (pointSmoothConformalEDist a y (γ t) p).toReal = |0 - t.1| * _ at h
    rw [zero_sub, abs_neg, abs_of_nonneg t.2.1] at h
    rw [h]
    apply (mul_le_of_le_one_left ENNReal.toReal_nonneg t.2.2).trans
    rwa [pointSmoothConformalEDist_comm a y p z]
  intro t
  apply classicalCone_geodesic_from_apex_nonneg (α := coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
    (fun s ↦ C.chart (γ s)) (C.chart z)
    ((congrArg C.chart h0).trans C.center) (congrArg C.chart h1)
  intro s u
  change pointClassicalConeDist a y p (C.chart (γ s)) (C.chart (γ u)) = _
  rw [← C.metric (γ s) (hball s) (γ u) (hball u), hgeo, hL]

end RepulsiveCoulomb
