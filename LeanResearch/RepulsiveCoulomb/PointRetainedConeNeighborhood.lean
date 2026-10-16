import LeanResearch.RepulsiveCoulomb.PointClosedRegionIntrinsicMetric
import LeanResearch.RepulsiveCoulomb.PointGeodesicStarGerms
import LeanResearch.RepulsiveCoulomb.PointRadialSectorTopology
import LeanResearch.RepulsiveCoulomb.MetricRegionIntrinsicGeodesic

/-! Literal retained intervals in actual point-cone disks. These are local
geometric inputs for an actual closed subset, to be supplied by the cut-contact
construction. No convexity or intrinsic metric is included in the input. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

def pointClosedRadialInterval (R lo hi : ℝ) : Set ℂ :=
  {w | ∃ r ∈ Icc (0 : ℝ) R, ∃ θ ∈ Icc lo hi, w = pointRadialSectorPoint r θ}

theorem pointClosedRadialInterval_smul {R lo hi : ℝ} {w : ℂ}
    (hw : w ∈ pointClosedRadialInterval R lo hi) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    t • w ∈ pointClosedRadialInterval R lo hi := by
  obtain ⟨r, hr, θ, hθ, rfl⟩ := hw
  refine ⟨t * r, ⟨mul_nonneg ht.1 hr.1, ?_⟩, θ, hθ, ?_⟩
  · exact (mul_le_of_le_one_left hr.1 ht.2).trans hr.2
  · simp only [pointRadialSectorPoint, Complex.real_smul, Complex.ofReal_mul]
    ring

/-- A full metric cone disk and its literal retained interval. The disk is an
actual ambient point-metric disk and the chart identifies all its pair distances. -/
structure PointRetainedConeNeighborhood {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (P : Set ℂ) (p : ℂ) where
  chart : OpenPartialHomeomorph ℂ ℂ
  radius : ℝ
  radius_pos : 0 < radius
  center : chart p = 0
  source : {z : ℂ | (pointSmoothConformalEDist a y z p).toReal ≤ radius} ⊆ chart.source
  onto : BijOn chart {z : ℂ | (pointSmoothConformalEDist a y z p).toReal ≤ radius}
    {w : ℂ | ‖w‖ ≤ radius}
  metric : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ radius →
    ∀ w, (pointSmoothConformalEDist a y w p).toReal ≤ radius →
      (pointSmoothConformalEDist a y z w).toReal = pointClassicalConeDist a y p (chart z) (chart w)
  lo : ℝ
  hi : ℝ
  width_pos : lo < hi
  width_le_full : hi - lo ≤ 2 * Real.pi
  retained : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ radius →
    (z ∈ P ↔ chart z ∈ pointClosedRadialInterval radius lo hi)

/-- Admissibility is a separate removed-side angle condition. It is deliberately
absent from every metric-existence theorem below. -/
def PointRetainedConeNeighborhood.Admissible {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p) : Prop :=
  Real.pi ≤ (coalescedPointExponent a y p / 2 + 1) * (2 * Real.pi - (C.hi - C.lo))

/-- Retained radial competitors are constructed using an actual ambient
minimizer from the chart center and its proved literal radiality. -/
theorem PointRetainedConeNeighborhood.exists_radial_path {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hp : p ∈ P) (hz : z ∈ P)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius) :
    ∃ γ : ℝ → ℂ, Continuous γ ∧ γ 0 = p ∧ γ 1 = z ∧
      MapsTo γ (Icc (0 : ℝ) 1) P ∧
      pointConformalMetricLength ha y γ 0 1 = pointSmoothConformalEDist a y p z := by
  obtain ⟨η, h0, h1, hc, hd⟩ := exists_pointConformal_geodesic ha y p z
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hL : (pointSmoothConformalEDist a y p z).toReal = ‖C.chart z‖ := by
    rw [pointSmoothConformalEDist_comm a y p z, C.metric z hzR p hpp,
      C.center, pointClassicalConeDist_apex]
  have hηR (t : unitInterval) : (pointSmoothConformalEDist a y (η t) p).toReal ≤ C.radius := by
    have h := hd t ⟨0, by norm_num⟩
    rw [h0, zero_sub, abs_neg, abs_of_nonneg t.2.1] at h
    rw [h]
    apply (mul_le_of_le_one_left ENNReal.toReal_nonneg t.2.2).trans
    rwa [pointSmoothConformalEDist_comm a y p z]
  have hradial (t : unitInterval) : C.chart (η t) = t.1 • C.chart z := by
    apply classicalCone_geodesic_from_apex_nonneg (α := coalescedPointExponent a y p / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
      (fun s ↦ C.chart (η s)) (C.chart z) (by rw [h0, C.center]) (by rw [h1])
    intro s u
    change pointClassicalConeDist a y p (C.chart (η s)) (C.chart (η u)) = _
    rw [← C.metric (η s) (hηR s) (η u) (hηR u), hd, hL]
  have hηP (t : unitInterval) : η t ∈ P := by
    apply (C.retained (η t) (hηR t)).mpr
    rw [hradial]
    exact pointClosedRadialInterval_smul ((C.retained z hzR).mp hz) t.2
  let γ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) η
  have hγ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t = η ⟨t, ht⟩ := IccExtend_of_mem _ _ ht
  have hγ0 : γ 0 = p := (hγ 0 (by norm_num)).trans h0
  have hγ1 : γ 1 = z := (hγ 1 (by norm_num)).trans h1
  have hγP : MapsTo γ (Icc (0 : ℝ) 1) P := by
    intro t ht
    rw [hγ t ht]
    exact hηP ⟨t, ht⟩
  refine ⟨γ, continuous_IccExtend_iff.mpr hc, hγ0, hγ1, hγP, ?_⟩
  rw [← hγ0, ← hγ1]
  apply pointConformalMetricLength_of_geodesic ha y
  intro s hs t ht
  rw [hγ0, hγ1, hγ s hs, hγ t ht]
  exact hd ⟨s, hs⟩ ⟨t, ht⟩

/-- Every actual retained interval chart supplies the radial-path input of the
intrinsic metric construction. No ambient pairwise convexity is assumed. -/
theorem pointRetainedConeNeighborhoods_radialPaths {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hcharts : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p)) :
    @MetricRegionRadialPaths ℂ (pointSmoothConformalMetricSpace ha y) P := by
  intro p hp
  obtain ⟨C⟩ := hcharts p hp
  refine ⟨C.radius, C.radius_pos, ?_⟩
  intro z hz hzp
  obtain ⟨γ, hc, h0, h1, hP, hlen⟩ := C.exists_radial_path ha y hp hz hzp.le
  have hc' : @Continuous ℝ ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  let Γ : @MetricRegionLengthPath ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P p z :=
    @MetricRegionLengthPath.mk ℂ
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P p z γ hc' h0 h1 hP
  refine ⟨Γ, ?_⟩
  change @MetricRegionLengthPath.length ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
    P p z Γ = pointSmoothConformalEDist a y p z
  exact hlen

end RepulsiveCoulomb
