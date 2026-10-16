import LeanResearch.RepulsiveCoulomb.PointRetainedIntervalLocalMetric
import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicRadialGerms
import LeanResearch.RepulsiveCoulomb.ClassicalConeRetainedChord
import LeanResearch.RepulsiveCoulomb.ClassicalConeRetainedPassage

/-! The actual short-chord contradiction at a retained interval-cone vertex.
An intrinsically minimizing passage through the vertex must have unwrapped
physical separation at least pi. This conclusion is derived from a literal
short competitor, not assumed as part of a polyhedral-region certificate. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

theorem PointRetainedConeNeighborhood.intrinsic_additive_pair_angle_ge_pi
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p x z : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hp : p ∈ P) (hx : x ∈ P) (hz : z ∈ P)
    (hxR : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius / 4)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius / 4)
    {r s θ φ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hθ : θ ∈ Icc C.lo C.hi) (hφ : φ ∈ Icc C.lo C.hi) (hθφ : θ ≤ φ)
    (hchartx : C.chart x = pointRadialSectorPoint r θ)
    (hchartz : C.chart z = pointRadialSectorPoint s φ)
    (hadd : (pointRegionIntrinsicEDist ha y P x z).toReal = r + s) :
    Real.pi ≤ (coalescedPointExponent a y p / 2 + 1) * (φ - θ) := by
  by_contra hnot
  have hshort := lt_of_not_ge hnot
  have hα : 0 ≤ coalescedPointExponent a y p / 2 :=
    div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hxfull : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius := by linarith [C.radius_pos]
  have hzfull : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius := by linarith [C.radius_pos]
  have hxr : (pointSmoothConformalEDist a y x p).toReal = r := by
    rw [C.metric x hxfull p hpp, C.center, pointClassicalConeDist_apex,
      hchartx, pointRadialSectorPoint_norm hr.le]
  have hzs : (pointSmoothConformalEDist a y z p).toReal = s := by
    rw [C.metric z hzfull p hpp, C.center, pointClassicalConeDist_apex,
      hchartz, pointRadialSectorPoint_norm hs.le]
  have hrR : r ≤ C.radius := hxr.symm.trans_le hxfull
  have hsR : s ≤ C.radius := hzs.symm.trans_le hzfull
  obtain ⟨γ, h0, h1, hc, hmap, hlen⟩ :=
    exists_classicalCone_retained_short_chord hα hr hs hrR hsR hθ hφ hθφ hshort
  have hc' : @ContinuousOn ℝ ℂ _
      (pointClassicalConeMetricSpace a y p).toUniformSpace.toTopologicalSpace
      γ (Icc (0 : ℝ) 1) := by
    rwa [pointClassicalConeMetricSpace_topology a y p]
  let η := @MetricRegionLengthPath.ofContinuousOn ℂ
    (pointClassicalConeMetricSpace a y p).toUniformSpace.toTopologicalSpace
    (pointClosedRadialInterval C.radius C.lo C.hi)
    (pointRadialSectorPoint r θ) (pointRadialSectorPoint s φ) γ hc' h0 h1 hmap
  have hbound := @metricRegionPathEDist_le_length ℂ (pointClassicalConeMetricSpace a y p)
    (pointClosedRadialInterval C.radius C.lo C.hi)
    (pointRadialSectorPoint r θ) (pointRadialSectorPoint s φ) η
  have hηlen := @MetricRegionLengthPath.length_ofContinuousOn ℂ
    (pointClassicalConeMetricSpace a y p).toPseudoMetricSpace
    (pointClosedRadialInterval C.radius C.lo C.hi)
    (pointRadialSectorPoint r θ) (pointRadialSectorPoint s φ) γ hc' h0 h1 hmap
  have hmodel : pointRetainedIntervalEDist C (C.chart x) (C.chart z) < ENNReal.ofReal (r + s) := by
    rw [hchartx, hchartz]
    exact hbound.trans_lt (hηlen.trans_lt hlen)
  rw [← C.intrinsic_local_model ha y hp hx hz hxR hzR] at hmodel
  have hfinite : pointRegionIntrinsicEDist ha y P x z ≠ ⊤ :=
    ne_top_of_lt (hmodel.trans_le le_top)
  have hreal := ((ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).mpr hmodel).trans_eq
    (ENNReal.toReal_ofReal (add_pos hr hs).le)
  rw [hadd] at hreal
  exact (lt_irrefl _ hreal)

/-- Once the intrinsic short-chord test has forced the retained separation,
admissibility supplies the other ambient side. Thus this actual minimizing
passage has exactly its ambient distance. -/
theorem PointRetainedConeNeighborhood.admissible_additive_pair_ambient
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p x z : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (hp : p ∈ P) (hx : x ∈ P) (hz : z ∈ P)
    (hxR : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius / 4)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius / 4)
    {r s θ φ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hθ : θ ∈ Icc C.lo C.hi) (hφ : φ ∈ Icc C.lo C.hi) (hθφ : θ ≤ φ)
    (hchartx : C.chart x = pointRadialSectorPoint r θ)
    (hchartz : C.chart z = pointRadialSectorPoint s φ)
    (hadd : (pointRegionIntrinsicEDist ha y P x z).toReal = r + s) :
    pointRegionIntrinsicEDist ha y P x z = pointSmoothConformalEDist a y x z := by
  have hα : 0 ≤ coalescedPointExponent a y p / 2 :=
    div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hsep := C.intrinsic_additive_pair_angle_ge_pi ha y hp hx hz hxR hzR
    hr hs hθ hφ hθφ hchartx hchartz hadd
  have hwidth : φ - θ ≤ C.hi - C.lo := by linarith [hθ.1, hφ.2]
  have hcomp : Real.pi ≤ (coalescedPointExponent a y p / 2 + 1) * (2 * Real.pi - (φ - θ)) := by
    apply hadm.trans
    exact mul_le_mul_of_nonneg_left (by linarith) (by linarith : 0 ≤ coalescedPointExponent a y p / 2 + 1)
  have hambient : (pointSmoothConformalEDist a y x z).toReal = r + s := by
    rw [C.metric x (by linarith [C.radius_pos]) z (by linarith [C.radius_pos]), hchartx, hchartz]
    exact classicalCone_retained_through_apex hα hr hs hθφ
      (hwidth.trans C.width_le_full) hsep hcomp
  have hfin : pointRegionIntrinsicEDist ha y P x z ≠ ⊤ := by
    intro he
    rw [he, ENNReal.toReal_top] at hadd
    linarith
  rw [← ENNReal.ofReal_toReal hfin,
    ← ENNReal.ofReal_toReal (pointSmoothConformalEDist_lt_top ha y x z).ne]
  exact congrArg ENNReal.ofReal (hadd.trans hambient.symm)

/-- The retained directions are extracted from the actual chart membership.
This is the full local passage criterion, including an endpoint equal to the
center. No angular witnesses are supplied by the caller. -/
theorem PointRetainedConeNeighborhood.admissible_intrinsic_additive_pair_ambient
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p x z : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (hp : p ∈ P) (hx : x ∈ P) (hz : z ∈ P)
    (hxR : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius / 4)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius / 4)
    (hadd : (pointRegionIntrinsicEDist ha y P x z).toReal =
      (pointRegionIntrinsicEDist ha y P x p).toReal +
      (pointRegionIntrinsicEDist ha y P p z).toReal) :
    pointRegionIntrinsicEDist ha y P x z = pointSmoothConformalEDist a y x z := by
  have hcomm (u v : ℂ) : pointRegionIntrinsicEDist ha y P u v = pointRegionIntrinsicEDist ha y P v u := by
    rw [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y,
      pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y]
    exact @metricRegionPathEDist_comm ℂ (pointSmoothConformalMetricSpace ha y) P u v
  have hxfull : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius := by linarith [C.radius_pos]
  have hzfull : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius := by linarith [C.radius_pos]
  by_cases hxp : x = p
  · subst x
    exact C.intrinsic_center_eq ha y hp hz hzfull
  by_cases hzp : z = p
  · subst z
    rw [hcomm, pointSmoothConformalEDist_comm a y x p]
    exact C.intrinsic_center_eq ha y hp hx hxfull
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  obtain ⟨r, hr, θ, hθ, hchartx⟩ := (C.retained x hxfull).mp hx
  obtain ⟨s, hs, φ, hφ, hchartz⟩ := (C.retained z hzfull).mp hz
  have hr0 : 0 < r := by
    by_contra h
    have hrz : r = 0 := le_antisymm (le_of_not_gt h) hr.1
    rw [hrz] at hchartx
    have hex : C.chart x = C.chart p := by simpa [pointRadialSectorPoint, C.center] using hchartx
    exact hxp (C.chart.injOn (C.source hxfull) (C.source hpp) hex)
  have hs0 : 0 < s := by
    by_contra h
    have hsz : s = 0 := le_antisymm (le_of_not_gt h) hs.1
    rw [hsz] at hchartz
    have hez : C.chart z = C.chart p := by simpa [pointRadialSectorPoint, C.center] using hchartz
    exact hzp (C.chart.injOn (C.source hzfull) (C.source hpp) hez)
  have hxr : (pointSmoothConformalEDist a y x p).toReal = r := by
    rw [C.metric x hxfull p hpp, C.center, pointClassicalConeDist_apex,
      hchartx, pointRadialSectorPoint_norm hr.1]
  have hzs : (pointSmoothConformalEDist a y z p).toReal = s := by
    rw [C.metric z hzfull p hpp, C.center, pointClassicalConeDist_apex,
      hchartz, pointRadialSectorPoint_norm hs.1]
  have hsum : (pointRegionIntrinsicEDist ha y P x z).toReal = r + s := by
    rw [hadd, hcomm x p, C.intrinsic_center_eq ha y hp hx hxfull,
      C.intrinsic_center_eq ha y hp hz hzfull,
      pointSmoothConformalEDist_comm a y p x, pointSmoothConformalEDist_comm a y p z,
      hxr, hzs]
  rcases le_total θ φ with hθφ | hφθ
  · exact C.admissible_additive_pair_ambient ha y hadm hp hx hz hxR hzR
      hr0 hs0 hθ hφ hθφ hchartx hchartz hsum
  · have hsum' : (pointRegionIntrinsicEDist ha y P z x).toReal = s + r := by
      rw [hcomm z x, hsum, add_comm]
    have h := C.admissible_additive_pair_ambient ha y hadm hp hz hx hzR hxR
      hs0 hr0 hφ hθ hφθ hchartz hchartx hsum'
    rwa [hcomm z x, pointSmoothConformalEDist_comm a y z x] at h

end RepulsiveCoulomb
