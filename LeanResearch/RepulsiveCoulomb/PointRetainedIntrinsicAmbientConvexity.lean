module

public import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicAngle
public import LeanResearch.RepulsiveCoulomb.MetricCenteredIntervalCriterion
public import LeanResearch.RepulsiveCoulomb.PointActualGeodesicContinuation

@[expose] public section

/-! Admissible actual retained regions are ambient convex. Intrinsic metrics
and minimizing segments have already been constructed from curve lengths.
At a boundary chart, short chords give the first ambient side angle and the
removed-side invariant gives the second. Only then is ambient local-to-global
applied. Initial-line boundary replacement is never used for residual regions. -/
noncomputable section
open Set Topology
open scoped ENNReal
namespace RepulsiveCoulomb

def PointRetainedConeNeighborhood.Full {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p) : Prop :=
  ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ C.radius → z ∈ P

theorem pointRegionIntrinsicEDist_eq_of_contained_geodesic {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ} {x z : ℂ}
    (η : unitInterval → ℂ) (h0 : η 0 = x) (h1 : η 1 = z) (hc : Continuous η)
    (hP : ∀ t, η t ∈ P)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (η s) (η t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal) :
    pointRegionIntrinsicEDist ha y P x z = pointSmoothConformalEDist a y x z := by
  let γ := IccExtend (show (0 : ℝ) ≤ 1 by norm_num) η
  have hγ (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : γ t = η ⟨t, ht⟩ := IccExtend_of_mem _ _ ht
  have hγ0 : γ 0 = x := (hγ 0 (by norm_num)).trans h0
  have hγ1 : γ 1 = z := (hγ 1 (by norm_num)).trans h1
  have hγc : Continuous γ := continuous_IccExtend_iff.mpr hc
  have hγP : MapsTo γ (Icc (0 : ℝ) 1) P := by
    intro t ht
    rw [hγ t ht]
    exact hP ⟨t, ht⟩
  have hlen : pointConformalMetricLength ha y γ 0 1 = pointSmoothConformalEDist a y x z := by
    rw [← hγ0, ← hγ1]
    apply pointConformalMetricLength_of_geodesic ha y
    intro s hs t ht
    rw [hγ0, hγ1, hγ s hs, hγ t ht]
    exact hd ⟨s, hs⟩ ⟨t, ht⟩
  apply le_antisymm ((iInf_le _ ⟨γ, hγ0, hγ1, hγc.continuousOn, hγP⟩).trans_eq hlen)
  change pointSmoothConformalEDist a y x z ≤ pointRegionIntrinsicEDist ha y P x z
  rw [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y]
  exact @edist_le_metricRegionPathEDist ℂ (pointSmoothConformalMetricSpace ha y) P x z

theorem PointRetainedConeNeighborhood.full_intrinsic_pair_ambient
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p x z : ℂ} (C : PointRetainedConeNeighborhood a y P p) (hfull : C.Full)
    (hxR : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius / 4)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius / 4) :
    pointRegionIntrinsicEDist ha y P x z = pointSmoothConformalEDist a y x z := by
  obtain ⟨γ, h0, h1, hc, hd⟩ := exists_pointConformal_geodesic ha y x z
  apply pointRegionIntrinsicEDist_eq_of_contained_geodesic ha y γ h0 h1 hc _ hd
  intro t
  apply hfull
  have hleg := hd t ⟨0, by norm_num⟩
  rw [h0] at hleg
  change (pointSmoothConformalEDist a y (γ t) x).toReal = |0 - t.1| * _ at hleg
  rw [zero_sub, abs_neg, abs_of_nonneg t.2.1] at hleg
  have hlegle := mul_le_of_le_one_left
    (ENNReal.toReal_nonneg (a := pointSmoothConformalEDist a y x z)) t.2.2
  rw [← hleg] at hlegle
  have htri := @dist_triangle ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace (γ t) x p
  have hends := @dist_triangle ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace x p z
  change (pointSmoothConformalEDist a y (γ t) p).toReal ≤
    (pointSmoothConformalEDist a y (γ t) x).toReal + (pointSmoothConformalEDist a y x p).toReal at htri
  change (pointSmoothConformalEDist a y x z).toReal ≤
    (pointSmoothConformalEDist a y x p).toReal + (pointSmoothConformalEDist a y p z).toReal at hends
  rw [pointSmoothConformalEDist_comm a y p z] at hends
  linarith [C.radius_pos]

/-- Every already-constructed intrinsic minimizing curve is an ambient local
geodesic, then globally minimizing. A chart is either a literal full interior
disk or an actual retained interval with removed-side physical angle at least pi. -/
theorem pointRetained_intrinsic_geodesic_ambient {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Full ∨ C.Admissible)
    (γ : unitInterval → ℂ) (hc : Continuous γ) (hP : ∀ t, γ t ∈ P) (c : ℝ)
    (hd : ∀ s t, (pointRegionIntrinsicEDist ha y P (γ s) (γ t)).toReal = c * |t.1 - s.1|) :
    ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = c * |t.1 - s.1| := by
  have hall : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p) := by
    intro p hp
    obtain ⟨C, _⟩ := hcharts p hp
    exact ⟨C⟩
  have hconn' : @IsPreconnected ℂ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace P := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hradial := pointRetainedConeNeighborhoods_radialPaths ha y hall
  have hcomm (u v : ℂ) : pointRegionIntrinsicEDist ha y P u v = pointRegionIntrinsicEDist ha y P v u := by
    rw [pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y,
      pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y]
    exact @metricRegionPathEDist_comm ℂ (pointSmoothConformalMetricSpace ha y) P u v
  have hupper (s t : unitInterval) : (pointSmoothConformalEDist a y (γ s) (γ t)).toReal ≤ c * |t.1 - s.1| := by
    rw [← hd s t, pointRegionIntrinsicEDist_eq_metricRegionPathEDist ha y]
    exact ENNReal.toReal_mono
      (@metricRegionPathEDist_lt_top_of_connected ℂ (pointSmoothConformalMetricSpace ha y)
        P hconn' hradial _ _ (hP s) (hP t)).ne
      (@edist_le_metricRegionPathEDist ℂ (pointSmoothConformalMetricSpace ha y) P (γ s) (γ t))
  apply pointConformal_local_geodesic_global ha y γ
  intro t₀
  obtain ⟨C, hcase⟩ := hcharts (γ t₀) (hP t₀)
  let U : Set unitInterval := {t | (pointSmoothConformalEDist a y (γ t) (γ t₀)).toReal < C.radius / 4}
  have hc' : @Continuous unitInterval ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ := by
    rwa [pointSmoothConformalMetricSpace_topology ha y]
  have hU : IsOpen U := by
    exact @IsOpen.preimage unitInterval ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ hc' _
      (@Metric.isOpen_ball ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
        (γ t₀) (C.radius / 4))
  have ht₀ : t₀ ∈ U := by
    change (pointSmoothConformalEDist a y (γ t₀) (γ t₀)).toReal < C.radius / 4
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact div_pos C.radius_pos (by norm_num)
  refine ⟨U, hU, ht₀, ?_⟩
  apply @metric_interval_eq_of_center_and_cross_pairs ℂ
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace γ c t₀ U
  · exact fun s _ t _ ↦ hupper s t
  · intro s hs
    have hsR : (pointSmoothConformalEDist a y (γ s) (γ t₀)).toReal ≤ C.radius := by
      have h := hs
      change (pointSmoothConformalEDist a y (γ s) (γ t₀)).toReal < C.radius / 4 at h
      linarith [C.radius_pos]
    have heq := C.intrinsic_center_eq ha y (hP t₀) (hP s) hsR
    have h := hd s t₀
    rw [hcomm (γ s) (γ t₀), heq, pointSmoothConformalEDist_comm a y (γ t₀) (γ s)] at h
    exact h
  · intro s hs t ht hst₀ ht₀t
    have hsR : (pointSmoothConformalEDist a y (γ s) (γ t₀)).toReal ≤ C.radius / 4 := hs.le
    have htR : (pointSmoothConformalEDist a y (γ t) (γ t₀)).toReal ≤ C.radius / 4 := ht.le
    have heq : pointRegionIntrinsicEDist ha y P (γ s) (γ t) = pointSmoothConformalEDist a y (γ s) (γ t) := by
      rcases hcase with hfull | hadm
      · exact C.full_intrinsic_pair_ambient ha y hfull hsR htR
      · apply C.admissible_intrinsic_additive_pair_ambient ha y hadm (hP t₀) (hP s) (hP t) hsR htR
        rw [hd s t, hd s t₀, hd t₀ t,
          abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from hst₀.trans ht₀t)),
          abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t₀.1 from hst₀)),
          abs_of_nonneg (sub_nonneg.mpr (show t₀.1 ≤ t.1 from ht₀t))]
        ring
    change (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = c * (t.1 - s.1)
    rw [← heq, hd s t, abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from hst₀.trans ht₀t))]

/-- Actual residual convexity and intrinsic/ambient equality, after the
intrinsic minimizers and the local angle criterion have both been proved. -/
theorem pointRetainedRegion_intrinsic_eq_and_geodesicallyConvex {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ}
    (hclosed : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Full ∨ C.Admissible) :
    PointGeodesicallyConvex a y P ∧ ∀ x ∈ P, ∀ z ∈ P,
      pointRegionIntrinsicEDist ha y P x z = pointSmoothConformalEDist a y x z := by
  have hall : ∀ p ∈ P, Nonempty (PointRetainedConeNeighborhood a y P p) := by
    intro p hp
    obtain ⟨C, _⟩ := hcharts p hp
    exact ⟨C⟩
  have hpair (x : ℂ) (hx : x ∈ P) (z : ℂ) (hz : z ∈ P) :
      pointRegionIntrinsicEDist ha y P x z = pointSmoothConformalEDist a y x z ∧
      ∃ γ : unitInterval → ℂ, γ 0 = x ∧ γ 1 = z ∧ Continuous γ ∧ (∀ t, γ t ∈ P) ∧
        ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
          |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal := by
    obtain ⟨η, h0, h1, hc, hd⟩ := exists_pointRetainedRegion_intrinsic_geodesic
      ha y hclosed hconn hall ⟨x, hx⟩ ⟨z, hz⟩
    let γ : unitInterval → ℂ := fun t ↦ (η t).1
    have hγ0 : γ 0 = x := congrArg Subtype.val h0
    have hγ1 : γ 1 = z := congrArg Subtype.val h1
    have hγc : Continuous γ := continuous_subtype_val.comp hc
    have hγP : ∀ t, γ t ∈ P := fun t ↦ (η t).2
    let c := (pointRegionIntrinsicEDist ha y P x z).toReal
    have hamb := pointRetained_intrinsic_geodesic_ambient ha y hconn hcharts γ hγc hγP c
      (fun s t ↦ (hd s t).trans (mul_comm _ _))
    have hcend : (pointSmoothConformalEDist a y x z).toReal = c := by
      have h := hamb 0 1
      rw [hγ0, hγ1] at h
      simpa only [Set.Icc.coe_zero, Set.Icc.coe_one, sub_zero, abs_one, mul_one] using h
    have hgeo : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal := by
      intro s t
      rw [hamb s t, hcend, mul_comm]
    exact ⟨pointRegionIntrinsicEDist_eq_of_contained_geodesic ha y γ hγ0 hγ1 hγc hγP hgeo,
      γ, hγ0, hγ1, hγc, hγP, hgeo⟩
  exact ⟨fun x hx z hz ↦ (hpair x hx z hz).2, fun x hx z hz ↦ (hpair x hx z hz).1⟩

end RepulsiveCoulomb
