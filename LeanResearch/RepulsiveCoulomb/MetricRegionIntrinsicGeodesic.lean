import LeanResearch.RepulsiveCoulomb.MetricRegionIntrinsicTopology
import LeanResearch.RepulsiveCoulomb.MetricRegionPathBisection
import LeanResearch.RepulsiveCoulomb.MetricMidpointGeodesic

/-! Actual minimizing segments for the constrained path metric. Approximate
midpoints come from bisection of a near-minimizing continuous path; properness
then supplies exact midpoints and the accepted dyadic construction. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X]

theorem metricRegionIntrinsic_approximate_midpoint {P : Set X}
    (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P) (x z : P) (r : ℝ)
    (hr : (metricRegionPathEDist P x.1 z.1).toReal / 2 < r) :
    ∃ p : P, (metricRegionPathEDist P x.1 p.1).toReal < r ∧
      (metricRegionPathEDist P p.1 z.1).toReal < r := by
  have hDfin := (metricRegionPathEDist_lt_top_of_connected hconn hlocal x.2 z.2).ne
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hD : metricRegionPathEDist P x.1 z.1 < ENNReal.ofReal (2 * r) := by
    rw [← ENNReal.ofReal_toReal hDfin]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
    linarith
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hD
  have hγfin : γ.length ≠ ⊤ := ne_top_of_lt (hγ.trans_le le_top)
  have hγr : γ.length.toReal < 2 * r := by
    exact ((ENNReal.toReal_lt_toReal hγfin ENNReal.ofReal_ne_top).mpr hγ).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  obtain ⟨t, ht, hleft, hright⟩ := γ.exists_length_bisection hγfin
  let p : P := ⟨γ.toFun t, γ.mapsTo ht⟩
  have hLfin : eVariationOn γ.toFun (Icc (0 : ℝ) t) ≠ ⊤ :=
    ne_top_of_le_ne_top hγfin (eVariationOn.mono γ.toFun (Icc_subset_Icc le_rfl ht.2))
  have hRfin : eVariationOn γ.toFun (Icc t (1 : ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hγfin (eVariationOn.mono γ.toFun (Icc_subset_Icc ht.1 le_rfl))
  have hL := metricRegionPathEDist_le_length (γ.subpath 0 t (by norm_num) ht)
  rw [MetricRegionLengthPath.length_subpath, uIcc_of_le ht.1, γ.source] at hL
  have hR := metricRegionPathEDist_le_length (γ.subpath t 1 ht (by norm_num))
  rw [MetricRegionLengthPath.length_subpath, uIcc_of_le ht.2, γ.target] at hR
  have hL' := ENNReal.toReal_mono hLfin hL
  have hR' := ENNReal.toReal_mono hRfin hR
  rw [hleft] at hL'
  rw [hright] at hR'
  exact ⟨p, by change (metricRegionPathEDist P x.1 (γ.toFun t)).toReal < r; linarith,
    by change (metricRegionPathEDist P (γ.toFun t) z.1).toReal < r; linarith⟩

theorem exists_metricRegionIntrinsic_geodesic [ProperSpace X] {P : Set X}
    (hclosed : IsClosed P) (hconn : IsPreconnected P) (hlocal : MetricRegionRadialPaths P)
    (x z : P) :
    ∃ γ : unitInterval → P, γ 0 = x ∧ γ 1 = z ∧ Continuous γ ∧
      ∀ s t, (metricRegionPathEDist P (γ s).1 (γ t).1).toReal =
        |t.1 - s.1| * (metricRegionPathEDist P x.1 z.1).toReal := by
  let dP := metricRegionIntrinsicMetricSpace P hconn hlocal
  have hproper := metricRegionIntrinsicMetricSpace_proper hclosed hconn hlocal
  have hcomplete := metricRegionIntrinsicMetricSpace_complete hclosed hconn hlocal
  have hmid : ∀ u v : P, ∃ p,
      @dist P dP.toDist u p = @dist P dP.toDist u v / 2 ∧
      @dist P dP.toDist p v = @dist P dP.toDist u v / 2 :=
    @proper_exists_midpoint_of_approximate P dP hproper
      (fun u v r hr ↦ metricRegionIntrinsic_approximate_midpoint hconn hlocal u v r hr)
  obtain ⟨γ, h0, h1, hc, hd⟩ := @exists_geodesic_of_exact_midpoints P dP hcomplete hmid x z
  have hc' : Continuous γ := by
    change @Continuous unitInterval P _
      (metricRegionIntrinsicMetricSpace P hconn hlocal).toUniformSpace.toTopologicalSpace γ at hc
    rwa [metricRegionIntrinsicMetricSpace_topology hconn hlocal] at hc
  exact ⟨γ, h0, h1, hc', hd⟩

end RepulsiveCoulomb
