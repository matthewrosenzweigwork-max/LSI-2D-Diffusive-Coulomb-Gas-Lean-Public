import LeanResearch.RepulsiveCoulomb.PointConformalMetricCharts
import LeanResearch.RepulsiveCoulomb.AnalyticRadialRectifiability

/-! A power-density cone chart retaining both analytic regularity directions and a whole closed
point-metric neighborhood in its source. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem exists_pointConformal_regular_power_cone_disk {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ R : ℝ, 0 < R ∧ e p = 0 ∧
      AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ z ∈ e.source, AnalyticAt ℂ e z ∧ deriv e z ≠ 0) ∧
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ R → z ∈ e.source) ∧
      ∀ u, (pointSmoothConformalEDist a y u p).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v p).toReal ≤ R →
          pointSmoothConformalEDist a y u v =
            pointSmoothConformalEDist (standardConeExponents (coalescedPointExponent a y p / 2))
              standardConeLocations (e u) (e v) := by
  obtain ⟨e, hep, he0, hinv, he⟩ := exists_pointConformal_cone_chart_with_inverse ha y p
  have hF : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
      pointConformalDensity (standardConeExponents (coalescedPointExponent a y p / 2))
        standardConeLocations (e z) * ‖deriv e z‖ = pointConformalDensity a y z := by
    intro z hz
    refine ⟨(he z hz).1, ?_⟩
    rw [standardCone_density]
    exact (he z hz).2.2
  have hb : ∀ j, 0 ≤ standardConeExponents (coalescedPointExponent a y p / 2) j := by
    intro j
    exact mul_nonneg (by norm_num) (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
  obtain ⟨r, hr, hsource, hd⟩ := pointConformal_chart_local_metric_eq ha y hb
    standardConeLocations e hF hinv hep
  obtain ⟨R, hR, hball⟩ := exists_real_pointConformal_ball_subset ha y isOpen_ball (mem_ball_self hr)
  have hlocal (z : ℂ) (hz : (pointSmoothConformalEDist a y z p).toReal ≤ R / 2) : z ∈ ball p r := by
    apply hball
    have hlt := ((ENNReal.ofReal_lt_ofReal_iff hR).mpr (hz.trans_lt (show R / 2 < R by linarith)))
    rw [ENNReal.ofReal_toReal (pointSmoothConformalEDist_lt_top ha y z p).ne,
      pointSmoothConformalEDist_comm a y z p] at hlt
    exact hlt
  exact ⟨e, R / 2, by positivity, he0, hinv, (fun z hz => ⟨(he z hz).1, (he z hz).2.1⟩), fun z hz => hsource (hlocal z hz),
    fun u hu v hv => hd u (hlocal u hu) v (hlocal v hv)⟩

end RepulsiveCoulomb
