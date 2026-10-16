import LeanResearch.RepulsiveCoulomb.PointConformalConnection
import LeanResearch.RepulsiveCoulomb.PointConformalMetricCharts

/-! A constructed actual local isometric developing chart which retains its
holomorphic phase potential. Its derivative is exactly exp(H), and H' is the
literal logarithmic connection. These data are needed to derive geodesic turn
from point-argument increments, rather than postulate a conformal flux law. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem exists_pointConformal_phase_metric_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ} (hp : p ∉ pointPunctures a y) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ H : ℂ → ℂ, ∃ r : ℝ,
      0 < r ∧ p ∈ e.source ∧ e p = 0 ∧ ball p r ⊆ e.source ∧
      e.source ⊆ (pointPunctures a y)ᶜ ∧
      AnalyticOnNhd ℂ e.symm e.target ∧ AnalyticOnNhd ℂ H e.source ∧
      (∀ z ∈ e.source, AnalyticAt ℂ e z ∧
        deriv e z = Complex.exp (H z) ∧ (H z).re = pointConformalLog a y z ∧
        deriv H z = pointConformalConnection a y z) ∧
      ∀ u ∈ ball p r, ∀ v ∈ ball p r,
        pointSmoothConformalEDist a y u v = ENNReal.ofReal ‖e v - e u‖ := by
  obtain ⟨R, hR, hdomain, H, hH, hphase⟩ := exists_pointConformal_connection_potential ha y hp
  have hExp : DifferentiableOn ℂ (fun z => Complex.exp (H z)) (ball p R) := by
    intro z hz
    exact ((hH z hz).differentiableAt.cexp).differentiableWithinAt
  obtain ⟨F, hFp, hF⟩ := hExp.isExactOn_ball.with_val_at p 0
  have hFd : DifferentiableOn ℂ F (ball p R) :=
    fun z hz => (hF z hz).differentiableAt.differentiableWithinAt
  have hFA : AnalyticOnNhd ℂ F (ball p R) := hFd.analyticOnNhd isOpen_ball
  have hFne (z : ℂ) (hz : z ∈ ball p R) : deriv F z ≠ 0 := by
    rw [(hF z hz).deriv]
    exact Complex.exp_ne_zero _
  have hc : ContDiffAt ℂ 1 F p := (hFA p (mem_ball_self hR)).contDiffAt
  have hstrict := (hc.hasStrictDerivAt one_ne_zero).hasStrictFDerivAt_equiv
    (hFne p (mem_ball_self hR))
  let e₀ := hstrict.toOpenPartialHomeomorph F
  let e := e₀.restrOpen (ball p R) isOpen_ball
  have hsub : e.source ⊆ ball p R := fun _ hz => hz.2
  have hep : p ∈ e.source := ⟨hstrict.mem_toOpenPartialHomeomorph_source, mem_ball_self hR⟩
  have he0 : e p = 0 := hFp
  have heA (z : ℂ) (hz : z ∈ e.source) : AnalyticAt ℂ e z := hFA z (hsub hz)
  have heD (z : ℂ) (hz : z ∈ e.source) : deriv e z = Complex.exp (H z) :=
    (hF z (hsub hz)).deriv
  have heN (z : ℂ) (hz : z ∈ e.source) : deriv e z ≠ 0 := by
    rw [heD z hz]
    exact Complex.exp_ne_zero _
  have heNorm (z : ℂ) (hz : z ∈ e.source) : ‖deriv e z‖ = pointConformalDensity a y z := by
    rw [heD z hz]
    exact (hphase z (hsub hz)).2.2
  have hinv : AnalyticOnNhd ℂ e.symm e.target := holomorphic_chart_inverse_analytic e heA heN
  have hmetricDeriv : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧
      pointConformalDensity (standardConeExponents 0) standardConeLocations (e z) * ‖deriv e z‖ =
        pointConformalDensity a y z := by
    intro z hz
    refine ⟨heA z hz, ?_⟩
    rw [standardCone_density, Real.rpow_zero, one_mul]
    exact heNorm z hz
  have hb : ∀ j, 0 ≤ standardConeExponents 0 j := by simp [standardConeExponents]
  obtain ⟨r, hr, hball, hmetric⟩ := pointConformal_chart_local_metric_eq ha y hb
    standardConeLocations e hmetricDeriv hinv hep
  refine ⟨e, H, r, hr, hep, he0, hball, hsub.trans hdomain, hinv,
    hH.mono hsub, ?_, ?_⟩
  · intro z hz
    exact ⟨heA z hz, heD z hz, (hphase z (hsub hz)).1, (hphase z (hsub hz)).2.1⟩
  · intro u hu v hv
    rw [hmetric u hu v hv, standardCone_zero_distance]

end RepulsiveCoulomb
