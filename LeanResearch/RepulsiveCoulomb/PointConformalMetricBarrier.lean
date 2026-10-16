module

public import LeanResearch.RepulsiveCoulomb.PointConformalTopology

@[expose] public section

/-! A smooth scalar function with derivative dominated by rho is Lipschitz for
the smooth conformal distance. This proved transfer will be used with a proper
radial function to obtain completeness. -/
noncomputable section
open MeasureTheory Set
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem pointConformal_metric_barrier {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) {C : ℝ} (hC : 0 < C)
    (hb : ∀ z, ‖fderiv ℝ φ z‖ ≤ C * pointConformalDensity a y z) (x z : ℂ) :
    ‖φ z - φ x‖ₑ ≤ ENNReal.ofReal C * pointSmoothConformalEDist a y x z := by
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  apply (ENNReal.div_le_iff' hC0 ENNReal.ofReal_ne_top).mp
  by_contra h
  have hr := lt_of_not_ge h
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y hr
  have hbar := pointConformalPath_barrier a y hφ hC.le hb hγ.contDiffOn zero_le_one
  rw [h0, h1] at hbar
  have hmul := ENNReal.mul_lt_mul_right hC0 ENNReal.ofReal_ne_top hlen
  rw [ENNReal.mul_div_cancel hC0 ENNReal.ofReal_ne_top] at hmul
  exact (not_lt_of_ge hbar) hmul

end RepulsiveCoulomb
