module

public import LeanResearch.RepulsiveCoulomb.RadialCutoffApproximation
public import LeanResearch.RepulsiveCoulomb.PointRadialDensity

@[expose] public section

/-! An actual radial barrier lower bound for the smooth conformal path metric.
The origin is regularized with genuine C1 barriers and the cutoff is removed by
dominated convergence, so no differentiability of the norm at zero is assumed. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem radial_integral_le_pointConformalEDist {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c z : ℂ)
    (h : ℝ → ℝ) (hc : Continuous h) (hn : ∀ t, 0 ≤ h t)
    (hb : ∀ w : ℂ, h ‖w - c‖ ≤ pointConformalDensity a y w) :
    (∫ t in (0 : ℝ)..‖z - c‖, h t) ≤ (pointSmoothConformalEDist a y c z).toReal := by
  apply le_of_tendsto (radialMask_integral_tendsto h hc hn (norm_nonneg _))
  filter_upwards [] with n
  let H : ℝ → ℝ := fun t => radialMask n t * h t
  have hH : Continuous H := (radialMask_continuous n).mul hc
  have hHn : ∀ t, 0 ≤ H t := fun t => mul_nonneg (radialMask_bounds n t).1 (hn t)
  have hHle : ∀ t, H t ≤ h t := fun t => mul_le_of_le_one_left (hn t) (radialMask_bounds n t).2
  have hε : 0 < 1 / (n + 1 : ℝ) := by positivity
  have hHz : ∀ t ∈ Icc (0 : ℝ) (1 / (n + 1 : ℝ)), H t = 0 := by
    intro t ht
    change radialMask n t * h t = 0
    rw [radialMask_zero n ht, zero_mul]
  have hφ := radialPrimitive_contDiff hH hε hHz c
  have hgrad : ∀ w, ‖fderiv ℝ (radialPrimitive H c) w‖ ≤ 1 * pointConformalDensity a y w := by
    intro w
    rw [one_mul]
    exact (radialPrimitive_fderiv_le hH hHn hε hHz c w).trans ((hHle _).trans (hb w))
  have hbar := pointConformal_metric_barrier a y hφ (by norm_num : (0 : ℝ) < 1) hgrad c z
  simp only [ENNReal.ofReal_one, one_mul] at hbar
  have hr := ENNReal.toReal_mono (pointSmoothConformalEDist_lt_top ha y c z).ne hbar
  have hcenter : radialPrimitive H c c = 0 := by simp [radialPrimitive]
  rw [hcenter, sub_zero] at hr
  have habs : |radialPrimitive H c z| ≤ (pointSmoothConformalEDist a y c z).toReal := by
    change ‖radialPrimitive H c z‖ ≤ _ at hr
    simpa only [Real.norm_eq_abs] using hr
  exact (le_abs_self (radialPrimitive H c z)).trans habs

theorem pointConformalEDist_uniform_radial_lower {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c z : ℂ) (hz : z ≠ c) :
    Real.exp (-2 * ∑ j, a j) * ‖z - c‖ *
      (∏ j, (‖z - c‖ + ‖y j - c‖) ^ (a j / 2)) ≤
      (pointSmoothConformalEDist a y c z).toReal := by
  exact (pointRadialDensity_integral_lower ha y c (norm_pos_iff.mpr (sub_ne_zero.mpr hz))).trans
    (radial_integral_le_pointConformalEDist ha y c z (pointRadialDensity a y c)
      (pointRadialDensity_continuous ha y c) (pointRadialDensity_nonneg a y c)
      (pointRadialDensity_le ha y c))

end RepulsiveCoulomb
