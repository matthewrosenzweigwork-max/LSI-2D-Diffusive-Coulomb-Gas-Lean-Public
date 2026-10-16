module

public import LeanResearch.RepulsiveCoulomb.MetricGeodesicRay

@[expose] public section

/-! Unboundedness and genuine unit-speed rays in the literal point-density metric. -/
noncomputable section
open Set
open scoped NNReal
namespace RepulsiveCoulomb

theorem pointConformal_metric_unbounded {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ) (R : ℝ) :
    ∃ z : ℂ, R < (pointSmoothConformalEDist a y x z).toReal := by
  obtain ⟨C, hC, hb⟩ := pointConformal_radial_bound ha y
  let M := 2 * pointConformalRadius y + ‖x‖ + C * max R 0 + 1
  have hM : 0 < M := by
    have := pointConformalRadius_pos y
    have := norm_nonneg x
    have := mul_nonneg hC.le (le_max_right R 0)
    dsimp [M]
    linarith
  refine ⟨(M : ℂ), ?_⟩
  have h := hb x (M : ℂ)
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM] at h
  dsimp only [M] at h
  have hR := le_max_left R 0
  nlinarith

theorem exists_pointConformal_ray {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ) :
    ∃ γ : ℝ≥0 → ℂ, γ 0 = x ∧ Continuous γ ∧
      ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t := by
  have hgeo : ∀ z : ℂ, ∃ γ : Icc (0 : ℝ) 1 → ℂ,
      γ ⟨0, by norm_num⟩ = x ∧
      ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal := by
    intro z
    obtain ⟨γ, h0, _, _, hd⟩ := exists_pointConformal_geodesic ha y x z
    exact ⟨γ, h0, hd⟩
  obtain ⟨γ, hi, h0⟩ := @exists_metric_ray_of_unbounded_geodesics ℂ
    (pointSmoothConformalMetricSpace ha y) (pointSmoothConformalMetricSpace_proper ha y)
    x (pointConformal_metric_unbounded ha y x) hgeo
  have hc := @Isometry.continuous ℝ≥0 ℂ _
    (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace γ hi
  change @Continuous ℝ≥0 ℂ _ (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ at hc
  rw [pointSmoothConformalMetricSpace_topology ha y] at hc
  exact ⟨γ, h0, hc, @Isometry.dist_eq ℝ≥0 ℂ _
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace γ hi⟩

end RepulsiveCoulomb
