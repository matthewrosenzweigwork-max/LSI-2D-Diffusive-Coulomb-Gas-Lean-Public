module

public import LeanResearch.RepulsiveCoulomb.MetricMidpointGeodesic

@[expose] public section

/-! Actual geodesics for every admissible point configuration. Completeness and
midpoints are proved inputs, not hypotheses left to the caller. Continuity below
is in the original Euclidean topology. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem exists_pointConformal_geodesic {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    ∃ γ : Icc (0 : ℝ) 1 → ℂ,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y x z).toReal := by
  obtain ⟨γ, h0, h1, hc, hd⟩ := @exists_geodesic_of_exact_midpoints ℂ
    (pointSmoothConformalMetricSpace ha y) (pointSmoothConformalMetricSpace_complete ha y)
    (exists_pointConformal_midpoint ha y) x z
  have hc' : Continuous γ := by
    change @Continuous (Icc (0 : ℝ) 1) ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ at hc
    rwa [pointSmoothConformalMetricSpace_topology ha y] at hc
  exact ⟨γ, h0, h1, hc', hd⟩

end RepulsiveCoulomb
