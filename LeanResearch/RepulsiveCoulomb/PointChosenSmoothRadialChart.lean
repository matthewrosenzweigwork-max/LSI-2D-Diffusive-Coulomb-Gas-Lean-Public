module

public import LeanResearch.RepulsiveCoulomb.PointSmoothRadialChartGerms

@[expose] public section

/-! Choose a chart once per physical vertex. Incident gaps then use the same
literal holomorphic chart, instead of incompatible independent existential
choices. The data are constructed from the proved actual metric chart theorem. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def pointChosenSmoothRadialChart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) : OpenPartialHomeomorph ℂ ℂ :=
  Classical.choose (exists_pointConformal_smooth_radial_germ_chart ha y p)

theorem pointChosenSmoothRadialChart_spec {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    let e := pointChosenSmoothRadialChart ha y p
    ∃ R : ℝ, 0 < R ∧ e p = 0 ∧ p ∈ e.source ∧
      AnalyticOnNhd ℂ e.symm e.target ∧
      (∀ z ∈ e.source, AnalyticAt ℂ e z ∧ deriv e z ≠ 0) ∧
      ∀ z : ℂ, (pointSmoothConformalEDist a y z p).toReal ≤ R → z ≠ p →
        ∀ γ : Icc (0 : ℝ) 1 → ℂ,
          γ ⟨0, by norm_num⟩ = p → γ ⟨1, by norm_num⟩ = z →
          (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
            |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal) →
          ∃ η : ℝ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) η ∧
            InjOn η (Icc (0 : ℝ) 1) ∧
            (∀ s ∈ Icc (0 : ℝ) 1, deriv η s ≠ 0) ∧
            η 0 = p ∧ η 1 = z ∧
            (∀ s ∈ Icc (0 : ℝ) 1, η =ᶠ[𝓝 s] (fun u : ℝ => e.symm (u • e z))) ∧
            (∀ t : Icc (0 : ℝ) 1,
              γ t = η (t.1 ^ (coalescedPointExponent a y p / 2 + 1)⁻¹)) ∧
            range γ = η '' Icc (0 : ℝ) 1 := by
  obtain ⟨R, hR, hep, hinv, he, hsource, _, hcollar⟩ :=
    Classical.choose_spec (exists_pointConformal_smooth_radial_germ_chart ha y p)
  refine ⟨R, hR, hep, ?_, hinv, he, hcollar⟩
  apply hsource
  rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
  exact hR.le

end RepulsiveCoulomb
