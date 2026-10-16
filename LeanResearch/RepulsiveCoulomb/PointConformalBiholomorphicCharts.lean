module

public import LeanResearch.RepulsiveCoulomb.HolomorphicChartRestriction

@[expose] public section

/-! Regular and singular density charts with actual holomorphic inverses.
These interfaces permit smooth paths to be transported in both directions. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_pointConformal_flat_chart_with_inverse {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ} (hp : p ∉ pointPunctures a y) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e p = 0 ∧
      e.source ⊆ (pointPunctures a y)ᶜ ∧ AnalyticOnNhd ℂ e.symm e.target ∧
      ∀ z ∈ e.source, AnalyticAt ℂ e z ∧ ‖deriv e z‖ = pointConformalDensity a y z ∧ deriv e z ≠ 0 := by
  obtain ⟨e, hep, he0, hsub, he⟩ := exists_pointConformal_holomorphic_chart ha y hp
  exact ⟨e, hep, he0, hsub,
    holomorphic_chart_inverse_analytic e (fun z hz ↦ (he z hz).1) (fun z hz ↦ (he z hz).2.2), he⟩

theorem exists_pointConformal_cone_chart_with_inverse {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, p ∈ e.source ∧ e p = 0 ∧
      AnalyticOnNhd ℂ e.symm e.target ∧ ∀ z ∈ e.source,
        AnalyticAt ℂ e z ∧ deriv e z ≠ 0 ∧
        ‖e z‖ ^ (coalescedPointExponent a y p / 2) * ‖deriv e z‖ = pointConformalDensity a y z := by
  obtain ⟨r, hr, g, hg, hg0, hfac⟩ := exists_pointConformal_holomorphic_puncture_factor ha y p
  obtain ⟨e, hep, he0, hdp, hball, he⟩ := exists_holomorphic_cone_coordinate_with_deriv
    (α := coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) p hr hg
    (hg0 p (mem_ball_self hr))
  obtain ⟨e', hep', hsub, hefun, hd'⟩ := exists_nonsingular_chart_restriction e hep (he p hep).1 hdp
  have ha' : ∀ z ∈ e'.source, AnalyticAt ℂ e' z := by
    intro z hz
    rw [hefun]
    exact (he z (hsub hz)).1
  have h0' : e' p = 0 := by rw [hefun]; exact he0
  refine ⟨e', hep', h0', holomorphic_chart_inverse_analytic e' ha' hd', ?_⟩
  intro z hz
  refine ⟨ha' z hz, hd' z hz, ?_⟩
  rw [hefun]
  exact (he z (hsub hz)).2.trans (hfac z (hball (hsub hz))).symm

end RepulsiveCoulomb
