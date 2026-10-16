import LeanResearch.RepulsiveCoulomb.HolomorphicRadialAverage

/-! A local analytic logarithm constructed by normalizing the value at the center
and using the principal logarithm near 1. No global branch is presumed. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_holomorphic_log_on_subball {A : ℂ → ℂ} {p : ℂ} {R : ℝ}
    (hR : 0 < R) (hA : AnalyticOnNhd ℂ A (ball p R)) (hA0 : A p ≠ 0) :
    ∃ r : ℝ, 0 < r ∧ ball p r ⊆ ball p R ∧ ∃ L : ℂ → ℂ,
      AnalyticOnNhd ℂ L (ball p r) ∧ ∀ z ∈ ball p r, Complex.exp (L z) = A z := by
  have hc : ContinuousAt (fun z ↦ A z / A p) p :=
    (hA p (mem_ball_self hR)).continuousAt.div_const (A p)
  have hslit : A p / A p ∈ Complex.slitPlane := by simp [hA0]
  have he : ∀ᶠ z in 𝓝 p, A z / A p ∈ Complex.slitPlane :=
    hc.preimage_mem_nhds (Complex.isOpen_slitPlane.mem_nhds hslit)
  have hboth : {z | z ∈ ball p R ∧ A z / A p ∈ Complex.slitPlane} ∈ 𝓝 p :=
    inter_mem (ball_mem_nhds p hR) he
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hboth
  let L : ℂ → ℂ := fun z ↦ Complex.log (A z / A p) + Complex.log (A p)
  refine ⟨r, hr, (fun z hz ↦ (hsub hz).1), L, ?_, ?_⟩
  · intro z hz
    exact (((hA z (hsub hz).1).div_const).clog (hsub hz).2).add analyticAt_const
  · intro z hz
    dsimp [L]
    rw [Complex.exp_add, Complex.exp_log (Complex.slitPlane_ne_zero (hsub hz).2),
      Complex.exp_log hA0, div_mul_cancel₀ _ hA0]

end RepulsiveCoulomb
