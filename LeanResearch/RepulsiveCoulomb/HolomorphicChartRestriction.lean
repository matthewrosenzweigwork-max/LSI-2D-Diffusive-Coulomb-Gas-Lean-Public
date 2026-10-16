import LeanResearch.RepulsiveCoulomb.PointConeSectorMap

/-! Nonsingular restrictions and analytic inverses of the actual local charts. -/
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem exists_nonsingular_chart_restriction (e : OpenPartialHomeomorph ℂ ℂ) {p : ℂ}
    (hp : p ∈ e.source) (ha : AnalyticAt ℂ e p) (hd : deriv e p ≠ 0) :
    ∃ e' : OpenPartialHomeomorph ℂ ℂ, p ∈ e'.source ∧ e'.source ⊆ e.source ∧
      (e' : ℂ → ℂ) = e ∧ ∀ z ∈ e'.source, deriv e' z ≠ 0 := by
  have hevent : ∀ᶠ z in 𝓝 p, deriv e z ≠ 0 :=
    ha.deriv.continuousAt.preimage_mem_nhds
      (isClosed_singleton.isOpen_compl.mem_nhds hd)
  have hboth : {z | z ∈ e.source ∧ deriv e z ≠ 0} ∈ 𝓝 p :=
    inter_mem (e.open_source.mem_nhds hp) hevent
  obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hboth
  let e' := e.restrOpen (ball p r) isOpen_ball
  refine ⟨e', ⟨hp, mem_ball_self hr⟩, (fun _ hz ↦ hz.1), rfl, ?_⟩
  intro z hz
  exact (hsub hz.2).2

theorem holomorphic_chart_inverse_analytic (e : OpenPartialHomeomorph ℂ ℂ)
    (ha : ∀ z ∈ e.source, AnalyticAt ℂ e z)
    (hd : ∀ z ∈ e.source, deriv e z ≠ 0) : AnalyticOnNhd ℂ e.symm e.target := by
  apply DifferentiableOn.analyticOnNhd _ e.open_target
  intro w hw
  have hp : e.symm w ∈ e.source := e.map_target hw
  have hc : ContDiffAt ℂ 1 e (e.symm w) := (ha _ hp).contDiffAt
  have hs := (hc.hasStrictDerivAt one_ne_zero).to_local_left_inverse
    (hd _ hp) (e.eventually_left_inverse hp)
  have hi : DifferentiableAt ℂ e.symm w := by
    simpa only [e.right_inv hw] using hs.hasDerivAt.differentiableAt
  exact hi.differentiableWithinAt

end RepulsiveCoulomb
