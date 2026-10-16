module

public import LeanResearch.RepulsiveCoulomb.PointRegularPowerConeChart

@[expose] public section

/-! Ordinary smooth regular arcs obtained by taking a straight radial segment
through a biholomorphic chart. This concerns Euclidean parametrization, including
its endpoints, rather than the possibly singular metric-speed parametrization. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem holomorphic_radial_arc_regular (e : OpenPartialHomeomorph ℂ ℂ)
    (ha : ∀ z ∈ e.source, AnalyticAt ℂ e z ∧ deriv e z ≠ 0)
    (hi : AnalyticOnNhd ℂ e.symm e.target) {w : ℂ} (hw : w ≠ 0)
    (htarget : ∀ s ∈ Icc (0 : ℝ) 1, s • w ∈ e.target) :
    AnalyticOnNhd ℝ (fun s : ℝ => e.symm (s • w)) (Icc (0 : ℝ) 1) ∧
    (∀ s ∈ Icc (0 : ℝ) 1, deriv (fun t : ℝ => e.symm (t • w)) s ≠ 0) ∧
    InjOn (fun s : ℝ => e.symm (s • w)) (Icc (0 : ℝ) 1) := by
  have hA : AnalyticOnNhd ℝ (fun s : ℝ => e.symm (s • w)) (Icc (0 : ℝ) 1) := by
    intro s hs
    exact ((hi _ (htarget s hs)).restrictScalars (𝕜 := ℝ)).comp
      (f := fun t : ℝ => t • w) (analyticAt_id.smul analyticAt_const)
  refine ⟨hA, ?_, ?_⟩
  · intro s hs
    have hT := htarget s hs
    have hS := e.map_target hT
    have hI := e.hasDerivAt_symm hT (ha _ hS).2 (ha _ hS).1.differentiableAt.hasDerivAt
    have hd : deriv (fun t : ℝ => e.symm (t • w)) s = w * (deriv e (e.symm (s • w)))⁻¹ := by
      have hl : DifferentiableAt ℝ (fun t : ℝ => t • w) s := differentiableAt_id.smul_const w
      change deriv ((e.symm : ℂ → ℂ) ∘ (fun t : ℝ => t • w)) s = _
      rw [fderiv_comp_deriv s (hI.differentiableAt.restrictScalars ℝ) hl,
        hI.differentiableAt.fderiv_restrictScalars (𝕜 := ℝ)]
      change fderiv ℂ e.symm (s • w) (deriv (fun t : ℝ => t • w) s) = _
      have hlD : HasDerivAt (fun t : ℝ => t • w) w s := by
        simpa only [id_eq, one_smul] using (hasDerivAt_id s).smul_const w
      rw [fderiv_eq_smul_deriv, hI.deriv, hlD.deriv]
      rfl
    rw [hd]
    exact mul_ne_zero hw (inv_ne_zero (ha _ hS).2)
  · intro s hs t ht h
    have heq : s • w = t • w := e.symm.injOn (htarget s hs) (htarget t ht) h
    exact (smul_left_injective ℝ hw) heq

end RepulsiveCoulomb
