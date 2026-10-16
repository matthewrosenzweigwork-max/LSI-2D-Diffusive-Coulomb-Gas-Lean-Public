module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryWeightedApproximation

@[expose] public section

/-! The exact curvature-weighted estimate on the genuine auxiliary adjoint
restricted to the closed compatibility space. First pass a common local
mollifier sequence at fixed cutoff radius, then let the radius grow. The
controlled norm is that of R*u, not the full auxiliary norm of u. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology LinearPMap
namespace RepulsiveCoulomb

theorem coulombAuxiliary_cutoff_basic_estimate {N : ℕ} {β R : ℝ}
    (hβ : 0 < β) (hR : 0 < R)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    (β / 2) * ‖coulombInverseRootL2L N β (coulombMetricCutoffL2L hR (CoulombConfig N) u)‖ ^ 2 ≤
      ‖coulombAuxiliaryCutoffScalar hR u h‖ ^ 2 + ‖coulombCutoffExteriorError β hR u‖ ^ 2 := by
  obtain ⟨ψ, hvalue, hadjoint, hexterior⟩ := coulombAuxiliaryCutoff_joint_core_approximation hβ hR huh hu
  exact coulombAuxiliaryCore_basic_estimate_of_joint_limit hβ ψ _ _ _ hvalue hadjoint hexterior

theorem coulombAuxiliary_adjoint_basic_estimate {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (hu : u ∈ coulombAuxiliaryCompatibility N hβ) :
    (β / 2) * ‖coulombInverseRootL2L N β u‖ ^ 2 ≤ ‖h‖ ^ 2 := by
  have hv := coulombMetricCutoffL2L_tendsto hβ u
  have hR := ((coulombInverseRootL2L N β).continuous.tendsto u).comp hv
  have hh := (coulombAuxiliaryDbarAdjoint_cutoff_tendsto hβ u h).snd_nhds
  have he := coulombCutoffExteriorError_tendsto_zero hβ u
  have hleft := (hR.norm.pow 2).const_mul (β / 2)
  have hright := (hh.norm.pow 2).add (he.norm.pow 2)
  have hle := le_of_tendsto_of_tendsto hleft hright
    (Eventually.of_forall fun n : ℕ =>
      coulombAuxiliary_cutoff_basic_estimate hβ (by positivity : 0 < (n : ℝ) + 1) huh hu)
  simpa only [norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] using hle

end RepulsiveCoulomb
