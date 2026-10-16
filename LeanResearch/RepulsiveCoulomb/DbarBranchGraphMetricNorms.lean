module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCovectorMetric
public import LeanResearch.RepulsiveCoulomb.DbarBranchGraphMetricSquareRoot

@[expose] public section

/-! Pointwise norm comparisons for the auxiliary metric. They distinguish
its H^{-1} one-form norm from the Euclidean norm controlled by curvature.
No global coercive estimate or equality of operator domains is asserted. -/
noncomputable section
open InnerProductSpace
namespace RepulsiveCoulomb

theorem dbarCovectorMetricRoot_lower {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) (v : CoulombConfig N) :
    ‖v‖ ≤ ‖dbarGraphMetricRoot (dbarCovectorRiesz A) v‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [dbarGraphMetricRoot_norm_sq, ← dbarCovectorMetric_eq_rankOne]
  exact dbarCovectorMetric_lower A v

theorem dbarCovectorMetricInverseRoot_contraction {N : ℕ}
    (A : CoulombConfig N →L[ℂ] ℂ) (v : CoulombConfig N) :
    ‖dbarGraphMetricInverseRoot (dbarCovectorRiesz A) v‖ ≤ ‖v‖ := by
  have h := dbarCovectorMetricRoot_lower A (dbarGraphMetricInverseRoot (dbarCovectorRiesz A) v)
  have he := congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L v)
    (dbarGraphMetricRoot_inverseRoot (dbarCovectorRiesz A))
  change dbarGraphMetricRoot (dbarCovectorRiesz A)
    (dbarGraphMetricInverseRoot (dbarCovectorRiesz A) v) = v at he
  rw [he] at h
  exact h

theorem dbarCovectorMetricInverse_norm_le_auxiliary {N : ℕ}
    (A : CoulombConfig N →L[ℂ] ℂ) (v : CoulombConfig N) :
    ‖dbarCovectorMetricInverse A v‖ ≤ ‖dbarGraphMetricInverseRoot (dbarCovectorRiesz A) v‖ := by
  have h := dbarCovectorMetricInverseRoot_contraction A
    (dbarGraphMetricInverseRoot (dbarCovectorRiesz A) v)
  have he := congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L v)
    (dbarGraphMetricInverseRoot_square (dbarCovectorRiesz A))
  change dbarGraphMetricInverseRoot (dbarCovectorRiesz A)
    (dbarGraphMetricInverseRoot (dbarCovectorRiesz A) v) = dbarCovectorMetricInverse A v at he
  rw [he] at h
  exact h

theorem dbarCovectorMetric_pointwise_dual_bound {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (A : CoulombConfig N →L[ℂ] ℂ) (α g : CoulombConfig N) :
    ‖inner ℂ α (dbarCovectorMetricInverse A g)‖ ^ 2 ≤
      (2 / β) * ‖α‖ ^ 2 * ((β / 2) * ‖dbarCovectorMetricInverse A g‖ ^ 2) := by
  have h := pow_le_pow_left₀ (norm_nonneg (inner ℂ α (dbarCovectorMetricInverse A g)))
    (norm_inner_le_norm α (dbarCovectorMetricInverse A g)) 2
  rw [mul_pow] at h
  calc
    _ ≤ ‖α‖ ^ 2 * ‖dbarCovectorMetricInverse A g‖ ^ 2 := h
    _ = _ := by field_simp [hβ.ne']

end RepulsiveCoulomb
