import LeanResearch.RepulsiveCoulomb.CoulombExponentialQuadraticMoment
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchVariational

/-! Records-only uncompiled adapter. Finite relative entropy against the actual
normalized Coulomb law implies a genuine competitor quadratic moment. -/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem coulomb_finite_entropy_quadratic_moment {N : ℕ} {β : ℝ}
    (hβ : 0 < β) {Q : Measure (CoulombConfig N)} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure N β) ≠ ∞) :
    Integrable (fun z : CoulombConfig N => ‖z‖ ^ 2) Q ∧
      (β / 8) * (∫ z : CoulombConfig N, ‖z‖ ^ 2 ∂Q) ≤
        (klDiv Q (coulombMeasure N β)).toReal +
          Real.log (∫ z : CoulombConfig N, Real.exp ((β / 8) * ‖z‖ ^ 2)
            ∂coulombMeasure N β) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  exact conditionalEntropyBranch_scaled_moment hKL
    (continuous_norm.pow 2).measurable (fun z => sq_nonneg ‖z‖)
    (by positivity : 0 < β / 8) (coulombMeasure_exp_quadratic_integrable hβ)

end RepulsiveCoulomb
