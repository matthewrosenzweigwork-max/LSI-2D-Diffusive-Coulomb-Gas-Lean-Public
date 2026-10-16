import LeanResearch.RepulsiveCoulomb.CoulombOneSiteDisintegration
import Mathlib.Probability.Kernel.Defs

/-! Actual measurable probability kernel for the first coordinate, with
configuration- and particle-number-uniform full-domain PI/LSI. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open PeriodicAttractiveLogGas
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

def coulombOneSiteExponents (N : ℕ) (β : ℝ) : Fin N → ℝ :=
  fun _ => β / ((N + 1 : ℕ) : ℝ)

theorem coulombOneSiteExponents_nonneg (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    ∀ j, 0 ≤ coulombOneSiteExponents N β j := fun _ => div_nonneg hβ (Nat.cast_nonneg _)

def coulombOneSiteKernel (N : ℕ) (β : ℝ) (hβ : 0 < β) : Kernel (CoulombConfig N) ℂ where
  toFun y := pointMeasure β (coulombOneSiteExponents N β) (fun j => y j)
  measurable' := pointMeasure_measurable_config β (coulombOneSiteExponents_nonneg N hβ.le)

theorem coulombOneSiteKernel_apply (N : ℕ) (β : ℝ) (hβ : 0 < β) (y : CoulombConfig N) :
    coulombOneSiteKernel N β hβ y = pointMeasure β (coulombOneSiteExponents N β) (fun j => y j) := rfl

instance coulombOneSiteKernel_isMarkov (N : ℕ) (β : ℝ) (hβ : 0 < β) :
    IsMarkovKernel (coulombOneSiteKernel N β hβ) where
  isProbabilityMeasure y := pointMeasure_isProbability hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j)

theorem coulomb_one_site_kernel_tower {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : CoulombConfig (N + 1) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ z, F z ∂coulombMeasure (N + 1) β) =
      ∫⁻ y : CoulombConfig N, (∫⁻ w : ℂ, F (coulombInsertZero w y) ∂coulombOneSiteKernel N β hβ y)
        ∂coulombOneSiteMarginal N β := coulomb_one_site_tower hβ hF

theorem coulomb_one_site_uniform_functional_inequalities {β : ℝ} (hβ : 0 < β) :
    ∃ C ρ : ℝ, 0 < C ∧ 0 < ρ ∧ ∀ (N : ℕ) (y : CoulombConfig N),
      ∀ u : PointFormDomain hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j),
      variance (pointFormValueL hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u : ℂ → ℝ)
        (coulombOneSiteKernel N β hβ y) ≤
        C * (∫ w, ‖pointFormGradientL hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u w‖ ^ 2
          ∂coulombOneSiteKernel N β hβ y) ∧
      entropy (coulombOneSiteKernel N β hβ y)
        (fun w => (pointFormValueL hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u w) ^ 2) ≤
        (((2 / ρ) * (∫ w, ‖pointFormGradientL hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j) u w‖ ^ 2
          ∂coulombOneSiteKernel N β hβ y) : ℝ) : EReal) := by
  obtain ⟨C, ρ, hC, hρ, hb⟩ := planar_weighted_gaussian_inequalities (Q := β) hβ
  refine ⟨C, ρ, hC, hρ, ?_⟩
  intro N y u
  exact hb N (coulombOneSiteExponents N β) (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j)
    (coulomb_one_site_exponent_sum_lt N hβ).le u

end RepulsiveCoulomb
