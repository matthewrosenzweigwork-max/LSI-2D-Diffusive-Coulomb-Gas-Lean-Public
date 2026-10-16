module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchFactorization
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGibbsDefectMoment
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGibbsEnergyIntegrability

@[expose] public section

/-!
Actual finite-entropy factorization and defect nonnegativity, using the genuine
finite Gibbs exponential moments and energy integrability. This module does
not import the uniform-partition or compact-defect chain. Its four declarations
are copied unchanged from the preserved CompleteFactorization draft.
Records-only split candidate, not staged or checked.
-/
noncomputable section
open MeasureTheory InformationTheory Real
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_B_gibbs_integrable {N : ℕ} {β : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (R : EquilibriumConstructedReference β) :
    Integrable (conditionalEntropyBranchThermalB R) (coulombMeasure N β) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  have hA := equilibriumReference_physical_gibbs_energy_integrable hβ R hN
  have hQ2 := (coulomb_finite_entropy_quadratic_moment hβ
    (Q := coulombMeasure N β) (by simp)).1
  exact hA.add ((conditionalEntropyBranch_thermal_sum_integrable R hQ2).div_const (N : ℝ))

theorem conditionalEntropyBranch_defect_exp_integrable {N : ℕ} {β ell : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (hell : 0 < ell) (R : EquilibriumConstructedReference β) :
    Integrable (fun z : CoulombConfig N => Real.exp (-ell * β * conditionalEntropyBranchThermalB R z))
      (coulombMeasure N β) :=
  (equilibriumReference_physical_gibbs_defect_moment hβ hell R hN).1

/-- The finite-entropy proposition's exact displayed inequality, without an
assumed exponential moment, abstract conditional law, or tensorization input. -/
theorem conditionalEntropyBranch_entropy_factorization {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q)
    {ell : ℝ} (hell : 1 < ell) :
    (1 - 1 / ell) * (klDiv Q (coulombMeasure (N + 1) β)).toReal -
      Real.log (equilibriumReferencePartition (N + 1) β R) -
      (1 / ell) * Real.log (∫ z : CoulombConfig (N + 1),
        Real.exp (-ell * β * conditionalEntropyBranchThermalB R z) ∂coulombMeasure (N + 1) β) ≤
      (conditionalEntropyBranchCoulombS hβ Q).toReal :=
  conditionalEntropyBranch_factorization_of_exp_integrable hβ R hKL hB hell
    (conditionalEntropyBranch_defect_exp_integrable (Nat.succ_pos N) hβ (zero_lt_one.trans hell) R)

theorem conditionalEntropyBranch_defect_nonneg {N : ℕ} {β ell : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (hell : 1 < ell) (R : EquilibriumConstructedReference β) :
    0 ≤ conditionalEntropyBranchDefect (N := N) R ell := by
  cases N with
  | zero => omega
  | succ N =>
      exact conditionalEntropyBranch_defect_nonneg_of_integrable hβ R
        (conditionalEntropyBranch_B_gibbs_integrable hN hβ R) hell
        (conditionalEntropyBranch_defect_exp_integrable hN hβ (zero_lt_one.trans hell) R)

end RepulsiveCoulomb
