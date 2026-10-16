module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoulombLower

@[expose] public section

/-!
Scalar variational assembly of the actual conditional-entropy inequality.
The exponential-moment input is explicitly exposed at this modular boundary;
the separate equilibrium/partition adapter must discharge it before the
unconditional manuscript proposition or compact defect bound is claimed.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

def conditionalEntropyBranchDefect {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (ell : ℝ) : ℝ :=
  Real.log (equilibriumReferencePartition N β R) +
    Real.log (∫ z : CoulombConfig N,
      Real.exp (-ell * β * conditionalEntropyBranchThermalB R z) ∂coulombMeasure N β) / ell

theorem conditionalEntropyBranch_factorization_of_exp_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q)
    {ell : ℝ} (hell : 1 < ell)
    (hExp : Integrable (fun z : CoulombConfig (N + 1) =>
      Real.exp (-ell * β * conditionalEntropyBranchThermalB R z)) (coulombMeasure (N + 1) β)) :
    (1 - 1 / ell) * (klDiv Q (coulombMeasure (N + 1) β)).toReal -
      Real.log (equilibriumReferencePartition (N + 1) β R) -
      (1 / ell) * Real.log (∫ z : CoulombConfig (N + 1),
        Real.exp (-ell * β * conditionalEntropyBranchThermalB R z) ∂coulombMeasure (N + 1) β) ≤
      (conditionalEntropyBranchCoulombS hβ Q).toReal := by
  letI := coulombMeasure_isProbability (N := N + 1) hβ
  have hlow := conditionalEntropyBranch_coulomb_pre_variational_lower hβ R hKL hB
  have hvar := conditionalEntropyBranch_negative_test hKL hB (zero_lt_one.trans hell) hExp
  simp only [div_eq_mul_inv, one_mul] at hvar ⊢
  nlinarith [hlow, hvar]

theorem conditionalEntropyBranch_factorization_defect_of_exp_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q)
    {ell : ℝ} (hell : 1 < ell)
    (hExp : Integrable (fun z : CoulombConfig (N + 1) =>
      Real.exp (-ell * β * conditionalEntropyBranchThermalB R z)) (coulombMeasure (N + 1) β)) :
    (1 - 1 / ell) * (klDiv Q (coulombMeasure (N + 1) β)).toReal -
      conditionalEntropyBranchDefect (N := N + 1) R ell ≤
        (conditionalEntropyBranchCoulombS hβ Q).toReal := by
  have h := conditionalEntropyBranch_factorization_of_exp_integrable hβ R hKL hB hell hExp
  unfold conditionalEntropyBranchDefect
  convert h using 1 <;> ring

theorem conditionalEntropyBranch_coulomb_site_self {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (i : Fin (N + 1)) :
    conditionalEntropyBranchCoulombSiteCost hβ (coulombMeasure (N + 1) β) i = 0 := by
  letI := coulombOneSiteMarginal_isProbability (N := N) hβ
  unfold conditionalEntropyBranchCoulombSiteCost
  rw [conditionalEntropyBranch_coulomb_chart_law hβ i, Measure.fst_compProd, klDiv_self]

/-- Q=P is used only after actual B-integrability is supplied. This is the
correct zero-cost argument for nonnegative defect, without assuming K>=1. -/
theorem conditionalEntropyBranch_defect_nonneg_of_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    (hB : Integrable (conditionalEntropyBranchThermalB R) (coulombMeasure (N + 1) β))
    {ell : ℝ} (hell : 1 < ell)
    (hExp : Integrable (fun z : CoulombConfig (N + 1) =>
      Real.exp (-ell * β * conditionalEntropyBranchThermalB R z)) (coulombMeasure (N + 1) β)) :
    0 ≤ conditionalEntropyBranchDefect (N := N + 1) R ell := by
  letI := coulombMeasure_isProbability (N := N + 1) hβ
  have hself : conditionalEntropyBranchCoulombS hβ (coulombMeasure (N + 1) β) = 0 := by
    simp only [conditionalEntropyBranchCoulombS_eq_sum, conditionalEntropyBranch_coulomb_site_self,
      Finset.sum_const_zero]
  have h := conditionalEntropyBranch_factorization_defect_of_exp_integrable
    hβ R (Q := coulombMeasure (N + 1) β) (by simp) hB hell hExp
  rw [klDiv_self, ENNReal.toReal_zero, mul_zero, zero_sub, hself, ENNReal.toReal_zero] at h
  linarith

end RepulsiveCoulomb
