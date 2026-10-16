import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchGibbsFactorization
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchUniformGibbsDefect

/-! Compact upper bound for the exact finite-particle defects. The four finite
Gibbs factorization declarations are supplied by GibbsFactorization under their
unchanged public names. Records-only split candidate, not staged or checked. -/
noncomputable section
open MeasureTheory InformationTheory Real
open scoped BigOperators
namespace RepulsiveCoulomb

/-- The exact finite-particle defects have a common finite upper bound over
all N>=2 and every beta in a compact positive interval. -/
theorem conditionalEntropyBranch_defect_compact_upper {βlo βhi ell : ℝ}
    (hlo : 0 < βlo) (hord : βlo ≤ βhi) (hell : 1 < ell) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ β (hβlo : βlo ≤ β) (hβhi : β ≤ βhi)
      (R : EquilibriumConstructedReference β), ∀ N : ℕ, 2 ≤ N →
      conditionalEntropyBranchDefect (N := N) R ell ≤ D := by
  obtain ⟨D, hD, hb⟩ := equilibriumGibbsDefect_compact_upper hlo hord (zero_lt_one.trans hell)
  refine ⟨D, hD, ?_⟩
  intro β hβlo hβhi R N hN
  simpa only [conditionalEntropyBranchDefect, conditionalEntropyBranchThermalB,
    equilibriumGibbsDefectMoment, equilibriumDefectEnergy, div_eq_mul_inv, mul_comm] using
      hb β hβlo hβhi R N hN

end RepulsiveCoulomb
