import LeanResearch.RepulsiveCoulomb.PaperRoute.ReferenceGibbsMomentFromPartition
import LeanResearch.RepulsiveCoulomb.PaperRoute.ResolventLabeledPoincare
import LeanResearch.RepulsiveCoulomb.CoulombFormTightening

/-! Additive experimental source; verification is recorded separately in evidence. Concrete full-domain Rothaus assembly
from the NEW labeled PI and NEW weighted one-site rate. Thermal physical data
and their actual uniform partition/exponential-moment bounds remain explicit.
This is not an original-input main-theorem claim while those gates are open. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb.PaperRoute

def paperLabeledRateFromReference {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) : ℝ :=
  assembledRate (paperOneSiteRate β) (paperUniformEntropyDefect R)
    (poleBranchSymmetricPoincareConstant hβ) (paperCrel β)

theorem paperLabeledRateFromReference_pos {β C M : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β)
    (hK : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N β R ≤ C)
    (hM : ∀ N : ℕ, 2 ≤ N → paperGibbsEntropyMoment R N ≤ M) :
    0 < paperLabeledRateFromReference hβ R :=
  assembledRate_pos (paperOneSiteRate_pos hβ)
    (paper_uniform_defect_nonneg hβ R hK hM)
    (poleBranchSymmetricPoincareConstant_pos hβ).le (paperCrel_pos hβ).le

/-- The actual centered original-domain representative and actual new full
labeled PI are used by Rothaus. The remaining inputs are physical data and
explicit integral bounds, not an assumed defective/tight LSI certificate. -/
theorem paper_full_labeled_lsi_of_reference_bounds {β C M : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β)
    (hK : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N β R ≤ C)
    (hM : ∀ N : ℕ, 2 ≤ N → paperGibbsEntropyMoment R N ≤ M)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
      (((2 / paperLabeledRateFromReference hβ R) * coulombFormEnergy N hβ u : ℝ) : EReal) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  have hD := paper_uniform_defect_nonneg hβ R hK hM
  have h := coulomb_form_tightening hβ
    (show 0 ≤ 2 * paperUniformEntropyDefect R + 2 by positivity)
    (fun v => paper_full_labeled_poincare_via_resolvent hβ (n + 2) (by omega) v)
    (fun v => paper_full_defective_of_reference_bounds hβ R hK hM (n + 2) (by omega) v) u
  have he := two_div_assembledRate (paperOneSiteRate_pos hβ) hD
    (poleBranchSymmetricPoincareConstant_pos hβ).le (paperCrel_pos hβ).le
  simpa only [paperLabeledRateFromReference, he] using h


/-- Physical-data and partition-bound version of the pending main assembly.
The input reference and fixed-to-lower-coupling partition bounds still await
new thermal and DG/Holder producers; no original-input theorem is claimed. -/
theorem paper_full_labeled_lsi_of_partition_bounds {β C₁ C₆ : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (hC₆ : 0 < C₆)
    (hPart₁ : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N β R ≤ C₁)
    (hPart₆ : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N (6 * β) R ≤ C₆)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    entropy (coulombMeasure N β) (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
      (((2 / paperLabeledRateFromReference hβ R) * coulombFormEnergy N hβ u : ℝ) : EReal) := by
  obtain ⟨M, hM, hMoment⟩ := paper_gibbs_moment_bound_of_partition_six hβ R hC₆ hPart₆
  exact paper_full_labeled_lsi_of_reference_bounds hβ R hPart₁ hMoment N hN u

end RepulsiveCoulomb.PaperRoute
