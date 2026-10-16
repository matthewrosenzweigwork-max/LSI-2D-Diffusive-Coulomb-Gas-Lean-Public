module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.LabeledEntropyFromReferenceMoments
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchGibbsDefectMoment

@[expose] public section

/-! Additive experimental source; verification is recorded separately in evidence. Actual Gibbs defect moments follow
from the upper partition bound at 6*beta, the correct Jensen lower bound
exp(beta*c/2), and the actual one-body exponential integral. There is no
assumption K>=1 and no omitted canonical 1/N one-body correction. -/
noncomputable section
open Set MeasureTheory Real
namespace RepulsiveCoulomb.PaperRoute

theorem paper_gibbs_moment_bound_of_partition_six {β C : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (hC : 0 < C)
    (hPart : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N (6 * β) R ≤ C) :
    ∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, 2 ≤ N → paperGibbsEntropyMoment R N ≤ M := by
  let a := Real.exp (β * equilibriumDensityInteraction R.density / 2)
  let J := ∫ x : ℂ, Real.exp (-4 * β * equilibriumDensityPotential R.density x) ∂R.measure
  have ha : 0 < a := Real.exp_pos _
  have hJi : Integrable (fun x : ℂ => Real.exp (-4 * β * equilibriumDensityPotential R.density x))
      (R.measure : Measure ℂ) :=
    (equilibriumReference_potential_exponential_bound (θ := 4) hβ le_rfl le_rfl (by norm_num) R).1
  have hJ : 0 < J := integral_exp_pos hJi
  let M := a⁻¹ * C ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ)
  have hM : 0 < M :=
    mul_pos (mul_pos (inv_pos.mpr ha) (Real.rpow_pos_of_pos hC _)) (Real.rpow_pos_of_pos hJ _)
  refine ⟨M, hM, ?_⟩
  intro N hN
  have hn : 0 < N := by omega
  have hKa : a ≤ equilibriumReferencePartition N β R :=
    equilibriumReferencePartition_lower hβ R hn hβ.le
  have hK6 : 0 < equilibriumReferencePartition N (6 * β) R :=
    equilibriumReferencePartition_pos hβ R hn (by positivity)
  have hInv : (equilibriumReferencePartition N β R)⁻¹ ≤ a⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le ha hKa
  have hRoot : (equilibriumReferencePartition N (6 * β) R) ^ (1 / 2 : ℝ) ≤ C ^ (1 / 2 : ℝ) :=
    Real.rpow_le_rpow hK6.le (hPart N hN) (by norm_num)
  have hb : paperGibbsEntropyMoment R N ≤
      (equilibriumReferencePartition N β R)⁻¹ *
        (equilibriumReferencePartition N (6 * β) R) ^ (1 / 2 : ℝ) * J ^ (1 / 2 : ℝ) := by
    simpa only [paperGibbsEntropyMoment, conditionalEntropyBranchThermalB,
      show (2 : ℝ) * (1 + 2) = 6 by norm_num,
      show (2 : ℝ) * 2 = 4 by norm_num] using
      (equilibriumReference_physical_gibbs_defect_moment hβ (by norm_num : (0 : ℝ) < 2) R hn).2
  apply hb.trans
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hInv hRoot (Real.rpow_nonneg hK6.le _) (inv_nonneg.mpr ha.le))
    (Real.rpow_nonneg hJ.le _)

/-- Only the two literal partition upper bounds remain; the exponential
moment prerequisite is derived above. The fixed-T-to-beta application must
be supplied by the new actual Holder argument, not an old all-t endpoint. -/
theorem paper_full_defective_of_partition_bounds {β C₁ C₆ : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (hC₆ : 0 < C₆)
    (hPart₁ : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N β R ≤ C₁)
    (hPart₆ : ∀ N : ℕ, 2 ≤ N → equilibriumReferencePartition N (6 * β) R ≤ C₆)
    (N : ℕ) (hN : 2 ≤ N) (u : CoulombFormDomain N hβ) :
    PeriodicAttractiveLogGas.entropy (coulombMeasure N β)
      (fun z => (coulombFormValueL N hβ u z) ^ 2) ≤
      (((4 / paperOneSiteRate β) * coulombFormEnergy N hβ u +
        2 * paperUniformEntropyDefect R *
          (∫ z, (coulombFormValueL N hβ u z) ^ 2 ∂coulombMeasure N β) : ℝ) : EReal) := by
  obtain ⟨M, hM, hMoment⟩ := paper_gibbs_moment_bound_of_partition_six hβ R hC₆ hPart₆
  exact paper_full_defective_of_reference_bounds hβ R hPart₁ hMoment N hN u

end RepulsiveCoulomb.PaperRoute
