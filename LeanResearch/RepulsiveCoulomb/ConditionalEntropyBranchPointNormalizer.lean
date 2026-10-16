import LeanResearch.RepulsiveCoulomb.PointWeightUniformTails
import LeanResearch.RepulsiveCoulomb.PointMeasureParametric
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchLogKernel

/-!
Actual logarithmic normalizer control from the checked point-weight bounds.
There is no separation assumption on the frozen roots. The constants are
chosen before their number, locations, and nonnegative exponent vector.
Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory Real Filter
open scoped BigOperators
namespace RepulsiveCoulomb

def conditionalEntropyBranchPointLogNormalizer {m : ℕ} (γ : ℝ) (a : Fin m → ℝ)
    (y : CoulombConfig m) : ℝ := Real.log (∫ z : ℂ, pointWeight γ a (fun j => y j) z)

theorem conditionalEntropyBranchPointLogNormalizer_measurable {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) :
    Measurable (conditionalEntropyBranchPointLogNormalizer γ a) :=
  ((pointWeight_joint_continuous γ ha).measurable.stronglyMeasurable.integral_prod_right').measurable.log

theorem conditionalEntropyBranch_point_log_normalizer_bound {γ Q : ℝ}
    (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (y : CoulombConfig m),
      (∀ j, 0 ≤ a j) → (∑ j, a j ≤ Q) →
      |conditionalEntropyBranchPointLogNormalizer γ a y| ≤
        C + ∑ j, a j * equilibriumLogMoment (y j) := by
  obtain ⟨c, D, R, hc, hcD, hR, hb⟩ := uniform_pointWeight_normalization_and_tails hγ hQ
  refine ⟨|Real.log c| + |Real.log D|, add_nonneg (abs_nonneg _) (abs_nonneg _), ?_⟩
  intro m a y ha hsum
  have hD : 0 < D := hc.trans_le hcD
  obtain ⟨hlo, hhi, _, _⟩ := hb m a (fun j => y j) ha hsum
  have hLoc := pointLocationFactor_pos a (fun j => y j)
  have hI : 0 < ∫ z : ℂ, pointWeight γ a (fun j => y j) z := (mul_pos hc hLoc).trans_le hlo
  have hl := Real.log_le_log (mul_pos hc hLoc) hlo
  have hu := Real.log_le_log hI hhi
  rw [Real.log_mul hc.ne' hLoc.ne', pointLocationFactor_eq_exp_sum, Real.log_exp] at hl
  rw [Real.log_mul hD.ne' hLoc.ne', pointLocationFactor_eq_exp_sum, Real.log_exp] at hu
  have hL : 0 ≤ ∑ j, a j * equilibriumLogMoment (y j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (ha j) (equilibriumLogMoment_nonneg _))
  unfold conditionalEntropyBranchPointLogNormalizer
  change Real.log c + (∑ j, a j * equilibriumLogMoment (y j)) ≤ _ at hl
  change _ ≤ Real.log D + (∑ j, a j * equilibriumLogMoment (y j)) at hu
  apply abs_le.mpr
  constructor <;> linarith [neg_abs_le (Real.log c), le_abs_self (Real.log D),
    abs_nonneg (Real.log c), abs_nonneg (Real.log D)]

/-- The log normalizer is integrable whenever the actual frozen-coordinate
logarithmic moments are integrable. Its integrability is not inferred by
subtracting formal entropy expressions. -/
theorem conditionalEntropyBranch_point_log_normalizer_integrable {m : ℕ} {γ Q : ℝ}
    (hγ : 0 < γ) (hQ : 0 ≤ Q) {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hsum : ∑ j, a j ≤ Q) (ν : Measure (CoulombConfig m)) [IsFiniteMeasure ν]
    (hlog : ∀ j, Integrable (fun y => equilibriumLogMoment (y j)) ν) :
    Integrable (conditionalEntropyBranchPointLogNormalizer γ a) ν := by
  obtain ⟨C, hC, hb⟩ := conditionalEntropyBranch_point_log_normalizer_bound hγ hQ
  have hi : Integrable (fun y => C + ∑ j, a j * equilibriumLogMoment (y j)) ν :=
    (integrable_const C).add
      (integrable_finsetSum Finset.univ (fun j _ => (hlog j).const_mul (a j)))
  apply hi.mono' (conditionalEntropyBranchPointLogNormalizer_measurable γ ha).aestronglyMeasurable
  exact Eventually.of_forall (fun y => by
    simpa only [Real.norm_eq_abs] using hb m a y ha hsum)

end RepulsiveCoulomb
