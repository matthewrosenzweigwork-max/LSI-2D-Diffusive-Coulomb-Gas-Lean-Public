module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCenteredErrorMoments
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchErrorMomentTransfer
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPartitionParameters
public import LeanResearch.RepulsiveCoulomb.PartitionMomentBranchCorrelation

@[expose] public section

/-! Instantiation of the genuine finite-product correlation theorem with the
actual double-error kernel. No analytic moment hypothesis remains: centering,
measurability, symmetry, row integrability and both row bounds are supplied
by the constructed thermal reference. All constants are independent of N,beta. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

def equilibriumStatisticMomentConstant (k m : ℕ) : ℝ :=
  ((2 * k * m : ℕ) : ℝ) ^ (2 * (2 * k * m) + 1) *
    (equilibriumCenteredErrorMomentConstant (2 * k * m) +
      equilibriumCenteredErrorMomentConstant (4 * m) ^ ((k : ℝ) / 2))

def equilibriumCanonicalErrorMomentConstant (k m : ℕ) : ℝ :=
  (2 : ℝ) ^ (2 * k * m - 1) *
    ((1 / 2 : ℝ) ^ (2 * k * m) * equilibriumStatisticMomentConstant k m + (6 : ℝ) ^ (2 * k * m))

theorem equilibriumStatisticMomentConstant_nonneg (k m : ℕ) :
    0 ≤ equilibriumStatisticMomentConstant k m := by
  unfold equilibriumStatisticMomentConstant
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
    (add_nonneg (equilibriumCenteredErrorMomentConstant_pos _).le
      (Real.rpow_nonneg (equilibriumCenteredErrorMomentConstant_pos _).le _))

theorem equilibriumCanonicalErrorMomentConstant_pos (k m : ℕ) :
    0 < equilibriumCanonicalErrorMomentConstant k m := by
  unfold equilibriumCanonicalErrorMomentConstant
  have hc := equilibriumStatisticMomentConstant_nonneg k m
  positivity

/-- Exact identification with the generic ordered statistic, including its
factor 1/N and the label-only off-diagonal convention. -/
theorem equilibriumCenteredErrorStatistic_eq_partitionMoment {β : ℝ} {N : ℕ}
    (R : EquilibriumConstructedReference β) (ε : ℝ) (z : Fin N → ℂ) :
    equilibriumCenteredErrorStatistic ε R z =
      partitionMomentOrderedStatistic (equilibriumCenteredError ε R) z := by
  unfold equilibriumCenteredErrorStatistic equilibriumOrderedOffDiagonalSum partitionMomentOrderedStatistic
  rw [Fintype.sum_prod_type]

/-- The centered correlation moment, with every generic kernel hypothesis
proved for the actual thermal reference and with the stronger N^(-2m) term. -/
theorem equilibriumReference_centered_statistic_moment {β : ℝ}
    (R : EquilibriumConstructedReference β) {N k m : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun z : Fin N → ℂ => |equilibriumCenteredErrorStatistic ε R z| ^ (2 * k * m))
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ∧
    (∫ z : Fin N → ℂ, |equilibriumCenteredErrorStatistic ε R z| ^ (2 * k * m)
      ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ≤
      equilibriumStatisticMomentConstant k m * (ε ^ 2 / (N : ℝ) ^ (2 * m) + ε ^ k) := by
  have hk0 : 0 < k := by omega
  have hm0 : 0 < m := by omega
  have hp : 0 < 2 * k * m := by positivity
  have hq : 0 < 4 * m := by positivity
  have h := partitionMoment_centered_ordered_bound hN hk hm (equilibriumCenteredError ε R)
    (equilibriumCenteredError_joint_measurable R hε) (equilibriumCenteredError_symm R hε)
    (equilibriumCenteredError_row_integrable R hε) (integral_equilibriumCenteredError_zero R hε)
    (equilibriumCenteredErrorMomentConstant (2 * k * m) * ε ^ 2)
    (equilibriumCenteredErrorMomentConstant (4 * m) * ε ^ 2)
    (mul_nonneg (equilibriumCenteredErrorMomentConstant_pos _).le (sq_nonneg _))
    (mul_nonneg (equilibriumCenteredErrorMomentConstant_pos _).le (sq_nonneg _))
    (fun x => (equilibriumCenteredError_row_power R hε _ hp x).1)
    (fun x => (equilibriumCenteredError_row_power R hε _ hp x).2)
    (fun x => (equilibriumCenteredError_row_power R hε _ hq x).1)
    (fun x => (equilibriumCenteredError_row_power R hε _ hq x).2)
  simp_rw [← equilibriumCenteredErrorStatistic_eq_partitionMoment R ε] at h
  refine ⟨h.1, ?_⟩
  have he : (equilibriumCenteredErrorMomentConstant (4 * m) * ε ^ 2) ^
      ((2 * k * m : ℝ) / (4 * m : ℝ)) =
      equilibriumCenteredErrorMomentConstant (4 * m) ^ ((k : ℝ) / 2) * ε ^ k := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      equilibriumPartition_radius_power (k := k) hm (equilibriumCenteredErrorMomentConstant_pos _).le hε
  rw [he] at h
  have hX : 0 ≤ ε ^ 2 / (N : ℝ) ^ (2 * m) := div_nonneg (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hY : 0 ≤ ε ^ k := pow_nonneg hε.le _
  have hCp := (equilibriumCenteredErrorMomentConstant_pos (2 * k * m)).le
  have hCq := Real.rpow_nonneg (equilibriumCenteredErrorMomentConstant_pos (4 * m)).le ((k : ℝ) / 2)
  have hc : equilibriumCenteredErrorMomentConstant (2 * k * m) * (ε ^ 2 / (N : ℝ) ^ (2 * m)) +
      equilibriumCenteredErrorMomentConstant (4 * m) ^ ((k : ℝ) / 2) * ε ^ k ≤
      (equilibriumCenteredErrorMomentConstant (2 * k * m) +
        equilibriumCenteredErrorMomentConstant (4 * m) ^ ((k : ℝ) / 2)) *
        (ε ^ 2 / (N : ℝ) ^ (2 * m) + ε ^ k) := by
    nlinarith [mul_nonneg hCp hY, mul_nonneg hCq hX]
  apply h.2.trans
  have hscale := mul_le_mul_of_nonneg_left hc
    (pow_nonneg (show (0 : ℝ) ≤ (2 * k * m : ℕ) by positivity) (2 * (2 * k * m) + 1))
  unfold equilibriumStatisticMomentConstant
  simpa only [Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc, mul_assoc] using hscale

/-- Actual canonical regularization-error moments, with all terms and the
one-body correction retained and bounded uniformly for 0<epsilon<=1. -/
theorem equilibriumReference_canonical_error_moment {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N k m : ℕ} (hN : 2 ≤ N) (hk : 2 ≤ k) (hm : 1 ≤ m)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    Integrable (fun z : Fin N → ℂ =>
      |equilibriumModulatedEnergy R.density z - equilibriumRegularizedModulatedEnergy ε R z| ^ (2 * k * m))
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ∧
    (∫ z : Fin N → ℂ,
      |equilibriumModulatedEnergy R.density z - equilibriumRegularizedModulatedEnergy ε R z| ^ (2 * k * m)
      ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ≤
      equilibriumCanonicalErrorMomentConstant k m * (ε ^ 2 / (N : ℝ) ^ (2 * m) + ε ^ k) := by
  obtain ⟨hUi, hUb⟩ := equilibriumReference_centered_statistic_moment R hN hk hm hε
  obtain ⟨hEi, hEb⟩ := equilibriumReference_error_moment_transfer hβ R (by omega : 0 < N) hε (2 * k * m) hUi
  refine ⟨hEi, ?_⟩
  have horder : k ≤ 2 * (2 * k * m) := by
    have hkm := Nat.mul_le_mul_left k hm
    nlinarith
  have hpow : ε ^ (2 * (2 * k * m)) ≤ ε ^ k := pow_le_pow_of_le_one hε.le hε1 horder
  have hX : 0 ≤ ε ^ 2 / (N : ℝ) ^ (2 * m) := div_nonneg (sq_nonneg _) (pow_nonneg (Nat.cast_nonneg _) _)
  have hY : 0 ≤ ε ^ k := pow_nonneg hε.le _
  have h1 := mul_le_mul_of_nonneg_left hUb (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (2 * k * m))
  have h2 := mul_le_mul_of_nonneg_left (hpow.trans (le_add_of_nonneg_left hX))
    (by positivity : 0 ≤ (6 : ℝ) ^ (2 * k * m))
  have h := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (by positivity : 0 ≤ (2 : ℝ) ^ (2 * k * m - 1))
  apply hEb.trans (h.trans_eq ?_)
  unfold equilibriumCanonicalErrorMomentConstant
  ring

end RepulsiveCoulomb
