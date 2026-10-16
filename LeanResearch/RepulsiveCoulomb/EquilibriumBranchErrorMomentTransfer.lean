import LeanResearch.RepulsiveCoulomb.EquilibriumBranchModulatedErrorIdentity
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPartitionBasic

/-! Transfer from the generic centered-statistic moment to the actual
canonical regularization error. The factor 1/2 and the surviving one-body
correction remain explicit. This is an adapter, not an assumption or proof
of the still separate centered correlation moment theorem. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb

def equilibriumCenteredErrorStatistic {β : ℝ} {N : ℕ} (ε : ℝ)
    (R : EquilibriumConstructedReference β) (z : Fin N → ℂ) : ℝ :=
  equilibriumOrderedOffDiagonalSum (fun i j => equilibriumCenteredError ε R (z i) (z j)) / (N : ℝ)

def equilibriumErrorCanonicalCorrection {β : ℝ} {N : ℕ} (ε : ℝ)
    (R : EquilibriumConstructedReference β) (z : Fin N → ℂ) : ℝ :=
  -(∑ i : Fin N, equilibriumErrorPotential ε R (z i)) / (N : ℝ) + equilibriumErrorMean ε R / 2

theorem equilibriumErrorCanonicalCorrection_measurable {β : ℝ} {N : ℕ}
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε) :
    Measurable (equilibriumErrorCanonicalCorrection (N := N) ε R) := by
  have hs : Measurable (fun z : Fin N → ℂ => ∑ i : Fin N, equilibriumErrorPotential ε R (z i)) :=
    Finset.measurable_sum Finset.univ (fun i _ =>
      (equilibriumErrorPotential_measurable R hε).comp (measurable_pi_apply i))
  exact (hs.neg.div_const _).add measurable_const

theorem equilibriumCenteredErrorStatistic_measurable {β : ℝ} {N : ℕ}
    (R : EquilibriumConstructedReference β) {ε : ℝ} (hε : 0 < ε) :
    Measurable (equilibriumCenteredErrorStatistic (N := N) ε R) := by
  have hp (i j : Fin N) : Measurable (fun z : Fin N → ℂ =>
      if i = j then (0 : ℝ) else equilibriumCenteredError ε R (z i) (z j)) := by
    by_cases hij : i = j
    · simp only [hij, if_true]
      exact measurable_const
    · simp only [hij, if_false]
      have hpair : Measurable (fun z : Fin N → ℂ => (z i, z j)) :=
        (measurable_pi_apply i).prodMk (measurable_pi_apply j)
      have hcomp := (equilibriumCenteredError_joint_measurable R hε).comp hpair
      simpa only [Function.comp_def] using hcomp
  exact (Finset.measurable_sum Finset.univ (fun i _ =>
    Finset.measurable_sum Finset.univ (fun j _ => hp i j))).div_const _

theorem equilibriumReference_modulated_error_statistic_ae {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε) :
    (fun z : Fin N → ℂ => equilibriumModulatedEnergy R.density z - equilibriumRegularizedModulatedEnergy ε R z) =ᵐ[
      Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))]
      (fun z => equilibriumCenteredErrorStatistic ε R z / 2 + equilibriumErrorCanonicalCorrection ε R z) := by
  filter_upwards [equilibriumReference_product_injective_ae hβ R N] with z hz
  rw [equilibriumReference_modulated_error_identity hβ R hε hN z hz]
  unfold equilibriumCenteredErrorStatistic equilibriumErrorCanonicalCorrection
  ring

private theorem equilibrium_canonical_error_power_majorant {u c ε : ℝ}
    (hc : |c| ≤ 6 * ε ^ 2) (p : ℕ) :
    |u / 2 + c| ^ p ≤ (2 : ℝ) ^ (p - 1) *
      ((1 / 2 : ℝ) ^ p * |u| ^ p + (6 : ℝ) ^ p * ε ^ (2 * p)) := by
  have habs : |u / 2 + c| ≤ |u| / 2 + 6 * ε ^ 2 := by
    have h := abs_add_le (u / 2) c
    rw [abs_div, Nat.abs_ofNat] at h
    linarith
  have hpow := pow_le_pow_left₀ (abs_nonneg _) habs p
  have hsum := add_pow_le (by positivity : 0 ≤ |u| / 2) (by positivity : 0 ≤ 6 * ε ^ 2) p
  apply hpow.trans (hsum.trans_eq ?_)
  rw [div_pow, mul_pow, ← pow_mul]
  simp only [one_div, inv_pow]
  ring

/-- Given the genuine p-th moment integrability delivered by the generic
moment theorem, the actual canonical error is integrable and has the exact
normalization-sensitive moment bound. -/
theorem equilibriumReference_error_moment_transfer {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) {ε : ℝ} (hε : 0 < ε)
    (p : ℕ)
    (hU : Integrable (fun z : Fin N → ℂ => |equilibriumCenteredErrorStatistic ε R z| ^ p)
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)))) :
    Integrable (fun z : Fin N → ℂ =>
      |equilibriumModulatedEnergy R.density z - equilibriumRegularizedModulatedEnergy ε R z| ^ p)
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ∧
    (∫ z : Fin N → ℂ,
      |equilibriumModulatedEnergy R.density z - equilibriumRegularizedModulatedEnergy ε R z| ^ p
      ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ≤
      (2 : ℝ) ^ (p - 1) * ((1 / 2 : ℝ) ^ p *
        (∫ z : Fin N → ℂ, |equilibriumCenteredErrorStatistic ε R z| ^ p
          ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) + (6 : ℝ) ^ p * ε ^ (2 * p)) := by
  let P := Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))
  let H : (Fin N → ℂ) → ℝ := fun z =>
    |equilibriumCenteredErrorStatistic ε R z / 2 + equilibriumErrorCanonicalCorrection ε R z| ^ p
  have hsum : Measurable (fun z : Fin N → ℂ =>
      equilibriumCenteredErrorStatistic ε R z / 2 + equilibriumErrorCanonicalCorrection ε R z) :=
    ((equilibriumCenteredErrorStatistic_measurable R hε).div_const 2).add
      (equilibriumErrorCanonicalCorrection_measurable R hε)
  have hHm : Measurable H := by
    change Measurable (fun z : Fin N → ℂ =>
      |equilibriumCenteredErrorStatistic ε R z / 2 + equilibriumErrorCanonicalCorrection ε R z| ^ p)
    simpa only [Real.norm_eq_abs] using hsum.norm.pow_const p
  have hpoint (z : Fin N → ℂ) : H z ≤ (2 : ℝ) ^ (p - 1) *
      ((1 / 2 : ℝ) ^ p * |equilibriumCenteredErrorStatistic ε R z| ^ p + (6 : ℝ) ^ p * ε ^ (2 * p)) :=
    equilibrium_canonical_error_power_majorant (equilibriumError_oneBody_correction_bound R hε hN z) p
  have hmajor := ((hU.const_mul ((1 / 2 : ℝ) ^ p)).add
    (integrable_const ((6 : ℝ) ^ p * ε ^ (2 * p)))).const_mul ((2 : ℝ) ^ (p - 1))
  simp only [Pi.add_apply] at hmajor
  have hHi : Integrable H P := by
    apply hmajor.mono' hHm.aestronglyMeasurable
    exact Eventually.of_forall (fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg _) p)]
      exact hpoint z)
  have hae : (fun z : Fin N → ℂ =>
      |equilibriumModulatedEnergy R.density z - equilibriumRegularizedModulatedEnergy ε R z| ^ p) =ᵐ[P] H :=
    (equilibriumReference_modulated_error_statistic_ae hβ R hN hε).mono
      (fun z hz => by simp only [H, hz])
  refine ⟨hHi.congr hae.symm, ?_⟩
  rw [integral_congr_ae hae]
  have h := integral_mono hHi hmajor hpoint
  have hsum := integral_add (f := fun z : Fin N → ℂ =>
      (1 / 2 : ℝ) ^ p * |equilibriumCenteredErrorStatistic ε R z| ^ p)
    (g := fun _ : Fin N → ℂ => (6 : ℝ) ^ p * ε ^ (2 * p))
    (hU.const_mul _) (integrable_const _)
  rw [integral_const_mul, hsum, integral_const_mul] at h
  simpa only [integral_const, probReal_univ, one_smul] using h

end RepulsiveCoulomb
