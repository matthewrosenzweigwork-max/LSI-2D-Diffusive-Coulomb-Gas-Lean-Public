import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchPointNormalizer
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceBounds
import LeanResearch.RepulsiveCoulomb.CoulombOneSiteKernel
import LeanResearch.RepulsiveCoulomb.PointWeightLocalComparison
import Mathlib.MeasureTheory.Measure.Tilted

/-!
Actual one-site Coulomb conditional as a normalized thermal-reference tilt.
The exponent identity is proved off the finite frozen root set and used only
almost everywhere for density/measure identities. Frozen roots may coincide.
The normalizer is derived from the genuine positive finite point normalizer.
Constructed thermal reference prerequisites are still uncompiled future inputs.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Filter
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

def conditionalEntropyBranchThermalPhi {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (y : CoulombConfig N) (w : ℂ) : ℝ :=
  (∑ j, equilibriumLogKernel (w - y j)) / ((N + 1 : ℕ) : ℝ) -
    equilibriumDensityPotential R.density w

theorem conditionalEntropyBranchThermalPhi_measurable {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) :
    Measurable (fun p : CoulombConfig N × ℂ => conditionalEntropyBranchThermalPhi R p.1 p.2) := by
  have hs : Measurable (fun p : CoulombConfig N × ℂ =>
      ∑ j : Fin N, equilibriumLogKernel (p.2 - p.1 j)) :=
    Finset.measurable_sum Finset.univ (fun j _ => equilibriumLogKernel_measurable.comp
      (measurable_snd.sub ((coulombCoordinate j).continuous.measurable.comp measurable_fst)))
  exact (hs.div_const _).sub
    ((equilibriumDensityPotential_measurable R.smooth.continuous.measurable).comp measurable_snd)

/-- Pointwise equality is restricted to the complement of every frozen root.
It is intentionally not asserted at collisions, where Real.log 0 is defaulted. -/
theorem conditionalEntropyBranch_thermal_exp_weight {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (y : CoulombConfig N) {w : ℂ}
    (hw : ∀ j, w ≠ y j) :
    Real.exp (-β * conditionalEntropyBranchThermalPhi R y w) * R.density w =
      Real.exp R.elConstant * pointWeight β (coulombOneSiteExponents N β) (fun j => y j) w := by
  calc
    Real.exp (-β * conditionalEntropyBranchThermalPhi R y w) * R.density w =
        Real.exp (-β * conditionalEntropyBranchThermalPhi R y w + Real.log (R.density w)) := by
      rw [Real.exp_add, Real.exp_log (R.positive w)]
    _ = Real.exp (R.elConstant + pointLogWeight β (coulombOneSiteExponents N β) (fun j => y j) w) := by
      congr 1
      rw [R.eulerLagrange w]
      unfold conditionalEntropyBranchThermalPhi pointLogWeight coulombOneSiteExponents equilibriumLogKernel
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum]
      ring
    _ = _ := by rw [Real.exp_add, exp_pointLogWeight β _ _ hw]

theorem conditionalEntropyBranch_thermal_exp_weight_ae {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (y : CoulombConfig N) :
    (fun w => Real.exp (-β * conditionalEntropyBranchThermalPhi R y w) * R.density w) =ᵐ[volume]
      (fun w => Real.exp R.elConstant * pointWeight β (coulombOneSiteExponents N β) (fun j => y j) w) := by
  have hroot : ∀ᵐ w : ℂ ∂volume, ∀ j : Fin N, w ≠ y j :=
    ae_all_iff.mpr (fun j => volume.ae_ne (y j))
  exact hroot.mono (fun w hw => conditionalEntropyBranch_thermal_exp_weight R y hw)

theorem conditionalEntropyBranch_thermal_exp_integrable {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β) (y : CoulombConfig N) :
    Integrable (fun w => Real.exp (-β * conditionalEntropyBranchThermalPhi R y w))
      (R.measure : Measure ℂ) := by
  have hi := (pointWeight_integrable hβ (coulombOneSiteExponents_nonneg N hβ.le)
    (fun j => y j)).const_mul (Real.exp R.elConstant)
  have hw : Integrable (fun w => Real.exp (-β * conditionalEntropyBranchThermalPhi R y w) *
      R.density w) := hi.congr (conditionalEntropyBranch_thermal_exp_weight_ae R y).symm
  rw [← R.density_measure]
  exact (equilibriumDensityMeasure_integrable_iff R.smooth.continuous.measurable
    (fun w => (R.positive w).le) _).mpr hw

theorem conditionalEntropyBranch_thermal_normalizer {N : ℕ} {β : ℝ}
    (R : EquilibriumConstructedReference β) (y : CoulombConfig N) :
    (∫ w, Real.exp (-β * conditionalEntropyBranchThermalPhi R y w) ∂(R.measure : Measure ℂ)) =
      Real.exp R.elConstant * ∫ w : ℂ, pointWeight β (coulombOneSiteExponents N β) (fun j => y j) w := by
  rw [← R.density_measure, integral_equilibriumDensityMeasure R.smooth.continuous.measurable
    (fun w => (R.positive w).le), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [conditionalEntropyBranch_thermal_exp_weight_ae R y] with w hw
  simpa only [mul_comm] using hw

theorem conditionalEntropyBranch_thermal_log_normalizer {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β) (y : CoulombConfig N) :
    Real.log (∫ w, Real.exp (-β * conditionalEntropyBranchThermalPhi R y w)
      ∂(R.measure : Measure ℂ)) =
      R.elConstant + conditionalEntropyBranchPointLogNormalizer β (coulombOneSiteExponents N β) y := by
  rw [conditionalEntropyBranch_thermal_normalizer R y,
    Real.log_mul (Real.exp_pos _).ne'
      (pointWeight_integral_pos hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j)).ne',
    Real.log_exp]
  rfl

/-- Exact probability-law identity for the already checked Gibbs one-site
kernel. No separation of frozen coordinates is assumed. -/
theorem conditionalEntropyBranch_thermal_tilt_eq_kernel {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β) (y : CoulombConfig N) :
    (R.measure : Measure ℂ).tilted (fun w => -β * conditionalEntropyBranchThermalPhi R y w) =
      coulombOneSiteKernel N β hβ y := by
  have hPhi : Measurable (fun w => conditionalEntropyBranchThermalPhi R y w) := by
    simpa only [Function.comp_def] using
      (conditionalEntropyBranchThermalPhi_measurable (N := N) R).comp
        (measurable_prodMk_left : Measurable (fun w : ℂ => (y, w)))
  have hnorm := conditionalEntropyBranch_thermal_normalizer R y
  have hI := pointWeight_integral_pos hβ (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j)
  rw [Measure.tilted, hnorm, ← R.density_measure, equilibriumDensityMeasure,
    ← withDensity_mul volume R.smooth.continuous.measurable.ennreal_ofReal
      (((hPhi.const_mul (-β)).exp.div_const _).ennreal_ofReal),
    coulombOneSiteKernel_apply, pointMeasure_eq_withDensity hβ
      (coulombOneSiteExponents_nonneg N hβ.le) (fun j => y j)]
  apply withDensity_congr_ae
  filter_upwards [conditionalEntropyBranch_thermal_exp_weight_ae R y] with w hw
  dsimp only [Pi.mul_apply]
  rw [← ENNReal.ofReal_mul (R.positive w).le]
  congr 1
  unfold pointDensity
  field_simp [hI.ne', Real.exp_ne_zero R.elConstant]
  simpa only [neg_mul, mul_comm] using hw

end RepulsiveCoulomb
