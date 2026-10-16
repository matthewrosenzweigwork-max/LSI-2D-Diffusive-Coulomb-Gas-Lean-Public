import LeanResearch.RepulsiveCoulomb.WeightedPointNormalization
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.PolarCoord

/-! Uniform estimates for the actual finite point-weight family.
The location factor is the one in manuscript Lemma 3.3. All integrability
and normalization claims concern planar Lebesgue measure, not a torus.
-/
noncomputable section
open MeasureTheory Real Filter
open scoped BigOperators ENNReal Topology
namespace RepulsiveCoulomb

theorem pointWeight_continuous {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : Continuous (pointWeight γ a y) := by
  unfold pointWeight
  apply Continuous.mul (by fun_prop)
  apply continuous_finsetProd
  intro j _
  exact (Real.continuous_rpow_const (ha j)).comp (by fun_prop)

/-- The fixed Gaussian-polynomial envelope in Lemma 3.3. -/
def pointEnvelope (γ Q : ℝ) (z : ℂ) : ℝ :=
  Real.exp (-γ * ‖z‖ ^ 2 / 2) * (1 + ‖z‖) ^ Q

theorem pointEnvelope_nonneg (γ Q : ℝ) (z : ℂ) : 0 ≤ pointEnvelope γ Q z := by
  unfold pointEnvelope
  positivity

theorem pointWeight_le_envelope {m : ℕ} (γ : ℝ) {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) (z : ℂ) :
    pointWeight γ a y z ≤ pointLocationFactor a y * pointEnvelope γ Q z := by
  have hp : (∏ j, ‖z - y j‖ ^ a j) ≤
      ∏ j, ((1 + ‖y j‖) ^ a j * (1 + ‖z‖) ^ a j) := by
    apply Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
    intro j _
    rw [← Real.mul_rpow (by positivity) (by positivity)]
    apply Real.rpow_le_rpow (norm_nonneg _) _ (ha j)
    have ht := norm_sub_le z (y j)
    nlinarith [norm_nonneg z, norm_nonneg (y j), mul_nonneg (norm_nonneg z) (norm_nonneg (y j))]
  rw [Finset.prod_mul_distrib, ← Real.rpow_sum_of_pos (by positivity)] at hp
  have hpow := Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z] : 1 ≤ 1 + ‖z‖) hQ
  calc
    pointWeight γ a y z ≤ Real.exp (-γ * ‖z‖ ^ 2 / 2) *
        (pointLocationFactor a y * (1 + ‖z‖) ^ ∑ j, a j) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ ≤ Real.exp (-γ * ‖z‖ ^ 2 / 2) * (pointLocationFactor a y * (1 + ‖z‖) ^ Q) := by
      gcongr
      exact (pointLocationFactor_pos a y).le
    _ = _ := by unfold pointEnvelope; ring

theorem pointEnvelope_continuous (γ : ℝ) {Q : ℝ} (hQ : 0 ≤ Q) :
    Continuous (pointEnvelope γ Q) := by
  exact Continuous.mul (by fun_prop) ((Real.continuous_rpow_const hQ).comp (by fun_prop))

theorem pointEnvelope_le_gaussian {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) (z : ℂ) :
    pointEnvelope γ Q z ≤ Real.exp (Q ^ 2 / γ) * Real.exp (-(γ / 4) * ‖z‖ ^ 2) := by
  calc
    pointEnvelope γ Q z ≤ Real.exp (-γ * ‖z‖ ^ 2 / 2) * Real.exp (‖z‖ * Q) :=
      mul_le_mul_of_nonneg_left (one_add_rpow_le_exp_mul (norm_nonneg z) hQ) (Real.exp_pos _).le
    _ = Real.exp (-γ * ‖z‖ ^ 2 / 2 + ‖z‖ * Q) := (Real.exp_add _ _).symm
    _ ≤ _ := gaussian_linear_le γ Q ‖z‖ hγ

theorem pointEnvelope_integrable {γ Q : ℝ} (hγ : 0 < γ) (hQ : 0 ≤ Q) :
    Integrable (pointEnvelope γ Q) := by
  refine ((integrable_planar_gaussian (by positivity : 0 < γ / 4)).const_mul
    (Real.exp (Q ^ 2 / γ))).mono' (pointEnvelope_continuous γ hQ).aestronglyMeasurable ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (pointEnvelope_nonneg γ Q z)]
  exact pointEnvelope_le_gaussian hγ hQ z

theorem pointPartition_eq_ofReal_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointPartition γ a y = ENNReal.ofReal (∫ z : ℂ, pointWeight γ a y z) := by
  exact (ofReal_integral_eq_lintegral_ofReal (pointWeight_integrable hγ ha y)
    (Eventually.of_forall (pointWeight_nonneg γ a y))).symm

theorem pointPartition_le_envelope {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    pointPartition γ a y ≤ ENNReal.ofReal (pointLocationFactor a y * ∫ z : ℂ, pointEnvelope γ Q z) := by
  have hQ0 := (Finset.sum_nonneg (fun j _ ↦ ha j)).trans hQ
  rw [pointPartition_eq_ofReal_integral hγ ha y, ← integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  exact integral_mono (pointWeight_integrable hγ ha y)
    ((pointEnvelope_integrable hγ hQ0).const_mul _) (pointWeight_le_envelope γ ha hQ y)

end RepulsiveCoulomb
