module

public import LeanResearch.RepulsiveCoulomb.WeightedPointModel
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Finite-positive normalization of the literal weighted planar Gaussian.
The planar integration step uses Mathlib's volume-preserving real-product
identification. No polar integration, probability, or tail estimate is assumed.
The location-normalized upper bound is also an input to manuscript Lemma 3.3.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem integrable_planar_gaussian {b : ℝ} (hb : 0 < b) :
    Integrable (fun z : ℂ ↦ Real.exp (-b * ‖z‖ ^ 2)) := by
  have hprod := (integrable_exp_neg_mul_sq hb).mul_prod
    (integrable_exp_neg_mul_sq hb)
  have h := (Complex.volume_preserving_equiv_real_prod.integrable_comp_emb
    Complex.measurableEquivRealProd.measurableEmbedding).mpr hprod
  convert h using 1
  ext z
  simp only [Function.comp_def, Complex.measurableEquivRealProd_apply,
    ← Real.exp_add, Complex.sq_norm, Complex.normSq_apply]
  congr 1
  ring

theorem one_add_rpow_le_exp_mul {r a : ℝ} (hr : 0 ≤ r) (ha : 0 ≤ a) :
    (1 + r) ^ a ≤ Real.exp (r * a) := by
  rw [Real.rpow_def_of_pos (by linarith : 0 < 1 + r)]
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_right _ ha
  simpa using Real.log_le_sub_one_of_pos (by linarith : 0 < 1 + r)

theorem point_distance_rpow_le {a : ℝ} (ha : 0 ≤ a) (z y : ℂ) :
    ‖z - y‖ ^ a ≤ (1 + ‖y‖) ^ a * Real.exp (‖z‖ * a) := by
  have hd : ‖z - y‖ ≤ (1 + ‖y‖) * (1 + ‖z‖) := by
    have ht := norm_sub_le z y
    have hp := mul_nonneg (norm_nonneg y) (norm_nonneg z)
    nlinarith [norm_nonneg y, norm_nonneg z]
  calc
    ‖z - y‖ ^ a ≤ ((1 + ‖y‖) * (1 + ‖z‖)) ^ a :=
      Real.rpow_le_rpow (norm_nonneg _) hd ha
    _ = (1 + ‖y‖) ^ a * (1 + ‖z‖) ^ a :=
      Real.mul_rpow (by positivity) (by positivity)
    _ ≤ (1 + ‖y‖) ^ a * Real.exp (‖z‖ * a) :=
      mul_le_mul_of_nonneg_left (one_add_rpow_le_exp_mul (norm_nonneg _) ha)
        (Real.rpow_nonneg (by positivity) _)

/-- The location factor used in manuscript Lemma 3.3. -/
def pointLocationFactor {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : ℝ :=
  ∏ j, (1 + ‖y j‖) ^ a j

theorem pointLocationFactor_pos {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) :
    0 < pointLocationFactor a y := by
  exact Finset.prod_pos (fun j _ ↦ Real.rpow_pos_of_pos (by positivity) _)

theorem pointWeight_le_gaussian_linear {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (z : ℂ) :
    pointWeight γ a y z ≤ pointLocationFactor a y *
      Real.exp (-γ * ‖z‖ ^ 2 / 2 + ‖z‖ * ∑ j, a j) := by
  have hp : (∏ j, ‖z - y j‖ ^ a j) ≤
      ∏ j, ((1 + ‖y j‖) ^ a j * Real.exp (‖z‖ * a j)) := by
    exact Finset.prod_le_prod₀
      (fun j _ ↦ Real.rpow_nonneg (norm_nonneg _) _)
      (fun j _ ↦ point_distance_rpow_le (ha j) z (y j))
  calc
    pointWeight γ a y z ≤ Real.exp (-γ * ‖z‖ ^ 2 / 2) *
        ∏ j, ((1 + ‖y j‖) ^ a j * Real.exp (‖z‖ * a j)) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = pointLocationFactor a y *
        Real.exp (-γ * ‖z‖ ^ 2 / 2 + ‖z‖ * ∑ j, a j) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum, ← Finset.mul_sum, Real.exp_add]
      unfold pointLocationFactor
      ring

theorem gaussian_linear_le (γ q r : ℝ) (hγ : 0 < γ) :
    Real.exp (-γ * r ^ 2 / 2 + r * q) ≤
      Real.exp (q ^ 2 / γ) * Real.exp (-(γ / 4) * r ^ 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hq : 0 ≤ (γ * r - 2 * q) ^ 2 := sq_nonneg _
  apply (mul_le_mul_iff_of_pos_right hγ).mp
  field_simp
  nlinarith

theorem pointWeight_le_gaussian {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (z : ℂ) :
    pointWeight γ a y z ≤ (pointLocationFactor a y *
      Real.exp ((∑ j, a j) ^ 2 / γ)) * Real.exp (-(γ / 4) * ‖z‖ ^ 2) := by
  calc
    pointWeight γ a y z ≤ pointLocationFactor a y *
        Real.exp (-γ * ‖z‖ ^ 2 / 2 + ‖z‖ * ∑ j, a j) :=
      pointWeight_le_gaussian_linear γ ha y z
    _ ≤ pointLocationFactor a y *
        (Real.exp ((∑ j, a j) ^ 2 / γ) * Real.exp (-(γ / 4) * ‖z‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (gaussian_linear_le γ _ _ hγ)
        (pointLocationFactor_pos a y).le
    _ = _ := (mul_assoc _ _ _).symm

theorem pointWeight_integrable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    Integrable (pointWeight γ a y) := by
  refine ((integrable_planar_gaussian (by positivity : 0 < γ / 4)).const_mul
    (pointLocationFactor a y * Real.exp ((∑ j, a j) ^ 2 / γ))).mono'
      (pointWeight_measurable γ a y).aestronglyMeasurable ?_
  filter_upwards [] with z
  rw [Real.norm_eq_abs, abs_of_nonneg (pointWeight_nonneg γ a y z)]
  exact pointWeight_le_gaussian hγ ha y z

theorem pointPartition_lt_top {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointPartition γ a y < ⊤ :=
  (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (pointWeight_nonneg γ a y))).mp (pointWeight_integrable hγ ha y).hasFiniteIntegral

theorem pointWeight_pos_ae {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) :
    ∀ᵐ z : ℂ, 0 < pointWeight γ a y z := by
  have havoid : ∀ᵐ z : ℂ, ∀ j, z ≠ y j :=
    ae_all_iff.mpr (fun j ↦ volume.ae_ne (y j))
  filter_upwards [havoid] with z hz
  exact pointWeight_pos_of_avoids γ a y hz

theorem pointPartition_pos {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) :
    0 < pointPartition γ a y := by
  apply pos_iff_ne_zero.mpr
  intro hzero
  have hz := (lintegral_eq_zero_iff (pointWeight_measurable γ a y).ennreal_ofReal).mp hzero
  have hfalse : ∀ᵐ z : ℂ, False := by
    filter_upwards [hz, pointWeight_pos_ae γ a y] with z heq hpos
    exact (ne_of_gt (ENNReal.ofReal_pos.mpr hpos)) heq
  exact hfalse.exists.elim (fun _ h ↦ h)

/-- Normalization is unconditional on partition hypotheses: only the actual
positive Gaussian parameter and nonnegative finite exponents are required. -/
theorem pointMeasure_isProbability {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    IsProbabilityMeasure (pointMeasure γ a y) :=
  pointMeasure_isProbability_of_partition γ a y
    (ne_of_gt (pointPartition_pos γ a y)) (ne_of_lt (pointPartition_lt_top hγ ha y))

end RepulsiveCoulomb
