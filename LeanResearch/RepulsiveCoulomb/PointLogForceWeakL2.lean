import LeanResearch.RepulsiveCoulomb.PlanarTruncatedLogKernel
import Mathlib.Analysis.Normed.Group.AddTorsor

/-! The configuration-uniform weak L2 estimate for the literal finite
logarithmic force in manuscript Lemma 3.4 (label lem:weak-field).

Proof adaptation: truncate the inverse-distance kernel at radius R, control
the far part by total mass/R, and apply Chebyshev to the near part, whose
L1 norm is computed using planar radial integration. This replaces the
manuscript's finite-atomic maximal-function proof, not its conclusion or
hypotheses. It avoids applying a Haar/function maximal theorem to an atomic
measure. The explicit universal constant is 8*pi; it is not claimed sharp.
-/
noncomputable section
open MeasureTheory Set Metric Real Filter
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

def pointLogForce {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℂ :=
  ∑ j, a j • ((‖z - y j‖ ^ 2)⁻¹ • (z - y j))

def pointTruncatedPotential {m : ℕ} (R : ℝ) (a : Fin m → ℝ)
    (y : Fin m → ℂ) (z : ℂ) : ℝ :=
  ∑ j, a j * truncatedLogKernel R (z - y j)

theorem norm_logForceKernel (z : ℂ) : ‖(‖z‖ ^ 2)⁻¹ • z‖ = ‖z‖⁻¹ := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  by_cases hz : ‖z‖ = 0
  · simp [hz]
  · field_simp

theorem norm_pointLogForce_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (z : ℂ) :
    ‖pointLogForce a y z‖ ≤ ∑ j, a j * ‖z - y j‖⁻¹ := by
  calc
    ‖pointLogForce a y z‖ ≤ ∑ j, ‖a j • ((‖z - y j‖ ^ 2)⁻¹ • (z - y j))‖ :=
      norm_sum_le _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ha j), norm_logForceKernel]

theorem inverseNorm_le_truncated {R : ℝ} (hR : 0 < R) (z : ℂ) :
    ‖z‖⁻¹ ≤ truncatedLogKernel R z + R⁻¹ := by
  by_cases hz : ‖z‖ < R
  · simp only [truncatedLogKernel, ite_eq_left hz]
    exact le_add_of_nonneg_right (by positivity)
  · simp only [truncatedLogKernel, ite_eq_right hz, zero_add]
    exact inv_anti₀ hR (le_of_not_gt hz)

theorem pointTruncatedPotential_nonneg {m : ℕ} (R : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (z : ℂ) :
    0 ≤ pointTruncatedPotential R a y z :=
  Finset.sum_nonneg (fun j _ ↦ mul_nonneg (ha j) (truncatedLogKernel_nonneg R _))

theorem pointTruncatedPotential_integrable {m : ℕ} (R : ℝ)
    (a : Fin m → ℝ) (y : Fin m → ℂ) : Integrable (pointTruncatedPotential R a y) :=
  integrable_finsetSum _ (fun j _ ↦ (truncatedLogKernel_shift_integrable R (y j)).const_mul (a j))

theorem integral_pointTruncatedPotential {m : ℕ} {R : ℝ} (hR : 0 ≤ R)
    (a : Fin m → ℝ) (y : Fin m → ℂ) :
    ∫ z, pointTruncatedPotential R a y z = 2 * Real.pi * R * ∑ j, a j := by
  unfold pointTruncatedPotential
  rw [integral_finsetSum _ (fun j _ ↦ (truncatedLogKernel_shift_integrable R (y j)).const_mul (a j))]
  simp_rw [integral_const_mul, integral_truncatedLogKernel_shift hR]
  rw [← Finset.sum_mul]
  ring

theorem pointLogForce_le_truncated {m : ℕ} {R : ℝ} (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (z : ℂ) :
    ‖pointLogForce a y z‖ ≤ pointTruncatedPotential R a y z + (∑ j, a j) * R⁻¹ := by
  calc
    ‖pointLogForce a y z‖ ≤ ∑ j, a j * ‖z - y j‖⁻¹ := norm_pointLogForce_le ha y z
    _ ≤ ∑ j, a j * (truncatedLogKernel R (z - y j) + R⁻¹) :=
      Finset.sum_le_sum (fun j _ ↦ mul_le_mul_of_nonneg_left (inverseNorm_le_truncated hR _) (ha j))
    _ = _ := by simp only [mul_add, Finset.sum_add_distrib, Finset.sum_mul, pointTruncatedPotential]

/-- The actual vector field has a weak L2 bound depending only on total
exponent. Empty families, zero exponents and arbitrary coincidences are included. -/
theorem pointLogForce_weak_l2 {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {t : ℝ} (ht : 0 < t) :
    volume {z : ℂ | t < ‖pointLogForce a y z‖} ≤
      ENNReal.ofReal (8 * Real.pi * (∑ j, a j) ^ 2 / t ^ 2) := by
  classical
  have hq : 0 ≤ ∑ j, a j := Finset.sum_nonneg (fun j _ ↦ ha j)
  by_cases hq0 : ∑ j, a j = 0
  · have hazero : ∀ j, a j = 0 := by
      intro j
      exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ ↦ ha j)).mp hq0 j (Finset.mem_univ j)
    simp [pointLogForce, hazero, not_lt_of_ge ht.le]
  · have hqpos : 0 < ∑ j, a j := lt_of_le_of_ne hq (Ne.symm hq0)
    let R : ℝ := 2 * (∑ j, a j) / t
    have hR : 0 < R := by dsimp [R]; positivity
    have hfar : (∑ j, a j) * R⁻¹ = t / 2 := by
      dsimp [R]
      field_simp
    have hi : Integrable (fun z ↦ (2 / t) * pointTruncatedPotential R a y z) :=
      (pointTruncatedPotential_integrable R a y).const_mul (2 / t)
    have hbound := hi.measure_le_integral
      (Eventually.of_forall (fun z ↦ mul_nonneg (by positivity) (pointTruncatedPotential_nonneg R ha y z)))
      (s := {z : ℂ | t < ‖pointLogForce a y z‖}) (fun z hz ↦ by
        have h := pointLogForce_le_truncated hR ha y z
        rw [hfar] at h
        rw [div_mul_eq_mul_div]
        apply (le_div_iff₀ ht).mpr
        change t < ‖pointLogForce a y z‖ at hz
        nlinarith)
    rw [integral_const_mul, integral_pointTruncatedPotential hR.le] at hbound
    convert hbound using 1
    congr 1
    dsimp [R]
    field_simp
    ring

/-- The manuscript's formulation with a prescribed total-exponent bound. -/
theorem pointLogForce_weak_l2_of_total_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {Q t : ℝ}
    (hQ : ∑ j, a j ≤ Q) (ht : 0 < t) :
    volume {z : ℂ | t < ‖pointLogForce a y z‖} ≤ ENNReal.ofReal (8 * Real.pi * Q ^ 2 / t ^ 2) := by
  apply (pointLogForce_weak_l2 ha y ht).trans
  apply ENNReal.ofReal_le_ofReal
  have hq : 0 ≤ ∑ j, a j := Finset.sum_nonneg (fun j _ ↦ ha j)
  have hsq : (∑ j, a j) ^ 2 ≤ Q ^ 2 := by nlinarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by positivity)) (sq_nonneg t)

end RepulsiveCoulomb
