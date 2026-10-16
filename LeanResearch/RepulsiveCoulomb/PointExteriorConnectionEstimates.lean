module

public import LeanResearch.RepulsiveCoulomb.PointConformalConnection
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Tactic

@[expose] public section

/-!
UNCOMPILED ADDITIVE DRAFT, 2026-10-02. No accepted-source or inventory claim.

Literal finite-product exterior connection and phase estimates. The connection is
the existing derivative of the actual conformal logarithm; the correction is an
actual single-valued finite sum of principal logarithms, not an assumed phase.
All declarations below contain proof terms. They have not been compiler checked.
The global geodesic angle lift and its propagation are separate dependencies.
-/

noncomputable section
open Set Filter InnerProductSpace
open scoped BigOperators Topology ComplexConjugate

namespace RepulsiveCoulomb

def pointExteriorHalfMass {m : ℕ} (a : Fin m → ℝ) : ℝ := ∑ j, a j / 2

def pointExteriorMoment {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : ℝ :=
  2 * ∑ j, (a j / 2) * ‖y j‖

def pointExteriorConnectionError {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℂ :=
  ∑ j, ((a j / 2 : ℝ) : ℂ) * ((z - y j)⁻¹ - z⁻¹)

def pointExteriorLogCorrection {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℂ :=
  ∑ j, ((a j / 2 : ℝ) : ℂ) * Complex.log (1 - y j / z)

def pointExteriorPhaseCorrection {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) : ℝ :=
  (pointExteriorLogCorrection a y z).im

theorem pointExteriorConnectionError_eq {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) :
    pointExteriorConnectionError a y z =
      pointConformalConnection a y z - (pointExteriorHalfMass a : ℂ) / z := by
  rw [pointConformalConnection_eq_reciprocal_sum]
  unfold pointExteriorConnectionError pointExteriorHalfMass
  push_cast
  rw [Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  simp only [div_eq_mul_inv]
  ring

theorem pointExterior_norm_div_le_half {y z : ℂ} (hz : 0 < ‖z‖)
    (hy : 2 * ‖y‖ ≤ ‖z‖) : ‖y / z‖ ≤ 1 / 2 := by
  rw [norm_div, div_le_iff₀ hz]
  linarith

theorem pointExterior_sub_ne_zero {y z : ℂ} (hz : 0 < ‖z‖)
    (hy : 2 * ‖y‖ ≤ ‖z‖) : z - y ≠ 0 := by
  have h := norm_sub_norm_le z y
  apply norm_pos_iff.mp
  nlinarith [norm_nonneg y]

theorem pointExterior_norm_inv_sub_inv_le {y z : ℂ} (hz : 0 < ‖z‖)
    (hy : 2 * ‖y‖ ≤ ‖z‖) :
    ‖(z - y)⁻¹ - z⁻¹‖ ≤ 2 * ‖y‖ / ‖z‖ ^ 2 := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp hz
  have hzy : z - y ≠ 0 := pointExterior_sub_ne_zero hz hy
  have halg : (z - y)⁻¹ - z⁻¹ = y / ((z - y) * z) := by
    field_simp [hz0, hzy]
    <;> ring
  have hsub : ‖z‖ / 2 ≤ ‖z - y‖ := by
    have h := norm_sub_norm_le z y
    linarith
  rw [halg, norm_div, norm_mul]
  calc
    ‖y‖ / (‖z - y‖ * ‖z‖) ≤ ‖y‖ / ((‖z‖ / 2) * ‖z‖) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
        (mul_le_mul_of_nonneg_right hsub hz.le)
    _ = 2 * ‖y‖ / ‖z‖ ^ 2 := by field_simp [ne_of_gt hz] <;> ring

theorem norm_pointExteriorConnectionError_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : 0 < ‖z‖) (hy : ∀ j, 2 * ‖y j‖ ≤ ‖z‖) :
    ‖pointExteriorConnectionError a y z‖ ≤ pointExteriorMoment a y / ‖z‖ ^ 2 := by
  calc
    ‖pointExteriorConnectionError a y z‖ ≤
        ∑ j, ‖((a j / 2 : ℝ) : ℂ) * ((z - y j)⁻¹ - z⁻¹)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, (a j / 2) * (2 * ‖y j‖ / ‖z‖ ^ 2) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (ha j) (by norm_num))]
      exact mul_le_mul_of_nonneg_left
        (pointExterior_norm_inv_sub_inv_le hz (hy j)) (div_nonneg (ha j) (by norm_num))
    _ = pointExteriorMoment a y / ‖z‖ ^ 2 := by
      unfold pointExteriorMoment
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- This is a bound for the actual logarithmic gradient. Conjugating the
existing connection identifies it with `(1/2) • pointLogForce`, the vector in
`hasFDerivAt_pointConformalLog`. -/
theorem norm_pointExterior_actual_gradient_error_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : 0 < ‖z‖) (hy : ∀ j, 2 * ‖y j‖ ≤ ‖z‖) :
    ‖(1 / 2 : ℝ) • pointLogForce a y z -
      conj ((pointExteriorHalfMass a : ℂ) / z)‖ ≤
      pointExteriorMoment a y / ‖z‖ ^ 2 := by
  calc
    ‖(1 / 2 : ℝ) • pointLogForce a y z -
        conj ((pointExteriorHalfMass a : ℂ) / z)‖ =
        ‖conj (pointExteriorConnectionError a y z)‖ := by
      rw [pointExteriorConnectionError_eq]
      simp only [map_sub, pointConformalConnection, Complex.conj_conj]
    _ = ‖pointExteriorConnectionError a y z‖ := Complex.norm_conj _
    _ ≤ pointExteriorMoment a y / ‖z‖ ^ 2 :=
      norm_pointExteriorConnectionError_le ha y hz hy

theorem pointExterior_log_argument_mem_slitPlane {y z : ℂ} (hz : 0 < ‖z‖)
    (hy : 2 * ‖y‖ ≤ ‖z‖) : 1 - y / z ∈ Complex.slitPlane := by
  have h : ‖-(y / z)‖ < 1 := by
    rw [norm_neg]
    exact (pointExterior_norm_div_le_half hz hy).trans_lt (by norm_num)
  simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one h

theorem pointExterior_norm_log_factor_le {y z : ℂ} (hz : 0 < ‖z‖)
    (hy : 2 * ‖y‖ ≤ ‖z‖) :
    ‖Complex.log (1 - y / z)‖ ≤ 2 * ‖y‖ / ‖z‖ := by
  have hsmall : ‖-(y / z)‖ ≤ 1 / 2 := by
    simpa only [norm_neg] using pointExterior_norm_div_le_half hz hy
  have h := Complex.norm_log_one_add_half_le_self hsmall
  simp only [norm_neg, norm_div, ← sub_eq_add_neg] at h
  calc
    ‖Complex.log (1 - y / z)‖ ≤ (3 / 2) * (‖y‖ / ‖z‖) := h
    _ ≤ 2 * ‖y‖ / ‖z‖ := by
      have hn : 0 ≤ ‖y‖ / ‖z‖ := div_nonneg (norm_nonneg _) hz.le
      rw [mul_div_assoc]
      nlinarith

theorem norm_pointExteriorLogCorrection_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : 0 < ‖z‖) (hy : ∀ j, 2 * ‖y j‖ ≤ ‖z‖) :
    ‖pointExteriorLogCorrection a y z‖ ≤ pointExteriorMoment a y / ‖z‖ := by
  calc
    ‖pointExteriorLogCorrection a y z‖ ≤
        ∑ j, ‖((a j / 2 : ℝ) : ℂ) * Complex.log (1 - y j / z)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ j, (a j / 2) * (2 * ‖y j‖ / ‖z‖) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (div_nonneg (ha j) (by norm_num))]
      exact mul_le_mul_of_nonneg_left
        (pointExterior_norm_log_factor_le hz (hy j)) (div_nonneg (ha j) (by norm_num))
    _ = pointExteriorMoment a y / ‖z‖ := by
      unfold pointExteriorMoment
      rw [Finset.mul_sum, Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem abs_pointExteriorPhaseCorrection_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : 0 < ‖z‖) (hy : ∀ j, 2 * ‖y j‖ ≤ ‖z‖) :
    |pointExteriorPhaseCorrection a y z| ≤ pointExteriorMoment a y / ‖z‖ :=
  (Complex.abs_im_le_norm _).trans (norm_pointExteriorLogCorrection_le ha y hz hy)

theorem pointExteriorPhaseCorrection_eq_arg_sum {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) :
    pointExteriorPhaseCorrection a y z =
      ∑ j, (a j / 2) * Complex.arg (1 - y j / z) := by
  simp [pointExteriorPhaseCorrection, pointExteriorLogCorrection,
    Complex.mul_im, Complex.log_im]

theorem hasDerivAt_pointExterior_log_factor {y z : ℂ} (hz : 0 < ‖z‖)
    (hy : 2 * ‖y‖ ≤ ‖z‖) :
    HasDerivAt (fun w : ℂ => Complex.log (1 - y / w))
      ((z - y)⁻¹ - z⁻¹) z := by
  have hz0 : z ≠ 0 := norm_pos_iff.mp hz
  have hzy : z - y ≠ 0 := pointExterior_sub_ne_zero hz hy
  have hslit := pointExterior_log_argument_mem_slitPlane hz hy
  have harg : HasDerivAt (fun w : ℂ => 1 - y / w) (y / z ^ 2) z := by
    have hquot := ((hasDerivAt_const z y).fun_div (hasDerivAt_id z) hz0).const_sub 1
    simpa only [id_eq, zero_mul, mul_one, zero_sub, neg_div, neg_neg] using hquot
  have h := (Complex.hasDerivAt_log hslit).comp z harg
  have harg0 : 1 - y / z ≠ 0 := Complex.slitPlane_ne_zero hslit
  have hcoeff : (1 - y / z)⁻¹ * (y / z ^ 2) = (z - y)⁻¹ - z⁻¹ := by
    field_simp [hz0, hzy, harg0] <;> ring
  rw [hcoeff] at h
  simpa only [Function.comp_def] using h

theorem hasDerivAt_pointExteriorLogCorrection {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) {z : ℂ}
    (hz : 0 < ‖z‖) (hy : ∀ j, 2 * ‖y j‖ ≤ ‖z‖) :
    HasDerivAt (pointExteriorLogCorrection a y)
      (pointExteriorConnectionError a y z) z := by
  unfold pointExteriorLogCorrection pointExteriorConnectionError
  exact HasDerivAt.fun_sum fun j _ =>
    (hasDerivAt_pointExterior_log_factor hz (hy j)).const_mul _

end RepulsiveCoulomb
