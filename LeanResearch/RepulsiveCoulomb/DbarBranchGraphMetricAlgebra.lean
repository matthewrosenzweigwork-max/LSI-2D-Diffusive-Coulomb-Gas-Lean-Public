module

public import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel
public import Mathlib.Analysis.InnerProductSpace.Adjoint

@[expose] public section

/-! Algebraic rank-one graph metric and its explicit inverse. This module does
not identify a curvature operator, prove completeness, or assert any basic
estimate. Those analytic and geometric obligations remain separate. -/
noncomputable section
open InnerProductSpace
open scoped ComplexConjugate
namespace RepulsiveCoulomb

def dbarGraphMetric {N : ℕ} (a : CoulombConfig N) : CoulombConfig N →L[ℂ] CoulombConfig N :=
  ContinuousLinearMap.id ℂ _ + rankOne ℂ a a

def dbarGraphMetricInverse {N : ℕ} (a : CoulombConfig N) : CoulombConfig N →L[ℂ] CoulombConfig N :=
  ContinuousLinearMap.id ℂ _ - (1 + inner ℂ a a)⁻¹ • rankOne ℂ a a

theorem dbarGraphMetric_apply {N : ℕ} (a z : CoulombConfig N) :
    dbarGraphMetric a z = z + inner ℂ a z • a := rfl

theorem dbarGraphMetricInverse_apply {N : ℕ} (a z : CoulombConfig N) :
    dbarGraphMetricInverse a z = z - ((1 + inner ℂ a a)⁻¹ * inner ℂ a z) • a := by
  simp only [dbarGraphMetricInverse, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, rankOne_apply, smul_smul]

theorem dbarGraphMetric_denominator_ne_zero {N : ℕ} (a : CoulombConfig N) :
    (1 : ℂ) + inner ℂ a a ≠ 0 := by
  intro h
  have hr := congrArg Complex.re h
  change (1 : ℝ) + (inner ℂ a a).re = 0 at hr
  have ha : (inner ℂ a a).re = ‖a‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) a
  rw [ha] at hr
  nlinarith [sq_nonneg ‖a‖]

theorem dbarGraphMetricInverse_inner {N : ℕ} (a z : CoulombConfig N) :
    inner ℂ a (dbarGraphMetricInverse a z) = inner ℂ a z / (1 + inner ℂ a a) := by
  apply (eq_div_iff (dbarGraphMetric_denominator_ne_zero a)).mpr
  rw [dbarGraphMetricInverse_apply, inner_sub_right, inner_smul_right]
  calc
    _ = inner ℂ a z * (1 + inner ℂ a a) -
        ((1 + inner ℂ a a)⁻¹ * (1 + inner ℂ a a)) * (inner ℂ a z * inner ℂ a a) := by ring
    _ = _ := by rw [inv_mul_cancel₀ (dbarGraphMetric_denominator_ne_zero a)]; ring

theorem dbarGraphMetric_right_inverse {N : ℕ} (a z : CoulombConfig N) :
    dbarGraphMetric a (dbarGraphMetricInverse a z) = z := by
  rw [dbarGraphMetric_apply, dbarGraphMetricInverse_inner, dbarGraphMetricInverse_apply]
  simp only [div_eq_mul_inv, mul_comm (inner ℂ a z) (1 + inner ℂ a a)⁻¹]
  exact sub_add_cancel _ _

theorem dbarGraphMetric_left_inverse {N : ℕ} (a z : CoulombConfig N) :
    dbarGraphMetricInverse a (dbarGraphMetric a z) = z := by
  have hi : inner ℂ a (dbarGraphMetric a z) = (1 + inner ℂ a a) * inner ℂ a z := by
    rw [dbarGraphMetric_apply, inner_add_right, inner_smul_right]
    ring
  rw [dbarGraphMetricInverse_apply, hi, ← mul_assoc,
    inv_mul_cancel₀ (dbarGraphMetric_denominator_ne_zero a), one_mul, dbarGraphMetric_apply]
  exact add_sub_cancel_right _ _

theorem dbarGraphMetric_selfAdjoint_pairing {N : ℕ} (a u v : CoulombConfig N) :
    inner ℂ (dbarGraphMetric a u) v = inner ℂ u (dbarGraphMetric a v) := by
  simp only [dbarGraphMetric_apply, inner_add_left, inner_add_right, inner_smul_left,
    inner_smul_right, inner_conj_symm]
  ring

theorem dbarGraphMetric_inverse_pairing_cancel {N : ℕ} (a g : CoulombConfig N) :
    inner ℂ (dbarGraphMetricInverse a g) (dbarGraphMetric a g) = (‖g‖ ^ 2 : ℝ) := by
  rw [← dbarGraphMetric_selfAdjoint_pairing, dbarGraphMetric_right_inverse]
  apply Complex.ext
  · change (inner ℂ g g).re = ‖g‖ ^ 2
    exact inner_self_eq_norm_sq (𝕜 := ℂ) g
  · change (inner ℂ g g).im = 0
    exact inner_self_im (𝕜 := ℂ) g

theorem dbarGraphMetric_scaled_inverse_pairing_cancel {N : ℕ} (β : ℝ) (a g : CoulombConfig N) :
    (inner ℂ (dbarGraphMetricInverse a g) ((2 / β : ℝ) • dbarGraphMetric a g)).re =
      (2 / β) * ‖g‖ ^ 2 := by
  rw [inner_smul_right_eq_smul, ← dbarGraphMetric_selfAdjoint_pairing, dbarGraphMetric_right_inverse]
  rw [Complex.smul_re, smul_eq_mul]
  have hg : (inner ℂ g g).re = ‖g‖ ^ 2 := inner_self_eq_norm_sq (𝕜 := ℂ) g
  rw [hg]

end RepulsiveCoulomb
