import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! A continuous, joint divided difference obtained from the actual derivative
by integration. This removes the diagonal singularity in the smooth secant
construction without an assumed extension certificate. -/
noncomputable section
open Set MeasureTheory
namespace RepulsiveCoulomb

def euclideanAverageDerivative (γ : ℝ → ℂ) (s t : ℝ) : ℂ :=
  ∫ r in (0 : ℝ)..1, deriv γ ((t - s) * r + s)

@[simp] theorem euclideanAverageDerivative_same (γ : ℝ → ℂ) (s : ℝ) :
    euclideanAverageDerivative γ s s = deriv γ s := by
  simp [euclideanAverageDerivative]

theorem euclideanAverageDerivative_continuous {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (fun p : ℝ × ℝ => euclideanAverageDerivative γ p.1 p.2) := by
  have hi : Continuous (fun p : ℝ × ℝ =>
      ∫ r in Icc (0 : ℝ) 1, deriv γ ((p.2 - p.1) * r + p.1)) :=
    continuous_parametric_integral_of_continuous
      (f := fun p : ℝ × ℝ => fun r : ℝ => deriv γ ((p.2 - p.1) * r + p.1))
      (μ := volume)
      (hγ.continuous_deriv_one.comp (by fun_prop)) isCompact_Icc
  have heq : (fun p : ℝ × ℝ => euclideanAverageDerivative γ p.1 p.2) =
      (fun p : ℝ × ℝ => ∫ r in Icc (0 : ℝ) 1,
        deriv γ ((p.2 - p.1) * r + p.1)) := by
    funext p
    rw [euclideanAverageDerivative, intervalIntegral.integral_of_le (by norm_num),
      integral_Icc_eq_integral_Ioc]
  rw [heq]
  exact hi

/-- The exact secant formula, including equal endpoints. -/
theorem euclideanAverageDerivative_smul {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (s t : ℝ) :
    (t - s) • euclideanAverageDerivative γ s t = γ t - γ s := by
  unfold euclideanAverageDerivative
  rw [intervalIntegral.smul_integral_comp_mul_add]
  simp only [mul_zero, zero_add, mul_one, sub_add_cancel]
  exact intervalIntegral.integral_deriv_of_contDiffOn_uIcc hγ.contDiffOn

theorem euclideanAverageDerivative_eq_slope {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {s t : ℝ} (hst : s ≠ t) :
    euclideanAverageDerivative γ s t = slope γ s t := by
  have hst' : t - s ≠ 0 := sub_ne_zero.mpr hst.symm
  rw [slope_def_module, ← euclideanAverageDerivative_smul hγ s t,
    inv_smul_smul₀ hst']

/-- Injectivity prevents a secant divided difference from vanishing. -/
theorem euclideanAverageDerivative_ne_zero {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {s t : ℝ} (hne : γ t ≠ γ s) : euclideanAverageDerivative γ s t ≠ 0 := by
  intro hz
  have h := euclideanAverageDerivative_smul hγ s t
  rw [hz, smul_zero] at h
  exact hne (sub_eq_zero.mp h.symm)

/-- The two periodic divided-difference charts agree after the sign reversal
on the overlap used to resolve the closing corner. -/
theorem euclideanAverageDerivative_periodic_half {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1)
    {s t : ℝ} (hst : t - s = 1 / 2) :
    euclideanAverageDerivative γ s t = -euclideanAverageDerivative γ s (t - 1) := by
  have h₁ := euclideanAverageDerivative_smul hγ s t
  have h₂ := euclideanAverageDerivative_smul hγ s (t - 1)
  rw [hp.sub_eq] at h₂
  have ht : t - 1 - s = -(1 / 2 : ℝ) := by linarith
  rw [hst] at h₁
  rw [ht, neg_smul] at h₂
  apply (smul_right_injective ℂ (show (1 / 2 : ℝ) ≠ 0 by norm_num))
  change (1 / 2 : ℝ) • euclideanAverageDerivative γ s t =
    (1 / 2 : ℝ) • -euclideanAverageDerivative γ s (t - 1)
  rw [smul_neg, h₁]
  exact h₂.symm

/-- A global continuous secant representative using the ordinary chart when
`t-s≤1/2` and the periodic chart when `t-s≥1/2`. -/
def euclideanPeriodicSecant (γ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  if p.2 - p.1 ≤ 1 / 2 then euclideanAverageDerivative γ p.1 p.2
  else -euclideanAverageDerivative γ p.1 (p.2 - 1)

theorem euclideanPeriodicSecant_continuous {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) (hp : Function.Periodic γ 1) :
    Continuous (euclideanPeriodicSecant γ) := by
  unfold euclideanPeriodicSecant
  have hc : Continuous (fun p : ℝ × ℝ => -euclideanAverageDerivative γ p.1 (p.2 - 1)) :=
    ((euclideanAverageDerivative_continuous hγ).comp
      (show Continuous (fun p : ℝ × ℝ => (p.1, p.2 - 1)) by fun_prop)).neg
  exact Continuous.if_le (euclideanAverageDerivative_continuous hγ) hc
    (continuous_snd.sub continuous_fst) continuous_const
    (fun p h => euclideanAverageDerivative_periodic_half hγ hp h)

end RepulsiveCoulomb
