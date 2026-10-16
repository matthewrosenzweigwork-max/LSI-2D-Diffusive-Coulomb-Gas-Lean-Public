module

public import LeanResearch.RepulsiveCoulomb.PointRadialSectorTopology
public import LeanResearch.RepulsiveCoulomb.JordanAffineTraceTangent
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! The literal positively traversed circle cap, its actual derivative,
regularity, and full tangent increment. No tangent-turn value is supplied as
a certificate. The angular width need not be less than a semicircle. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointCircleCapArc (R α β t : ℝ) : ℂ :=
  pointRadialSectorPoint R (α + (β - α) * t)

theorem pointCircleCapArc_norm {R : ℝ} (hR : 0 ≤ R) (α β t : ℝ) :
    ‖pointCircleCapArc R α β t‖ = R := pointRadialSectorPoint_norm hR _

theorem pointCircleCapArc_smooth (R α β : ℝ) : ContDiff ℝ 1 (pointCircleCapArc R α β) := by
  unfold pointCircleCapArc pointRadialSectorPoint
  simp only [Circle.coe_exp]
  have hlin : ContDiff ℝ 1 (fun t : ℝ => α + (β - α) * t) := by fun_prop
  have hc : ContDiff ℝ 1 (fun t : ℝ => ((α + (β - α) * t : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hlin
  exact contDiff_const.mul ((hc.mul contDiff_const).cexp)

theorem hasDerivAt_pointCircleCapArc (R α β t : ℝ) :
    HasDerivAt (pointCircleCapArc R α β)
      ((β - α) • (Complex.I * pointCircleCapArc R α β t)) t := by
  have hp : HasDerivAt (fun s : ℝ => ((α + (β - α) * s : ℝ) : ℂ) * Complex.I)
      (((β - α : ℝ) : ℂ) * Complex.I) t := by
    convert! (((hasDerivAt_id t).const_mul (β - α)).const_add α).ofReal_comp.mul_const Complex.I using 1 <;>
      simp
  convert! hp.cexp.const_mul (R : ℂ) using 1 <;>
    simp only [pointCircleCapArc, pointRadialSectorPoint, Circle.coe_exp, Complex.real_smul] <;> ring

theorem pointCircleCapArc_regular {R α β : ℝ} (hR : 0 < R) (hαβ : α < β) (t : ℝ) :
    deriv (pointCircleCapArc R α β) t ≠ 0 := by
  rw [(hasDerivAt_pointCircleCapArc R α β t).deriv, Complex.real_smul]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (sub_pos.mpr hαβ).ne')
    (mul_ne_zero Complex.I_ne_zero (norm_pos_iff.mp (by rw [pointCircleCapArc_norm hR.le]; exact hR)))

theorem pointCircleCapArc_polar_lift {R : ℝ} (hR : 0 < R) (α β t : ℝ) :
    Complex.exp (((α + (β - α) * t : ℝ) : ℂ) * Complex.I) =
      pointCircleCapArc R α β t / (‖pointCircleCapArc R α β t‖ : ℂ) := by
  rw [pointCircleCapArc_norm hR.le]
  simp only [pointCircleCapArc, pointRadialSectorPoint, Circle.coe_exp]
  field_simp [Complex.ofReal_ne_zero.mpr hR.ne'] <;> ring

theorem pointCircleCapArc_tangent_lift {R α β : ℝ} (hR : 0 < R) (hαβ : α < β) (t : ℝ) :
    Complex.exp (((α + (β - α) * t + Real.pi / 2 : ℝ) : ℂ) * Complex.I) =
      deriv (pointCircleCapArc R α β) t / (‖deriv (pointCircleCapArc R α β) t‖ : ℂ) := by
  have hz : Complex.I * pointCircleCapArc R α β t ≠ 0 := mul_ne_zero Complex.I_ne_zero
    (norm_pos_iff.mp (by rw [pointCircleCapArc_norm hR.le]; exact hR))
  rw [(hasDerivAt_pointCircleCapArc R α β t).deriv,
    normalized_complex_smul_pos hz (sub_pos.mpr hαβ), norm_mul, Complex.norm_I, one_mul,
    mul_div_assoc, ← pointCircleCapArc_polar_lift hR α β t]
  push_cast
  rw [add_mul, Complex.exp_add, Complex.exp_pi_div_two_mul_I]
  ring

/-- Every actual continuous tangent lift of the positive circle has its
full angular increment β−α, with no principal-value truncation. -/
theorem pointCircleCapArc_tangent_increment {R α β : ℝ} (hR : 0 < R) (hαβ : α < β)
    (τ : Icc (0 : ℝ) 1 → ℝ) (hτ : Continuous τ)
    (hτl : ∀ t, Complex.exp ((τ t : ℂ) * Complex.I) =
      deriv (pointCircleCapArc R α β) t / (‖deriv (pointCircleCapArc R α β) t‖ : ℂ)) :
    τ 1 - τ 0 = β - α := by
  have hc : Continuous (fun t : Icc (0 : ℝ) 1 => α + (β - α) * t.1 + Real.pi / 2) := by fun_prop
  have hi := euclidean_angle_lift_increment_eq hτ hc
    (fun t => Circle.ext ((hτl t).trans (pointCircleCapArc_tangent_lift hR hαβ t).symm))
    (0 : Icc (0 : ℝ) 1) 1
  simpa using hi

end RepulsiveCoulomb
