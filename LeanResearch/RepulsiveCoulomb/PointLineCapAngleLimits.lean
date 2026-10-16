import LeanResearch.RepulsiveCoulomb.PointLineCapCrossingLimits
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-! Records-only, uncompiled. Full CCW width and the two literal physical
line/circle principal turns converge. No angle equality is a hypothesis. The
branch for the width is centered at pi, so the negative real axis causes no
spurious jump. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- A positive full angle below 2pi is recovered in the branch centered at pi. -/
theorem lineCap_width_from_shifted_arg {θ : ℝ} (hθ : 0 < θ) (hθ2 : θ < 2 * Real.pi) :
    θ = Real.pi + Complex.arg (-(Circle.exp θ : ℂ)) := by
  have hshift : (Circle.exp (θ - Real.pi) : ℂ) = -(Circle.exp θ : ℂ) := by
    simp only [Circle.coe_exp, Complex.ofReal_sub, sub_mul, Complex.exp_sub,
      Complex.exp_pi_mul_I, div_neg, div_one]
  rw [← hshift, Circle.arg_exp (by linarith) (by linarith)]
  ring

namespace LineCapGeometry
variable {c : ℝ → ℂ} {R : ℝ}

theorem normalized_endpoint_ratio (D : LineCapGeometry c R) :
    (c D.minus / (‖c D.minus‖ : ℂ)) / (c D.plus / (‖c D.plus‖ : ℂ)) =
      (Circle.exp (D.beta - D.alpha) : ℂ) := by
  have hp := pointCircleCapArc_polar_lift D.radius_pos D.alpha D.beta 0
  have hm := pointCircleCapArc_polar_lift D.radius_pos D.alpha D.beta 1
  simp only [mul_zero, add_zero, D.circle_zero] at hp
  simp only [mul_one, add_sub_cancel, D.circle_one] at hm
  rw [← hp, ← hm, Circle.coe_exp, Complex.ofReal_sub, sub_mul, Complex.exp_sub]

theorem width_eq_shifted_arg (D : LineCapGeometry c R) :
    D.beta - D.alpha = Real.pi + Complex.arg
      (-((c D.minus / (‖c D.minus‖ : ℂ)) / (c D.plus / (‖c D.plus‖ : ℂ)))) := by
  rw [D.normalized_endpoint_ratio]
  exact lineCap_width_from_shifted_arg (sub_pos.mpr D.angle_lt) (by linarith [D.angle_width])

theorem normalized_circle_tangent (D : LineCapGeometry c R) (t : ℝ) :
    deriv (pointCircleCapArc R D.alpha D.beta) t /
      (‖deriv (pointCircleCapArc R D.alpha D.beta) t‖ : ℂ) =
        Complex.I * (pointCircleCapArc R D.alpha D.beta t /
          (‖pointCircleCapArc R D.alpha D.beta t‖ : ℂ)) := by
  have hz : Complex.I * pointCircleCapArc R D.alpha D.beta t ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (norm_pos_iff.mp (by
      rw [pointCircleCapArc_norm D.radius_pos.le]
      exact D.radius_pos))
  rw [(hasDerivAt_pointCircleCapArc R D.alpha D.beta t).deriv,
    normalized_complex_smul_pos hz (sub_pos.mpr D.angle_lt), norm_mul,
    Complex.norm_I, one_mul, mul_div_assoc]

end LineCapGeometry

theorem lineCapFamilyAt_width_tendsto {c : ℝ → ℂ} {R₀ : ℝ}
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R)
    (hp : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)))
    (hm : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ))) :
    Tendsto (fun r => (lineCapFamilyAt C r).beta - (lineCapFamilyAt C r).alpha)
      atTop (𝓝 Real.pi) := by
  obtain ⟨hpr, hmr⟩ := lineCapFamilyAt_position_limits C hp hm
  have hquot := (hmr.div hpr (by norm_num : (1 : ℂ) ≠ 0)).neg
  have hquot' : Tendsto (fun r => -((c (lineCapFamilyAt C r).minus /
      (‖c (lineCapFamilyAt C r).minus‖ : ℂ)) /
      (c (lineCapFamilyAt C r).plus / (‖c (lineCapFamilyAt C r).plus‖ : ℂ))))
      atTop (𝓝 (1 : ℂ)) := by simpa only [Pi.div_def, div_one, neg_neg] using hquot
  have harg := (Complex.continuousAt_arg (by simp : (1 : ℂ) ∈ Complex.slitPlane)).tendsto.comp hquot'
  have hsum := harg.const_add Real.pi
  simpa only [Function.comp_def, Complex.arg_one, add_zero, ← LineCapGeometry.width_eq_shifted_arg] using hsum

/-- Positive normalizations never change a physical principal turn. The zero
cases are included, so this transport itself needs no extra regularity input. -/
theorem lineCap_arg_normalized_quotient (v u : ℂ) :
    Complex.arg ((v / (‖v‖ : ℂ)) / (u / (‖u‖ : ℂ))) = Complex.arg (v / u) := by
  by_cases hv : v = 0
  · simp [hv]
  by_cases hu : u = 0
  · simp [hu]
  have hvn : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  have hun : (‖u‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hu)
  have he : (v / (‖v‖ : ℂ)) / (u / (‖u‖ : ℂ)) =
      ((‖u‖ / ‖v‖ : ℝ) : ℂ) * (v / u) := by
    push_cast
    field_simp [hu, hun, hvn]
    <;> ring
  rw [he, Complex.arg_real_mul _ (div_pos (norm_pos_iff.mpr hu) (norm_pos_iff.mpr hv))]

/-- These are the two actual physical corner quotients of the oriented line
and its CCW closing arc; each turn tends to pi/2, with the negative-end sign
fixed by the literal incoming circle velocity. -/
theorem lineCapFamilyAt_corner_turn_limits {c : ℝ → ℂ} {R₀ : ℝ}
    (C : ∀ R : ℝ, R₀ < R → LineCapGeometry c R)
    (hp : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atTop (𝓝 (1 : ℂ)))
    (hm : Tendsto (fun t => c t / (‖c t‖ : ℂ)) atBot (𝓝 (-1 : ℂ)))
    (hvp : Tendsto (fun t => deriv c t / (‖deriv c t‖ : ℂ) -
      c t / (‖c t‖ : ℂ)) atTop (𝓝 0))
    (hvm : Tendsto (fun t => (-deriv c t) / (‖deriv c t‖ : ℂ) -
      c t / (‖c t‖ : ℂ)) atBot (𝓝 0)) :
    Tendsto (fun r => Complex.arg
      (deriv (pointCircleCapArc (lineCapLargeRadius R₀ r)
        (lineCapFamilyAt C r).alpha (lineCapFamilyAt C r).beta) 0 /
        deriv c (lineCapFamilyAt C r).plus)) atTop (𝓝 (Real.pi / 2)) ∧
    Tendsto (fun r => Complex.arg
      (deriv c (lineCapFamilyAt C r).minus /
        deriv (pointCircleCapArc (lineCapLargeRadius R₀ r)
          (lineCapFamilyAt C r).alpha (lineCapFamilyAt C r).beta) 1))
        atTop (𝓝 (Real.pi / 2)) := by
  obtain ⟨hpr, hmr⟩ := lineCapFamilyAt_position_limits C hp hm
  obtain ⟨hvpr, hvmr⟩ := lineCapFamilyAt_oriented_tangent_limits C hp hm hvp hvm
  have hcp : Tendsto (fun r =>
      deriv (pointCircleCapArc (lineCapLargeRadius R₀ r)
        (lineCapFamilyAt C r).alpha (lineCapFamilyAt C r).beta) 0 /
      (‖deriv (pointCircleCapArc (lineCapLargeRadius R₀ r)
        (lineCapFamilyAt C r).alpha (lineCapFamilyAt C r).beta) 0‖ : ℂ))
      atTop (𝓝 Complex.I) := by
    simpa only [LineCapGeometry.normalized_circle_tangent,
      LineCapGeometry.circle_zero, mul_one] using hpr.const_mul Complex.I
  have hcm : Tendsto (fun r =>
      deriv (pointCircleCapArc (lineCapLargeRadius R₀ r)
        (lineCapFamilyAt C r).alpha (lineCapFamilyAt C r).beta) 1 /
      (‖deriv (pointCircleCapArc (lineCapLargeRadius R₀ r)
        (lineCapFamilyAt C r).alpha (lineCapFamilyAt C r).beta) 1‖ : ℂ))
      atTop (𝓝 (-Complex.I)) := by
    simpa only [LineCapGeometry.normalized_circle_tangent,
      LineCapGeometry.circle_one, mul_neg_one] using hmr.const_mul Complex.I
  have hargI := (Complex.continuousAt_arg (by simp [Complex.mem_slitPlane_iff] : Complex.I ∈ Complex.slitPlane)).tendsto
  constructor
  · have h := hargI.comp (by simpa only [Pi.div_def, div_one] using hcp.div hvpr (by norm_num : (1 : ℂ) ≠ 0))
    simpa only [Function.comp_def, Pi.div_apply, lineCap_arg_normalized_quotient, Complex.arg_I] using h
  · have hquot : Tendsto (fun r =>
        (deriv c (lineCapFamilyAt C r).minus /
          (‖deriv c (lineCapFamilyAt C r).minus‖ : ℂ)) /
        (deriv (pointCircleCapArc (lineCapLargeRadius R₀ r)
          (lineCapFamilyAt C r).alpha (lineCapFamilyAt C r).beta) 1 /
        (‖deriv (pointCircleCapArc (lineCapLargeRadius R₀ r)
          (lineCapFamilyAt C r).alpha (lineCapFamilyAt C r).beta) 1‖ : ℂ)))
        atTop (𝓝 Complex.I) := by
      simpa only [Pi.div_def, div_neg, one_div, Complex.inv_I, neg_neg] using hvmr.div hcm (neg_ne_zero.mpr Complex.I_ne_zero)
    simpa only [Function.comp_def, Pi.div_apply, lineCap_arg_normalized_quotient, Complex.arg_I] using
      hargI.comp hquot

end RepulsiveCoulomb
