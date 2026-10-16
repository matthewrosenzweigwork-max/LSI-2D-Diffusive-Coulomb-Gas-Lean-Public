import LeanResearch.RepulsiveCoulomb.AffineAngularTailPotential
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic

/-! Uncompiled additive successor. Convert actual angular bounds to ordinary
unit-direction bounds and pass them through actual convergent curve samples.
The explicit sine envelope and angular potential vanish at infinite radius. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

def tailSineEnvelope (A B D r : ℝ) : ℝ :=
  Real.rpow A (1 + B) / Real.rpow r (1 + B) + D / (B * r)

theorem tailSineEnvelope_continuousAt (A B D : ℝ) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (tailSineEnvelope A B D) r := by
  change ContinuousAt (fun x : ℝ =>
    Real.rpow A (1 + B) / Real.rpow x (1 + B) + D / (B * x)) r
  simp only [div_mul_eq_div_div]
  exact (continuousAt_const.div (continuousAt_id.rpow_const (Or.inl (ne_of_gt hr)))
    (ne_of_gt (Real.rpow_pos_of_pos hr _))).add
      (continuousAt_const.div continuousAt_id (ne_of_gt hr))

theorem tailSineEnvelope_tendsto_zero_atTop (A D : ℝ) {B : ℝ} (hB : 0 < B) :
    Tendsto (tailSineEnvelope A B D) atTop (𝓝 0) := by
  have hp : 0 < 1 + B := by linarith
  have h₁ : Tendsto (fun r : ℝ => Real.rpow A (1 + B) / Real.rpow r (1 + B)) atTop (𝓝 0) := by
    simpa only [Real.rpow_eq_pow] using
      (tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hp))
  have h₂ : Tendsto (fun r : ℝ => D / (B * r)) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div] using
      (tendsto_const_nhds.div_atTop tendsto_id : Tendsto (fun r : ℝ => (D / B) / r) atTop (𝓝 0))
  change Tendsto (fun r : ℝ =>
    Real.rpow A (1 + B) / Real.rpow r (1 + B) + D / (B * r)) atTop (𝓝 0)
  simpa only [zero_add] using h₁.add h₂

theorem angularTailPotential_tendsto_zero_atTop (A D : ℝ) {B : ℝ} (hB : 0 < B) :
    Tendsto (angularTailPotential A B D) atTop (𝓝 0) := by
  have hp : 0 < 1 + B := by linarith
  have h₁ : Tendsto (fun r : ℝ => Real.rpow A (1 + B) / Real.rpow r (1 + B)) atTop (𝓝 0) := by
    simpa only [Real.rpow_eq_pow] using
      (tendsto_const_nhds.div_atTop (tendsto_rpow_atTop hp))
  have h₂ : Tendsto (fun r : ℝ => (2 * D / B) / r) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  change Tendsto (fun r : ℝ => (2 / (1 + B)) *
    (Real.rpow A (1 + B) / Real.rpow r (1 + B)) + (2 * D / B) / r) atTop (𝓝 0)
  simpa only [mul_zero, zero_add] using (h₁.const_mul (2 / (1 + B))).add h₂

theorem angularTailPotential_continuousAt (A B D : ℝ) {r : ℝ} (hr : 0 < r) :
    ContinuousAt (angularTailPotential A B D) r := by
  unfold angularTailPotential
  exact ((continuousAt_const.div (continuousAt_id.rpow_const (Or.inl (ne_of_gt hr)))
    (ne_of_gt (Real.rpow_pos_of_pos hr _))).const_mul _).add
      (continuousAt_const.div continuousAt_id (ne_of_gt hr))

theorem norm_complex_angle_increment_le (x y : ℝ) :
    ‖Complex.exp ((x : ℂ) * Complex.I) - Complex.exp ((y : ℂ) * Complex.I)‖ ≤ |x - y| := by
  rw [mul_comm (x : ℂ) Complex.I, mul_comm (y : ℂ) Complex.I]
  have he : Complex.exp (Complex.I * (y : ℂ)) * Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (x : ℂ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hsub : Complex.exp (Complex.I * (x : ℂ)) - Complex.exp (Complex.I * (y : ℂ)) =
      Complex.exp (Complex.I * (y : ℂ)) * (Complex.exp (Complex.I * ((x - y : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, he]
  rw [hsub, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  simpa only [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := x - y))

theorem normalized_direction_continuousAt {z : ℂ} (hz : z ≠ 0) :
    ContinuousAt (fun w : ℂ => w / (‖w‖ : ℂ)) z := by
  exact continuousAt_id.div (Complex.continuous_ofReal.continuousAt.comp continuousAt_id.norm)
    (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz))

theorem normalized_direction_tail_bound_of_tendsto
    {z : ℕ → ℂ} {w d : ℂ} {A B D : ℝ} (hw : w ≠ 0)
    (hz : Tendsto z atTop (𝓝 w))
    (hbound : ∀ᶠ n in atTop, ‖z n / (‖z n‖ : ℂ) - d‖ ≤ angularTailPotential A B D ‖z n‖) :
    ‖w / (‖w‖ : ℂ) - d‖ ≤ angularTailPotential A B D ‖w‖ := by
  have hl := (((normalized_direction_continuousAt hw).tendsto.comp hz).sub_const d).norm
  have hr := (angularTailPotential_continuousAt A B D (norm_pos_iff.mpr hw)).tendsto.comp hz.norm
  exact le_of_tendsto_of_tendsto hl hr hbound

end RepulsiveCoulomb
