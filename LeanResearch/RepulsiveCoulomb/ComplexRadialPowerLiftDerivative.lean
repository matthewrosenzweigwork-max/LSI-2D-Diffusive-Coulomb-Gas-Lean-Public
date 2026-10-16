import LeanResearch.RepulsiveCoulomb.ComplexPolarLiftDerivatives
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic

/-! Uncompiled additive successor. The actual radial-power first derivative
is a strictly positive coefficient times the cosine of the actual tangent/radial
angle difference. The affine parameter is unchanged. -/
noncomputable section
open InnerProductSpace
namespace RepulsiveCoulomb

def radialPolarCoefficient (p : ℝ) (z v : ℂ) : ℝ :=
  2 * ‖z‖ * ‖v‖ * p * Real.rpow (‖z‖ ^ 2) (p - 1)

theorem radialPolarCoefficient_pos {p : ℝ} {z v : ℂ}
    (hp : 0 < p) (hz : z ≠ 0) (hv : v ≠ 0) : 0 < radialPolarCoefficient p z v := by
  unfold radialPolarCoefficient
  exact mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (norm_pos_iff.mpr hz))
    (norm_pos_iff.mpr hv)) hp)
    (Real.rpow_pos_of_pos (sq_pos_of_pos (norm_pos_iff.mpr hz)) _)

theorem radialPower_deriv_eq_polar
    {γ : ℝ → ℂ} {t θ φ : ℝ} (p : ℝ) (hγ : DifferentiableAt ℝ γ t)
    (hz : γ t ≠ 0) (hv : deriv γ t ≠ 0)
    (htangent : Complex.exp ((θ : ℂ) * Complex.I) = deriv γ t / (‖deriv γ t‖ : ℂ))
    (hradial : Complex.exp ((φ : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) :
    deriv (fun u => Real.rpow (‖γ u‖ ^ 2) p) t =
      radialPolarCoefficient p (γ t) (deriv γ t) * Real.cos (θ - φ) := by
  have hq := squared_radius_hasDerivAt_polar hγ hz hv htangent hradial
  have h := hq.rpow_const (p := p) (Or.inl (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)))
  have hcoeff : (2 * ‖γ t‖ * ‖deriv γ t‖ * Real.cos (θ - φ)) * p *
      (‖γ t‖ ^ 2) ^ (p - 1) =
      radialPolarCoefficient p (γ t) (deriv γ t) * Real.cos (θ - φ) := by
    simp only [radialPolarCoefficient, Real.rpow_eq_pow]
    ring
  rw [hcoeff] at h
  simpa only [Real.rpow_eq_pow] using h.deriv

end RepulsiveCoulomb
