import LeanResearch.RepulsiveCoulomb.PointArgumentLiftDerivative
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Tactic

/-! Uncompiled additive draft. Actual polar identities for radial and tangent
lifts, without changing the metric-affine curve parameter. -/
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology ComplexConjugate RealInnerProductSpace
namespace RepulsiveCoulomb

theorem complex_div_eq_polar_lift {z v : ℂ} {θ φ : ℝ} (hz : z ≠ 0) (hv : v ≠ 0)
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) = v / (‖v‖ : ℂ))
    (hφ : Complex.exp ((φ : ℂ) * Complex.I) = z / (‖z‖ : ℂ)) :
    v / z = ((‖v‖ / ‖z‖ : ℝ) : ℂ) *
      Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) := by
  have hzn : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hvn : (‖v‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)
  calc
    v / z = ((‖v‖ / ‖z‖ : ℝ) : ℂ) *
        ((v / (‖v‖ : ℂ)) / (z / (‖z‖ : ℂ))) := by
      push_cast
      field_simp [hz, hzn, hvn]
    _ = ((‖v‖ / ‖z‖ : ℝ) : ℂ) *
        (Complex.exp ((θ : ℂ) * Complex.I) / Complex.exp ((φ : ℂ) * Complex.I)) := by
      rw [hθ, hφ]
    _ = _ := by
      rw [← Complex.exp_sub]
      congr 2
      push_cast
      ring

theorem complex_div_polar_lift_im {z v : ℂ} {θ φ : ℝ} (hz : z ≠ 0) (hv : v ≠ 0)
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) = v / (‖v‖ : ℂ))
    (hφ : Complex.exp ((φ : ℂ) * Complex.I) = z / (‖z‖ : ℂ)) :
    (v / z).im = (‖v‖ / ‖z‖) * Real.sin (θ - φ) := by
  rw [complex_div_eq_polar_lift hz hv hθ hφ,
    Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem complex_div_polar_lift_re {z v : ℂ} {θ φ : ℝ} (hz : z ≠ 0) (hv : v ≠ 0)
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) = v / (‖v‖ : ℂ))
    (hφ : Complex.exp ((φ : ℂ) * Complex.I) = z / (‖z‖ : ℂ)) :
    (v / z).re = (‖v‖ / ‖z‖) * Real.cos (θ - φ) := by
  rw [complex_div_eq_polar_lift hz hv hθ hφ,
    Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem complex_real_inner_eq_norm_sq_mul_div_re {z v : ℂ} (hz : z ≠ 0) :
    ⟪z, v⟫_ℝ = ‖z‖ ^ 2 * (v / z).re := by
  have hn : Complex.normSq z ≠ 0 := ne_of_gt (Complex.normSq_pos.mpr hz)
  rw [Complex.inner, Complex.div_re, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  field_simp [hn] <;> ring

theorem complex_real_inner_polar_lifts {z v : ℂ} {θ φ : ℝ} (hz : z ≠ 0) (hv : v ≠ 0)
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) = v / (‖v‖ : ℂ))
    (hφ : Complex.exp ((φ : ℂ) * Complex.I) = z / (‖z‖ : ℂ)) :
    ⟪z, v⟫_ℝ = ‖z‖ * ‖v‖ * Real.cos (θ - φ) := by
  rw [complex_real_inner_eq_norm_sq_mul_div_re hz, complex_div_polar_lift_re hz hv hθ hφ]
  field_simp [norm_ne_zero_iff.mpr hz] <;> ring

theorem continuous_radial_lift_hasDerivAt_polar
    {γ : ℝ → ℂ} {φ : ℝ → ℝ} {t θ : ℝ}
    (hγ : DifferentiableAt ℝ γ t) (hz : γ t ≠ 0) (hv : deriv γ t ≠ 0)
    (hφ : ContinuousAt φ t)
    (hradial : ∀ᶠ u in 𝓝 t, Complex.exp ((φ u : ℂ) * Complex.I) =
      γ u / (‖γ u‖ : ℂ))
    (htangent : Complex.exp ((θ : ℂ) * Complex.I) =
      deriv γ t / (‖deriv γ t‖ : ℂ)) :
    HasDerivAt φ ((‖deriv γ t‖ / ‖γ t‖) * Real.sin (θ - φ t)) t := by
  have h := hasDerivAt_continuous_argument_lift hγ hz hφ hradial
  rwa [complex_div_polar_lift_im hz hv htangent hradial.self_of_nhds] at h

theorem squared_radius_hasDerivAt_polar
    {γ : ℝ → ℂ} {t θ φ : ℝ} (hγ : DifferentiableAt ℝ γ t)
    (hz : γ t ≠ 0) (hv : deriv γ t ≠ 0)
    (htangent : Complex.exp ((θ : ℂ) * Complex.I) =
      deriv γ t / (‖deriv γ t‖ : ℂ))
    (hradial : Complex.exp ((φ : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) :
    HasDerivAt (fun u => ‖γ u‖ ^ 2)
      (2 * ‖γ t‖ * ‖deriv γ t‖ * Real.cos (θ - φ)) t := by
  have h := hγ.hasDerivAt.norm_sq
  rw [complex_real_inner_polar_lifts hz hv htangent hradial] at h
  convert h using 1 <;> ring

end RepulsiveCoulomb
