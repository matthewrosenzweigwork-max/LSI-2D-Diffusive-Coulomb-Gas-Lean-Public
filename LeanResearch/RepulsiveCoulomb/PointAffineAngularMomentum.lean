module

public import LeanResearch.RepulsiveCoulomb.ComplexPolarLiftDerivatives
public import LeanResearch.RepulsiveCoulomb.PointGeodesicExteriorPhase
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Tactic

@[expose] public section

/-! Uncompiled additive successor. Exact radial and angular-momentum
derivatives in the original metric-affine parameter. There is no Euclidean
arclength reparameterization or inverse radius map. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem radius_hasDerivAt_polar
    {γ : ℝ → ℂ} {t θ φ : ℝ} (hγ : DifferentiableAt ℝ γ t)
    (hz : γ t ≠ 0) (hv : deriv γ t ≠ 0)
    (htangent : Complex.exp ((θ : ℂ) * Complex.I) = deriv γ t / (‖deriv γ t‖ : ℂ))
    (hradial : Complex.exp ((φ : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ)) :
    HasDerivAt (fun u => ‖γ u‖) (‖deriv γ t‖ * Real.cos (θ - φ)) t := by
  have hsq := squared_radius_hasDerivAt_polar hγ hz hv htangent hradial
  have h := hsq.sqrt (pow_ne_zero 2 (norm_ne_zero_iff.mpr hz))
  simp only [Real.sqrt_sq_eq_abs, abs_norm] at h
  have hcoeff : (2 * ‖γ t‖ * ‖deriv γ t‖ * Real.cos (θ - φ)) / (2 * ‖γ t‖) =
      ‖deriv γ t‖ * Real.cos (θ - φ) := by
    field_simp [norm_ne_zero_iff.mpr hz] <;> ring
  rw [hcoeff] at h
  exact h

theorem affine_angularMomentum_hasDerivAt
    {r ψ : ℝ → ℝ} {t p v e : ℝ} (hr : 0 < r t)
    (hrD : HasDerivAt r (v * Real.cos (ψ t)) t)
    (hψD : HasDerivAt ψ (-(p * (v / r t) * Real.sin (ψ t)) - e) t) :
    HasDerivAt (fun s => Real.rpow (r s) p * Real.sin (ψ s))
      (-(Real.rpow (r t) p * Real.cos (ψ t) * e)) t := by
  have hpow : (r t) ^ p = (r t) ^ (p - 1) * r t := by
    calc
      (r t) ^ p = (r t) ^ ((p - 1) + 1) := by congr 1; ring
      _ = (r t) ^ (p - 1) * r t := by rw [Real.rpow_add hr, Real.rpow_one]
  have h := (hrD.rpow_const (p := p) (Or.inl (ne_of_gt hr))).mul hψD.sin
  have hcoeff :
      (v * Real.cos (ψ t) * p * (r t) ^ (p - 1)) * Real.sin (ψ t) +
      (r t) ^ p * (Real.cos (ψ t) * (-(p * (v / r t) * Real.sin (ψ t)) - e)) =
      -((r t) ^ p * Real.cos (ψ t) * e) := by
    rw [hpow]
    field_simp [ne_of_gt hr] <;> ring
  rw [hcoeff] at h
  convert! h using 1 <;> simp only [Real.rpow_eq_pow, Pi.mul_apply]

theorem pointConformal_geodesic_affine_angularMomentum_hasDerivAt
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y)
    (hz : 0 < ‖γ t‖)
    {θ φ : ℝ → ℝ} (hθ : ContinuousAt θ t) (hφ : ContinuousAt φ t)
    (htangent : ∀ᶠ u in 𝓝 t, Complex.exp ((θ u : ℂ) * Complex.I) =
      deriv γ u / (‖deriv γ u‖ : ℂ))
    (hradial : ∀ᶠ u in 𝓝 t, Complex.exp ((φ u : ℂ) * Complex.I) =
      γ u / (‖γ u‖ : ℂ)) :
    HasDerivAt (fun u => Real.rpow ‖γ u‖ (1 + pointExteriorHalfMass a) * Real.sin (θ u - φ u))
      (-(Real.rpow ‖γ t‖ (1 + pointExteriorHalfMass a) * Real.cos (θ t - φ t) *
        (pointExteriorConnectionError a y (γ t) * deriv γ t).im)) t := by
  have hγD := (pointConformal_geodesic_analyticAt ha y γ hc L hgeo ht hp).differentiableAt
  have hv := pointConformal_geodesic_deriv_ne_zero ha y γ hc L hL hgeo ht hp
  have ht₀ : Complex.exp ((θ t : ℂ) * Complex.I) = deriv γ t / (‖deriv γ t‖ : ℂ) :=
    htangent.self_of_nhds
  have hr₀ : Complex.exp ((φ t : ℂ) * Complex.I) = γ t / (‖γ t‖ : ℂ) :=
    hradial.self_of_nhds
  have hrD := radius_hasDerivAt_polar hγD (norm_pos_iff.mp hz) hv ht₀ hr₀
  have hφD := continuous_radial_lift_hasDerivAt_polar hγD (norm_pos_iff.mp hz) hv
    hφ hradial ht₀
  have hθD := pointConformal_geodesic_tangent_lift_hasDerivAt
    ha y γ hc L hL hgeo ht hp hθ htangent
  have hcomplex : pointConformalConnection a y (γ t) * deriv γ t =
      (pointExteriorHalfMass a : ℂ) * (deriv γ t / γ t) +
        pointExteriorConnectionError a y (γ t) * deriv γ t := by
    rw [pointExteriorConnectionError_eq]
    simp only [div_eq_mul_inv]
    ring
  have him := congrArg Complex.im hcomplex
  simp only [Complex.add_im, Complex.im_ofReal_mul] at him
  rw [complex_div_polar_lift_im (norm_pos_iff.mp hz) hv ht₀ hr₀] at him
  have hψD : HasDerivAt (fun u => θ u - φ u)
      (-((1 + pointExteriorHalfMass a) * (‖deriv γ t‖ / ‖γ t‖) * Real.sin (θ t - φ t)) -
        (pointExteriorConnectionError a y (γ t) * deriv γ t).im) t := by
    convert! hθD.sub hφD using 1 <;> nlinarith [him]
  exact affine_angularMomentum_hasDerivAt hz hrD hψD

end RepulsiveCoulomb
