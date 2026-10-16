import LeanResearch.RepulsiveCoulomb.PointActualOutwardTailSine
import LeanResearch.RepulsiveCoulomb.DirectionalTailLimits
import LeanResearch.RepulsiveCoulomb.CircleTransverseCorner
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-! Exact affine-parameter transport and elementary angle algebra used to apply
 the finite original-time tail estimate directly to the actual limiting line. -/
noncomputable section
open Set
open scoped RealInnerProductSpace
namespace RepulsiveCoulomb

theorem pointMetricLine_affine_segment_identity
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ) (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    (l : ℝ) {k : ℝ} (hk : 0 < k) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∀ t ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (c (l + k * s)) (c (l + k * t))).toReal =
        |t - s| * k := by
  intro s hs t ht
  rw [hd, Real.dist_eq,
    show l + k * s - (l + k * t) = k * (s - t) by ring,
    abs_mul, abs_of_pos hk, abs_sub_comm]
  ring

theorem hasDerivAt_of_positive_affine_pullback
    {c : ℝ → ℂ} {l k u : ℝ} {V : ℂ} (hk : 0 < k)
    (h : HasDerivAt (fun v => c (l + k * v)) V u) :
    HasDerivAt c (k⁻¹ • V) (l + k * u) := by
  have hinv : HasDerivAt (fun t : ℝ => (t - l) / k) k⁻¹ (l + k * u) := by
    convert ((hasDerivAt_id (l + k * u)).sub_const l).div_const k using 1 <;> simp
  have he : u = (l + k * u - l) / k := by field_simp [ne_of_gt hk]; ring
  have hh := h.scomp_of_eq (l + k * u) hinv he
  convert hh using 1
  funext t
  simp only [Function.comp_def]
  congr 1
  field_simp [ne_of_gt hk]
  ring

theorem normalized_positive_real_smul (k : ℝ) (hk : 0 < k) (v : ℂ) :
    (k • v) / (‖k • v‖ : ℂ) = v / (‖v‖ : ℂ) := by
  by_cases hv : v = 0
  · simp [hv]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_pos hk, Complex.ofReal_mul, Complex.real_smul]
    field_simp [Complex.ofReal_ne_zero.mpr (ne_of_gt hk),
      Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hv)]

theorem physicalRadialProjection_polar_lifts
    {z v : ℂ} {θ φ : ℝ} (hz : z ≠ 0) (hv : v ≠ 0)
    (hθ : Complex.exp ((θ : ℂ) * Complex.I) = v / (‖v‖ : ℂ))
    (hφ : Complex.exp ((φ : ℂ) * Complex.I) = z / (‖z‖ : ℂ)) :
    physicalRadialProjection z v = ‖z‖ * ‖v‖ * Real.cos (θ - φ) := by
  have h := complex_real_inner_polar_lifts hz hv hθ hφ
  convert h using 1
  simp [physicalRadialProjection, Complex.inner, Complex.mul_re] <;> ring

theorem norm_angle_chord_le_two_abs_sin {θ φ : ℝ} (hcos : 0 ≤ Real.cos (θ - φ)) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp ((φ : ℂ) * Complex.I)‖ ≤
      2 * |Real.sin (θ - φ)| := by
  have he : Complex.exp ((θ : ℂ) * Complex.I) - Complex.exp ((φ : ℂ) * Complex.I) =
      Complex.exp ((φ : ℂ) * Complex.I) *
        (Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, ← Complex.exp_add, mul_one]
    congr 1
    push_cast
    ring
  rw [he, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
  have hsquare : ‖Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) - 1‖ ^ 2 =
      (Real.cos (θ - φ) - 1) ^ 2 + Real.sin (θ - φ) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
      Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_zero]
    ring
  have htrig := Real.sin_sq_add_cos_sq (θ - φ)
  have hc1 := Real.cos_le_one (θ - φ)
  have hprod : 0 ≤ Real.cos (θ - φ) * (1 - Real.cos (θ - φ)) :=
    mul_nonneg hcos (sub_nonneg.mpr hc1)
  have habs := sq_abs (Real.sin (θ - φ))
  have hn := norm_nonneg (Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I) - 1)
  have ha := abs_nonneg (Real.sin (θ - φ))
  nlinarith

end RepulsiveCoulomb
