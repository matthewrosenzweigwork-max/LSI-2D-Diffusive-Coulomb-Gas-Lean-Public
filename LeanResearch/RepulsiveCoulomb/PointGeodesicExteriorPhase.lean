import LeanResearch.RepulsiveCoulomb.PointGeodesicAcceleration
import LeanResearch.RepulsiveCoulomb.PointExteriorConnectionEstimates
import LeanResearch.RepulsiveCoulomb.JordanTurnAngleLift
import Mathlib.Tactic

/-!
UNCOMPILED ADDITIVE DRAFT, 2026-10-02. No accepted-source or inventory claim.

Actual exterior phase derivative and actual angle-lift construction on compact
interior subsegments. The tangent derivative comes from the proved chart-based
acceleration equation, and the correction is the literal principal-log sum.
No conserved-phase identity or continuously branching ray family is assumed.
-/

noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology ComplexConjugate

namespace RepulsiveCoulomb

theorem hasDerivAt_pointExteriorPhaseCorrection_comp
    {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) {γ : ℝ → ℂ} {t : ℝ}
    (hγ : DifferentiableAt ℝ γ t) (hz : 0 < ‖γ t‖)
    (hy : ∀ j, 2 * ‖y j‖ ≤ ‖γ t‖) :
    HasDerivAt (fun u => pointExteriorPhaseCorrection a y (γ u))
      (pointExteriorConnectionError a y (γ t) * deriv γ t).im t := by
  have h := (hasDerivAt_pointExteriorLogCorrection a y hz hy).comp t hγ.hasDerivAt
  convert! Complex.imCLM.hasFDerivAt.comp_hasDerivAt t h using 1 <;>
    simp [pointExteriorPhaseCorrection, Function.comp_def]

/-- The derivative of the actual total phase vanishes. Neither of the two
angle lifts is required to be monotone. -/
theorem pointConformal_geodesic_exterior_total_phase_hasDerivAt_zero
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y)
    (hz : 0 < ‖γ t‖) (hy : ∀ j, 2 * ‖y j‖ ≤ ‖γ t‖)
    {θ φ : ℝ → ℝ} (hθ : ContinuousAt θ t) (hφ : ContinuousAt φ t)
    (htangent : ∀ᶠ u in 𝓝 t, Complex.exp ((θ u : ℂ) * Complex.I) =
      deriv γ u / (‖deriv γ u‖ : ℂ))
    (hradial : ∀ᶠ u in 𝓝 t, Complex.exp ((φ u : ℂ) * Complex.I) =
      γ u / (‖γ u‖ : ℂ)) :
    HasDerivAt (fun u => θ u + pointExteriorHalfMass a * φ u +
      pointExteriorPhaseCorrection a y (γ u)) 0 t := by
  have hγ := (pointConformal_geodesic_analyticAt ha y γ hc L hgeo ht hp).differentiableAt
  have hθD := pointConformal_geodesic_tangent_lift_hasDerivAt
    ha y γ hc L hL hgeo ht hp hθ htangent
  have hφD := hasDerivAt_continuous_argument_lift hγ (norm_pos_iff.mp hz) hφ hradial
  have hδD := hasDerivAt_pointExteriorPhaseCorrection_comp a y hγ hz hy
  have hsum := (hθD.add (hφD.const_mul (pointExteriorHalfMass a))).add hδD
  have hcomplex : pointConformalConnection a y (γ t) * deriv γ t =
      (pointExteriorHalfMass a : ℂ) * (deriv γ t / γ t) +
        pointExteriorConnectionError a y (γ t) * deriv γ t := by
    rw [pointExteriorConnectionError_eq]
    simp only [div_eq_mul_inv]
    ring
  have him := congrArg Complex.im hcomplex
  simp only [Complex.add_im, Complex.im_ofReal_mul] at him
  convert hsum using 1
  linarith

/-- Both angle lifts are constructed on every actual regular compact interior
subsegment. The parameter is normalized only for the covering-map interface;
the tangent vector is the original metric-affine velocity. -/
theorem exists_pointConformal_geodesic_subsegment_angle_lifts
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {s u : ℝ} (hs : 0 < s) (hsu : s < u) (hu : u < 1)
    (havoid : ∀ v ∈ Icc s u, γ v ∉ pointPunctures a y)
    (hnonzero : ∀ v ∈ Icc s u, γ v ≠ 0) :
    ∃ θ φ : Icc (0 : ℝ) 1 → ℝ, Continuous θ ∧ Continuous φ ∧
      ∀ v : Icc (0 : ℝ) 1,
        Complex.exp ((θ v : ℂ) * Complex.I) =
          deriv γ (s + (u - s) * v) / (‖deriv γ (s + (u - s) * v)‖ : ℂ) ∧
        Complex.exp ((φ v : ℂ) * Complex.I) =
          γ (s + (u - s) * v) / (‖γ (s + (u - s) * v)‖ : ℂ) := by
  let τ : Icc (0 : ℝ) 1 → ℝ := fun v => s + (u - s) * v
  have hτ : Continuous τ := by fun_prop
  have hτmem (v : Icc (0 : ℝ) 1) : τ v ∈ Icc s u := by
    dsimp [τ]
    constructor <;> nlinarith [v.2.1, v.2.2]
  have h01 (v : ℝ) (hv : v ∈ Icc s u) : v ∈ Ioo (0 : ℝ) 1 :=
    ⟨hs.trans_le hv.1, hv.2.trans_lt hu⟩
  have hvelC : ContinuousOn (deriv γ) (Icc s u) := by
    intro v hv
    exact (pointConformal_geodesic_hasDerivAt_deriv
      ha y γ hc L hL hgeo (h01 v hv) (havoid v hv)).continuousAt.continuousWithinAt
  have hvelN (v : Icc (0 : ℝ) 1) : deriv γ (τ v) ≠ 0 :=
    pointConformal_geodesic_deriv_ne_zero ha y γ hc L hL hgeo
      (h01 _ (hτmem v)) (havoid _ (hτmem v))
  obtain ⟨θ, hθ, hθlift⟩ := exists_interval_euclidean_angle_lift
    (hvelC.comp_continuous hτ hτmem) hvelN
  obtain ⟨φ, hφ, hφlift⟩ := exists_interval_euclidean_angle_lift
    (hc.comp hτ) (fun v => hnonzero _ (hτmem v))
  exact ⟨θ, φ, hθ, hφ, fun v => ⟨hθlift v, hφlift v⟩⟩

end RepulsiveCoulomb
