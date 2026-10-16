import LeanResearch.RepulsiveCoulomb.PointGeodesicClockDifferentiable
import LeanResearch.RepulsiveCoulomb.PointGeodesicAnalytic
import LeanResearch.RepulsiveCoulomb.PointArgumentLiftDerivative
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Tactic

/-!
UNCOMPILED ADDITIVE DRAFT, 2026-10-02. No accepted-source or inventory claim.

Actual affine-parameter acceleration for a point-conformal minimizing segment.
The second-order equation is derived from the constructed holomorphic developing
chart. It is not an input hypothesis. In particular the older parallel-phase
interface, which omitted holomorphic differentiability of H, is not used.
-/

noncomputable section
open Set Metric Filter InnerProductSpace
open scoped Topology ComplexConjugate

namespace RepulsiveCoulomb

theorem pointConformal_geodesic_hasDerivAt_deriv {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ) (hc : Continuous γ)
    (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y) :
    HasDerivAt (deriv γ)
      (-(pointConformalConnection a y (γ t) * (deriv γ t) ^ 2)) t := by
  obtain ⟨e, H, A, B, hB, hep, hHA, he, hflat⟩ :=
    exists_pointConformal_geodesic_phase_affine_development ha y γ hc L hL hgeo ht hp
  have hγA := pointConformal_geodesic_analyticAt ha y γ hc L hgeo ht hp
  have heq : (e ∘ γ) =ᶠ[𝓝 t] (fun v : ℝ => A + (v : ℂ) * B) :=
    hflat.mono fun _ hv => hv.2
  have hparallel : ∀ᶠ v in 𝓝 t,
      Complex.exp (H (γ v)) * deriv γ v = B := by
    filter_upwards [hflat, heq.eventually_nhds, hγA.eventually_analyticAt]
      with v hsrc heqv hγv
    have hcomp : deriv (e ∘ γ) v = Complex.exp (H (γ v)) * deriv γ v := by
      have hed := (he _ hsrc.1).1.differentiableAt
      rw [fderiv_comp_deriv v (hed.restrictScalars ℝ) hγv.differentiableAt,
        hed.fderiv_restrictScalars (𝕜 := ℝ)]
      change (fderiv ℂ e (γ v)) (deriv γ v) = _
      simp only [fderiv_eq_smul_deriv, (he _ hsrc.1).2.1, smul_eq_mul]
      ring
    have hline : HasDerivAt (fun r : ℝ => A + (r : ℂ) * B) B v := by
      simpa using ((hasDerivAt_id v).ofReal_comp.mul_const B).const_add A
    have heqv' : (e ∘ γ) =ᶠ[𝓝 v] (fun r : ℝ => A + (r : ℂ) * B) := heqv
    rw [← hcomp, heqv'.deriv_eq, hline.deriv]
  have hvelocity : deriv γ =ᶠ[𝓝 t] (fun v => Complex.exp (-H (γ v)) * B) := by
    filter_upwards [hparallel] with v hv
    rw [← hv, Complex.exp_neg, ← mul_assoc,
      inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]
  have hG : HasDerivAt (H ∘ γ)
      (pointConformalConnection a y (γ t) * deriv γ t) t := by
    have h := (hHA _ hep).differentiableAt.hasDerivAt.comp t hγA.differentiableAt.hasDerivAt
    rwa [(he _ hep).2.2.2] at h
  have hcalc := hG.neg.cexp.mul_const B
  change HasDerivAt (fun v => Complex.exp (-H (γ v)) * B)
    (Complex.exp (-H (γ t)) *
      (-(pointConformalConnection a y (γ t) * deriv γ t)) * B) t at hcalc
  have hcoeff : Complex.exp (-H (γ t)) *
      (-(pointConformalConnection a y (γ t) * deriv γ t)) * B =
      -(pointConformalConnection a y (γ t) * (deriv γ t) ^ 2) := by
    calc
      _ = -(pointConformalConnection a y (γ t) * deriv γ t) *
          (Complex.exp (-H (γ t)) * B) := by ring
      _ = _ := by
        have hvelocityt : deriv γ t = Complex.exp (-H (γ t)) * B := hvelocity.self_of_nhds
        rw [← hvelocityt]
        ring
  rw [hcoeff] at hcalc
  exact hcalc.congr_of_eventuallyEq hvelocity

theorem pointConformal_geodesic_deriv_ne_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ) (hc : Continuous γ)
    (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y) :
    deriv γ t ≠ 0 := by
  intro hzero
  have h := pointConformal_geodesic_physical_speed ha y γ hc L hgeo ht hp
  rw [hzero, norm_zero, mul_zero] at h
  linarith

/-- A genuine continuous tangent-angle lift has the actual connection turn
derivative. Lift existence is supplied independently by the covering-space
angle-lift lemmas, not by this differentiation adapter. -/
theorem pointConformal_geodesic_tangent_lift_hasDerivAt
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hc : Continuous γ) (L : ℝ) (hL : 0 < L)
    (hgeo : ∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hp : γ t ∉ pointPunctures a y)
    {θ : ℝ → ℝ} (hθ : ContinuousAt θ t)
    (hlift : ∀ᶠ v in 𝓝 t, Complex.exp ((θ v : ℂ) * Complex.I) =
      deriv γ v / (‖deriv γ v‖ : ℂ)) :
    HasDerivAt θ (-(pointConformalConnection a y (γ t) * deriv γ t).im) t := by
  have hacc := pointConformal_geodesic_hasDerivAt_deriv ha y γ hc L hL hgeo ht hp
  have hvel := pointConformal_geodesic_deriv_ne_zero ha y γ hc L hL hgeo ht hp
  have h := hasDerivAt_continuous_argument_lift hacc.differentiableAt hvel hθ hlift
  rw [hacc.deriv] at h
  have heq : -(pointConformalConnection a y (γ t) * (deriv γ t) ^ 2) /
      deriv γ t = -(pointConformalConnection a y (γ t) * deriv γ t) := by
    field_simp [hvel]
  simpa only [heq, Complex.neg_im] using h

end RepulsiveCoulomb
