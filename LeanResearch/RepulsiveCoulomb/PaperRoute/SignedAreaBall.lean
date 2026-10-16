import LeanResearch.RepulsiveCoulomb.Imported.ScalarCoarea.ScalarCoarea
import Mathlib.Analysis.Complex.Basic

/-!
# Signed area on Euclidean balls

This module derives nonnegative change of variables for the actual signed real
Jacobian of an injective planar map. The analytic inputs are a Lipschitz bound
on the source ball and an almost-everywhere positive determinant of the actual
Fréchet derivative. No area identity or image-measure certificate is assumed.

The bundled ScalarCoarea theorem removes the nondifferentiability null set and
its image. We then identify the within derivative on the open ball, normalize
Euclidean Hausdorff measure to planar volume, and remove the absolute value
using positivity. Every integral remains ENNReal-valued, including for an
unbounded measurable target integrand. A separate conclusion proves finiteness
of image-ball volume and of the unweighted Jacobian integral.

The local corollaries use Euclidean Lipschitz bounds on closed balls about zero.
They apply to the same map supplied by a later consumer. This module does not
select or construct the accepted point map, prove analytic quasiconformality
implies weak quasisymmetry, or close the David--Semmes or Poincaré routes.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

namespace RepulsiveCoulomb.PaperRoute

/-- The signed real Jacobian of the actual Fréchet derivative of a planar map. -/
def signedJacobian (F : ℂ → ℂ) (x : ℂ) : ℝ :=
  (fderiv ℝ F x).toLinearMap.det

/-- The actual selected derivative gives a measurable signed Jacobian for any map. -/
@[fun_prop]
theorem measurable_signedJacobian (F : ℂ → ℂ) : Measurable (signedJacobian F) := by
  exact ContinuousLinearMap.continuous_det.measurable.comp (measurable_fderiv ℝ F)

/-- Nonnegative area transport on a ball, with a ballwise Lipschitz bound and
almost-everywhere positivity of the actual signed determinant. This holds for
all real radii, including empty balls. No target-integrability assumption is used. -/
theorem lintegral_image_ball_eq_lintegral_signedJacobian_mul
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ} {L : ℝ≥0}
    (hLip : LipschitzOnWith L F (ball c r)) (hInj : InjOn F (ball c r))
    (hJ : ∀ᵐ x ∂volume.restrict (ball c r), 0 < signedJacobian F x)
    (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y in F '' ball c r, g y ∂volume) =
      ∫⁻ x in ball c r, ENNReal.ofReal (signedJacobian F x) * g (F x) ∂volume := by
  have hFull : ∀ᵐ x ∂volume.restrict (ball c r),
      Function.Injective (fderivWithin ℝ F (ball c r) x) := by
    filter_upwards [hJ, ae_restrict_mem measurableSet_ball] with x hx hxb
    rw [fderivWithin_of_isOpen isOpen_ball hxb]
    apply LinearMap.ker_eq_bot.mp
    apply not_not.mp
    intro hker
    exact hx.ne' (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
  have hArea :=
    ProbabilityTheory.lintegral_image_eq_lintegral_normDet_fderivWithin_mul_of_lipschitzOnWith
      measurableSet_ball hLip hInj hFull g hg
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at hArea
  refine hArea.trans (lintegral_congr_ae ?_)
  filter_upwards [hJ, ae_restrict_mem measurableSet_ball] with x hx hxb
  rw [fderivWithin_of_isOpen isOpen_ball hxb, LinearMap.normDet_eq_abs_det]
  exact congrArg (fun t : ℝ => ENNReal.ofReal t * g (F x)) (abs_of_pos hx)

/-- The image volume is the nonnegative integral of the actual signed Jacobian. -/
theorem volume_image_ball_eq_lintegral_signedJacobian
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ} {L : ℝ≥0}
    (hLip : LipschitzOnWith L F (ball c r)) (hInj : InjOn F (ball c r))
    (hJ : ∀ᵐ x ∂volume.restrict (ball c r), 0 < signedJacobian F x) :
    volume (F '' ball c r) =
      ∫⁻ x in ball c r, ENNReal.ofReal (signedJacobian F x) ∂volume := by
  simpa using lintegral_image_ball_eq_lintegral_signedJacobian_mul
    hLip hInj hJ (fun _ => 1) measurable_const

/-- A ballwise Lipschitz map has finite image-ball volume; injectivity and
Jacobian regularity are not needed for this finiteness conclusion. -/
theorem volume_image_ball_lt_top_of_lipschitzOn
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ} {L : ℝ≥0}
    (hLip : LipschitzOnWith L F (ball c r)) : volume (F '' ball c r) < ⊤ := by
  have hBound := ProbabilityTheory.LipschitzOnWith.euclideanHausdorffMeasure_image_le
    hLip (Module.finrank ℝ ℂ)
  rw [InnerProductSpace.euclideanHausdorffMeasure_eq_volume] at hBound
  exact hBound.trans_lt (ENNReal.mul_lt_top (by finiteness) measure_ball_lt_top)

/-- In particular, the Jacobian integral whose equality was proved above is finite. -/
theorem lintegral_signedJacobian_ball_lt_top
    {F : ℂ → ℂ} {c : ℂ} {r : ℝ} {L : ℝ≥0}
    (hLip : LipschitzOnWith L F (ball c r)) (hInj : InjOn F (ball c r))
    (hJ : ∀ᵐ x ∂volume.restrict (ball c r), 0 < signedJacobian F x) :
    (∫⁻ x in ball c r, ENNReal.ofReal (signedJacobian F x) ∂volume) < ⊤ := by
  rw [← volume_image_ball_eq_lintegral_signedJacobian hLip hInj hJ]
  exact volume_image_ball_lt_top_of_lipschitzOn hLip

/-- Closed balls about zero suffice to obtain a Lipschitz bound on any source ball. -/
theorem exists_lipschitzOn_ball_of_closedBall
    {F : ℂ → ℂ}
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (c : ℂ) (r : ℝ) : ∃ L : ℝ≥0, LipschitzOnWith L F (ball c r) := by
  obtain ⟨L, hL⟩ := hLocal (‖c‖ + r + 1)
  refine ⟨L, hL.mono ?_⟩
  intro x hx
  rw [mem_closedBall, dist_zero_right]
  have hx' : ‖x - c‖ < r := by simpa only [mem_ball, dist_eq_norm] using hx
  calc
    ‖x‖ ≤ ‖x - c‖ + ‖c‖ := norm_le_norm_sub_add x c
    _ ≤ ‖c‖ + r + 1 := by linarith

/-- Local analytic producer in the form supplied by an actual differentiable map.
The derivative and positive signed determinant hold almost everywhere for this
same `F`; no choice of a replacement map or area-law structure is involved. -/
theorem lintegral_image_ball_eq_lintegral_signedJacobian_mul_of_locallyLipschitz
    {F : ℂ → ℂ} (hInj : Function.Injective F)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (c : ℂ) (r : ℝ) (g : ℂ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ y in F '' ball c r, g y ∂volume) =
      ∫⁻ x in ball c r, ENNReal.ofReal (signedJacobian F x) * g (F x) ∂volume := by
  obtain ⟨L, hLip⟩ := exists_lipschitzOn_ball_of_closedBall hLocal c r
  exact lintegral_image_ball_eq_lintegral_signedJacobian_mul hLip hInj.injOn
    (ae_restrict_of_ae (hRegular.mono fun _ hx => hx.2)) g hg

/-- Actual image volume and finite signed-Jacobian mass for the local map. -/
theorem volume_image_ball_eq_lintegral_signedJacobian_and_lt_top
    {F : ℂ → ℂ} (hInj : Function.Injective F)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (c : ℂ) (r : ℝ) :
    volume (F '' ball c r) =
        (∫⁻ x in ball c r, ENNReal.ofReal (signedJacobian F x) ∂volume) ∧
      (∫⁻ x in ball c r, ENNReal.ofReal (signedJacobian F x) ∂volume) < ⊤ := by
  obtain ⟨L, hLip⟩ := exists_lipschitzOn_ball_of_closedBall hLocal c r
  have hJ := ae_restrict_of_ae (s := ball c r) (hRegular.mono fun _ hx => hx.2)
  exact ⟨volume_image_ball_eq_lintegral_signedJacobian hLip hInj.injOn hJ,
    lintegral_signedJacobian_ball_lt_top hLip hInj.injOn hJ⟩

end RepulsiveCoulomb.PaperRoute
