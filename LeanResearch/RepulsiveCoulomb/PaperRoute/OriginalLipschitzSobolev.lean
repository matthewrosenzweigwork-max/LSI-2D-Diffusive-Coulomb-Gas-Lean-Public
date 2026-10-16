import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalGaussianLocalGeometry
import LeanResearch.RepulsiveCoulomb.PaperRoute.LipschitzSobolevClosure

/-! The original local strong-Sobolev displays for the genuine locally-Lipschitz
class. Constants, exponent and dilation11 are unchanged from the actual new
C1 geometry producer. The extension constructs smooth approximants and passes
both centered moments and the actual physical-gradient energy to the limit. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped Topology NNReal ENNReal ContDiff
namespace RepulsiveCoulomb.PaperRoute

/-- The existing new geometry proof is valid at every center, not just zero. -/
theorem original_raw_strong_sobolev_c1_center
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (f : ℂ → ℝ) (hf : ContDiff ℝ 1 f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R,
      ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
        (2 * originalGaussianKappa Q) ∂rawPointMeasure a y) ^ (1 / originalGaussianKappa Q) ≤
      originalRawSobolevConstant Q * R ^ 2 *
        (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg fun j _ => ha j).trans hQ
  obtain ⟨_, _, _, _, _, _, hP, _⟩ := originalPoint_constants_pos hQ0
  obtain ⟨F, hμ, hD, hA, hpath, hDS, hPI2, hPI5⟩ := original_point_localGeometry ha hQ y
  have hPI : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ w in ball z r,
        ‖v w - (⨍ z' in ball z r, v z' ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
      originalPointWeakTwoConstant Q * r * Real.sqrt
        (⨍ w in ball z (2 * r), ‖gradient v w‖ ^ 2 ∂rawPointMeasure a y) := by
    intro v hv z r hr
    simpa only [Real.norm_eq_abs, PlanarDS.norm_gradient_eq_norm_fderiv] using hPI2 v hv z r hr
  exact strong_sobolev_squared_norm_of_dilation_two hD hμ hP hPI f hf c hR

/-- Only Lipschitzness on the closed outer ball is required, and its Lipschitz
constant disappears from the quantitative conclusion. -/
theorem original_raw_strong_sobolev_closedBall
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} {L : ℝ≥0} (c : ℂ) {R : ℝ} (hR : 0 < R)
    (hf : LipschitzOnWith L f (closedBall c (11 * R))) :
    (⨍ x in ball c R,
      ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
        (2 * originalGaussianKappa Q) ∂rawPointMeasure a y) ^ (1 / originalGaussianKappa Q) ≤
      originalRawSobolevConstant Q * R ^ 2 *
        (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) := by
  obtain ⟨F, hμ, hD, hA, hpath, hDS, hPI2, hPI5⟩ := original_point_localGeometry ha hQ y
  let := hμ.locallyFinite
  have hκ : 0 < originalGaussianKappa Q := zero_lt_one.trans (originalGaussianKappa_gt_one Q)
  simp_rw [PlanarDS.norm_gradient_eq_norm_fderiv]
  apply strong_sobolev_on_balls_of_lipschitzOn
    (show rawPointMeasure a y ≪ volume from withDensity_absolutelyContinuous _ _)
    (by positivity : 0 ≤ 2 * originalGaussianKappa Q)
    (by positivity : 0 ≤ 1 / originalGaussianKappa Q) c (by linarith : R ≤ 11 * R) _ hf
  intro g hg
  simpa only [PlanarDS.norm_gradient_eq_norm_fderiv] using
    original_raw_strong_sobolev_c1_center ha hQ y g hg c hR

/-- Original raw strong Sobolev, arbitrary center and globally locally-Lipschitz
f, with exactly the same constants and dilation as the smooth producer. -/
theorem original_raw_strong_sobolev_locallyLipschitz
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : LocallyLipschitz f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R,
      ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
        (2 * originalGaussianKappa Q) ∂rawPointMeasure a y) ^ (1 / originalGaussianKappa Q) ≤
      originalRawSobolevConstant Q * R ^ 2 *
        (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) := by
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall c (11 * R)) hf.locallyLipschitzOn
  exact original_raw_strong_sobolev_closedBall ha hQ y c hR hL

/-- The manuscript's unsquared raw display, with C_Q equal to the square
root of the already fixed squared Sobolev constant. -/
theorem original_raw_local_sobolev_locallyLipschitz
    {Q : ℝ} {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : LocallyLipschitz f) (c : ℂ) {R : ℝ} (hR : 0 < R) :
    (⨍ x in ball c R,
      ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
        (2 * originalGaussianKappa Q) ∂rawPointMeasure a y) ^ (1 / (2 * originalGaussianKappa Q)) ≤
      Real.sqrt (originalRawSobolevConstant Q) * R *
        Real.sqrt (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) := by
  have hS := originalRawSobolevConstant_pos ((Finset.sum_nonneg fun j _ => ha j).trans hQ)
  have hs := original_raw_strong_sobolev_locallyLipschitz ha hQ y hf c hR
  have hs' : (⨍ x in ball c R,
      ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ ^
        (2 * originalGaussianKappa Q) ∂rawPointMeasure a y) ^ (1 / originalGaussianKappa Q) ≤
      originalRawSobolevConstant Q * Real.exp 0 * R ^ 2 *
        (⨍ x in ball c (11 * R), ‖gradient f x‖ ^ 2 ∂rawPointMeasure a y) := by
    simpa only [Real.exp_zero, mul_one] using hs
  simpa only [zero_div, Real.exp_zero, mul_one] using gaussian_sobolev_sqrt
    (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hS.le hR.le hs'

/-- The Gaussian squared estimate has the identical unnormalized coefficient
as its actual smooth counterpart. -/
theorem original_gaussian_strong_sobolev_closedBall
    {Q γ : ℝ} {m : ℕ} (hγ : 0 < γ) {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j)
    (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} {L : ℝ≥0} {R : ℝ} (hR : 0 < R)
    (hf : LipschitzOnWith L f (closedBall (0 : ℂ) (11 * R))) :
    (⨍ x in ball (0 : ℂ) R,
      ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
        (2 * originalGaussianKappa Q) ∂pointMeasure γ a y) ^ (1 / originalGaussianKappa Q) ≤
      (gaussianSobolevFactor (originalGaussianKappa Q) (originalRawSobolevConstant Q) *
        Real.exp (61 * γ * R ^ 2) * R ^ 2) *
        (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) := by
  let := pointMeasure_isProbability hγ ha y
  have hκ := originalGaussianKappa_gt_one Q
  have hκ0 : 0 < originalGaussianKappa Q := zero_lt_one.trans hκ
  have hS := originalRawSobolevConstant_pos ((Finset.sum_nonneg fun j _ => ha j).trans hQ)
  have hac : pointMeasure γ a y ≪ volume :=
    Measure.smul_absolutelyContinuous.trans (withDensity_absolutelyContinuous _ _)
  simp_rw [PlanarDS.norm_gradient_eq_norm_fderiv]
  apply strong_sobolev_on_balls_of_lipschitzOn hac
    (by positivity : 0 ≤ 2 * originalGaussianKappa Q)
    (by positivity : 0 ≤ 1 / originalGaussianKappa Q) 0 (by linarith : R ≤ 11 * R) _ hf
  intro g hg
  simpa only [PlanarDS.norm_gradient_eq_norm_fderiv] using
    gaussian_strong_sobolev_squared_norm hγ ha hκ hS y
      (original_uniform_raw_strong_sobolev Q m a ha y hQ) g hg hR

/-- Literal Gaussian strong-Sobolev display for every locally-Lipschitz f.
The constants, exponent and radius11 are the same pre-existing choices. -/
theorem original_gaussian_local_sobolev_locallyLipschitz
    {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {f : ℂ → ℝ} (hf : LocallyLipschitz f) {R : ℝ} (hR : 1 ≤ R) :
    (⨍ x in ball (0 : ℂ) R,
      ‖f x - (⨍ z in ball (0 : ℂ) R, f z ∂pointMeasure γ a y)‖ ^
        (2 * originalGaussianKappa Q) ∂pointMeasure γ a y) ^
          (1 / (2 * originalGaussianKappa Q)) ≤
      gaussianLocalConstant γ (originalGaussianKappa Q) (originalRawSobolevConstant Q) *
        Real.exp (gaussianLocalConstant γ (originalGaussianKappa Q)
          (originalRawSobolevConstant Q) * R ^ 2) * R *
        Real.sqrt (⨍ x in ball (0 : ℂ) (11 * R), ‖gradient f x‖ ^ 2 ∂pointMeasure γ a y) := by
  obtain ⟨L, hL⟩ := LocallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_closedBall (0 : ℂ) (11 * R)) hf.locallyLipschitzOn
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hS := originalRawSobolevConstant_pos ((Finset.sum_nonneg fun j _ => ha j).trans hQ)
  have hs := original_gaussian_strong_sobolev_closedBall hγ ha hQ y hR0 hL
  have h := gaussian_sobolev_sqrt
    (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _))
    (gaussianSobolevFactor_pos (originalGaussianKappa Q) hS).le hR0.le hs
  have hC := gaussianLocalConstant_pos hγ (originalGaussianKappa Q) (originalRawSobolevConstant Q)
  have hcf : Real.sqrt (gaussianSobolevFactor (originalGaussianKappa Q) (originalRawSobolevConstant Q)) ≤
      gaussianLocalConstant γ (originalGaussianKappa Q) (originalRawSobolevConstant Q) := by
    unfold gaussianLocalConstant
    linarith
  have hce : 61 * γ / 2 ≤ gaussianLocalConstant γ (originalGaussianKappa Q) (originalRawSobolevConstant Q) := by
    unfold gaussianLocalConstant
    have := Real.sqrt_nonneg (gaussianSobolevFactor (originalGaussianKappa Q) (originalRawSobolevConstant Q))
    linarith
  have he : Real.exp (61 * γ * R ^ 2 / 2) ≤
      Real.exp (gaussianLocalConstant γ (originalGaussianKappa Q) (originalRawSobolevConstant Q) * R ^ 2) :=
    Real.exp_le_exp.mpr (by nlinarith [mul_le_mul_of_nonneg_right hce (sq_nonneg R)])
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul hcf he (Real.exp_pos _).le hC.le) hR0.le)
    (Real.sqrt_nonneg _))

end RepulsiveCoulomb.PaperRoute
