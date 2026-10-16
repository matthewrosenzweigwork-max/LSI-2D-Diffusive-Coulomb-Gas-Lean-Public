import LeanResearch.RepulsiveCoulomb.PaperRoute.PlanarCofactorGradient
import LeanResearch.RepulsiveCoulomb.PaperRoute.SignedAreaBall
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Actual inverse-gradient transport on image balls

For the same supplied planar homeomorphism, its actual forward derivative is
converted to a continuous linear equivalence at each positive-Jacobian source
point. Continuity and the inverse identity then prove differentiability of the
actual inverse. The ordinary chain rule and the planar cofactor inequality
produce the inverse-pullback gradient bound. Signed area on the actual image
ball integrates that pointwise estimate.

The ENNReal estimate needs no integrability or measurability of the source
weight, and no inverse regularity certificate. Independent integrability of
the weighted source gradient implies target-gradient integrability and the
finite-real inequality. A C1 scalar and continuous weight discharge that
source integrability on every ball. No local inverse-Lipschitz, Sobolev,
Poincare, or David--Semmes conclusion is assumed or asserted here.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

namespace RepulsiveCoulomb.PaperRoute

/-- Nonvanishing of the actual determinant gives the actual inverse derivative.
Only continuity of the supplied inverse, rather than any inverse regularity
hypothesis, is used. -/
theorem hasFDerivAt_homeomorph_symm_of_det_ne_zero
    (F : ℂ ≃ₜ ℂ) {x : ℂ}
    (hF : HasFDerivAt F (fderiv ℝ F x) x)
    (hdet : (fderiv ℝ F x).toLinearMap.det ≠ 0) :
    HasFDerivAt F.symm
      (((fderiv ℝ F x).toContinuousLinearEquivOfDetNeZero hdet).symm : ℂ →L[ℝ] ℂ)
      (F x) := by
  apply HasFDerivAt.of_local_left_inverse F.symm.continuous.continuousAt
  · simpa only [ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero,
      F.symm_apply_apply] using hF
  · exact Filter.Eventually.of_forall F.apply_symm_apply

/-- Differentiability of the inverse pullback is derived from the actual forward
derivative and the differentiability of the source scalar. -/
theorem differentiableAt_scalar_comp_homeomorph_symm
    (F : ℂ ≃ₜ ℂ) {f : ℂ → ℝ} {x : ℂ}
    (hF : HasFDerivAt F (fderiv ℝ F x) x)
    (hdet : (fderiv ℝ F x).toLinearMap.det ≠ 0)
    (hf : DifferentiableAt ℝ f x) :
    DifferentiableAt ℝ (f ∘ F.symm) (F x) := by
  have hi := hasFDerivAt_homeomorph_symm_of_det_ne_zero F hF hdet
  apply DifferentiableAt.comp (F x) _ hi.differentiableAt
  simpa only [F.symm_apply_apply] using hf

/-- The actual inverse pullback satisfies the full cofactor gradient estimate.
Its differentiability is an output of the proof, not an input. -/
theorem signedJacobian_mul_norm_fderiv_scalar_comp_symm_le
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {x : ℂ} {K C : ℝ}
    (hF : HasFDerivAt F (fderiv ℝ F x) x)
    (hJ : 0 < signedJacobian F x) (hf : DifferentiableAt ℝ f x)
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hQC : ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hJw : signedJacobian F x ≤ C * w x) :
    signedJacobian F x * ‖fderiv ℝ (f ∘ F.symm) (F x)‖ ≤
      Real.sqrt (K * C) * ‖fderiv ℝ f x‖ * Real.sqrt (w x) := by
  have hg := differentiableAt_scalar_comp_homeomorph_symm F hF hJ.ne' hf
  have hcomp : (f ∘ F.symm) ∘ F = f := by
    funext z
    simp only [Function.comp_apply, F.symm_apply_apply]
  obtain ⟨h₁, h₂⟩ := fderiv_det_mul_norm_gradient_chain_of_comp
    hF.differentiableAt hg hcomp hK hC hJ.le hQC hJw
  exact h₁.trans h₂

/-- Nonnegative inverse-gradient transport on the actual image ball. Neither
target integrability nor differentiability of the inverse pullback is assumed.
Even measurability of `w` is unnecessary for this ENNReal inequality. -/
theorem lintegral_norm_fderiv_scalar_comp_symm_image_ball_le
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hQC : ∀ᵐ x ∂volume, ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hJw : ∀ᵐ x ∂volume, signedJacobian F x ≤ C * w x)
    (hf : Differentiable ℝ f) (c : ℂ) (r : ℝ) :
    (∫⁻ z in F '' ball c r, ENNReal.ofReal ‖fderiv ℝ (f ∘ F.symm) z‖) ≤
      ENNReal.ofReal (Real.sqrt (K * C)) *
        ∫⁻ x in ball c r, ENNReal.ofReal (‖fderiv ℝ f x‖ * Real.sqrt (w x)) := by
  rw [lintegral_image_ball_eq_lintegral_signedJacobian_mul_of_locallyLipschitz
    F.injective hLocal hRegular c r _
    (measurable_fderiv ℝ (f ∘ F.symm)).norm.ennreal_ofReal]
  calc
    _ ≤ ∫⁻ x in ball c r, ENNReal.ofReal (Real.sqrt (K * C)) *
        ENNReal.ofReal (‖fderiv ℝ f x‖ * Real.sqrt (w x)) := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_of_ae hRegular, ae_restrict_of_ae hQC,
        ae_restrict_of_ae hJw] with x hx hqc hjw
      have hb := ENNReal.ofReal_le_ofReal
        (signedJacobian_mul_norm_fderiv_scalar_comp_symm_le
          F hx.1 hx.2 (hf x) hK hC hqc hjw)
      simpa only [ENNReal.ofReal_mul hx.2.le,
        ← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg (K * C))] using hb
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Finite source weighted gradient produces integrability of the actual target
gradient, without assuming a Sobolev or inverse-gradient certificate. -/
theorem integrableOn_norm_fderiv_scalar_comp_symm_image_ball
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hQC : ∀ᵐ x ∂volume, ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hJw : ∀ᵐ x ∂volume, signedJacobian F x ≤ C * w x)
    (hf : Differentiable ℝ f) (c : ℂ) (r : ℝ)
    (hfinite : IntegrableOn (fun x => ‖fderiv ℝ f x‖ * Real.sqrt (w x)) (ball c r)) :
    IntegrableOn (fun z => ‖fderiv ℝ (f ∘ F.symm) z‖) (F '' ball c r) := by
  have hb := lintegral_norm_fderiv_scalar_comp_symm_image_ball_le
    F hK hC hLocal hRegular hQC hJw hf c r
  refine ⟨(measurable_fderiv ℝ (f ∘ F.symm)).norm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => norm_nonneg _))]
  apply hb.trans_lt
  exact ENNReal.mul_lt_top (by finiteness)
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun x => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))).mp hfinite.hasFiniteIntegral)

/-- Real inverse-gradient transport, after proving the target integral is finite.
The sole finiteness input concerns the source weighted gradient. -/
theorem integral_norm_fderiv_scalar_comp_symm_image_ball_le
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hQC : ∀ᵐ x ∂volume, ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hJw : ∀ᵐ x ∂volume, signedJacobian F x ≤ C * w x)
    (hf : Differentiable ℝ f) (c : ℂ) (r : ℝ)
    (hfinite : IntegrableOn (fun x => ‖fderiv ℝ f x‖ * Real.sqrt (w x)) (ball c r)) :
    (∫ z in F '' ball c r, ‖fderiv ℝ (f ∘ F.symm) z‖) ≤
      Real.sqrt (K * C) * ∫ x in ball c r, ‖fderiv ℝ f x‖ * Real.sqrt (w x) := by
  have hb := lintegral_norm_fderiv_scalar_comp_symm_image_ball_le
    F hK hC hLocal hRegular hQC hJw hf c r
  have ht := integrableOn_norm_fderiv_scalar_comp_symm_image_ball
    F hK hC hLocal hRegular hQC hJw hf c r hfinite
  rw [← ofReal_integral_eq_lintegral_ofReal ht
    (Filter.Eventually.of_forall (fun z => norm_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hfinite
    (Filter.Eventually.of_forall (fun x => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _)
    (integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))))).mp hb

/-- For C1 source data and a continuous weight, compactness proves the source
weighted-gradient integrability on every ball. No compact support is required. -/
theorem integrableOn_norm_fderiv_mul_sqrt_weight_ball
    {f w : ℂ → ℝ} (hf : ContDiff ℝ 1 f) (hw : Continuous w) (c : ℂ) (r : ℝ) :
    IntegrableOn (fun x => ‖fderiv ℝ f x‖ * Real.sqrt (w x)) (ball c r) := by
  have hc : Continuous (fun x => ‖fderiv ℝ f x‖ * Real.sqrt (w x)) :=
    (hf.continuous_fderiv one_ne_zero).norm.mul hw.sqrt
  exact (hc.continuousOn.integrableOn_compact (isCompact_closedBall c r)).mono_set
    ball_subset_closedBall

/-- C1/continuous-weight producer: both actual image-gradient integrability and
the real transport estimate follow from the same map's analytic assumptions. -/
theorem inverse_gradient_transport_of_contDiff_continuous_weight
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hQC : ∀ᵐ x ∂volume, ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hJw : ∀ᵐ x ∂volume, signedJacobian F x ≤ C * w x)
    (hf : ContDiff ℝ 1 f) (hw : Continuous w) (c : ℂ) (r : ℝ) :
    IntegrableOn (fun z => ‖fderiv ℝ (f ∘ F.symm) z‖) (F '' ball c r) ∧
      (∫ z in F '' ball c r, ‖fderiv ℝ (f ∘ F.symm) z‖) ≤
        Real.sqrt (K * C) * ∫ x in ball c r, ‖fderiv ℝ f x‖ * Real.sqrt (w x) := by
  have hs := integrableOn_norm_fderiv_mul_sqrt_weight_ball hf hw c r
  exact ⟨integrableOn_norm_fderiv_scalar_comp_symm_image_ball
      F hK hC hLocal hRegular hQC hJw (hf.differentiable one_ne_zero) c r hs,
    integral_norm_fderiv_scalar_comp_symm_image_ball_le
      F hK hC hLocal hRegular hQC hJw (hf.differentiable one_ne_zero) c r hs⟩

end RepulsiveCoulomb.PaperRoute
