module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.InverseGradientTransport
public import Mathlib.Analysis.Calculus.Rademacher

@[expose] public section

/-!
# Source-a.e. inverse-gradient transport for actual Lipschitz scalars

Rademacher supplies differentiability only almost everywhere. Boundedness of
the actual selected derivative, including its zero value where no derivative
exists, proves source finiteness. Signed area and the cofactor estimate then
prove target finiteness and the real inverse-gradient bound.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology
namespace RepulsiveCoulomb.PaperRoute

/-- Nonnegative inverse-gradient transport on the actual image ball. Neither
target integrability nor differentiability of the inverse pullback is assumed.
Even measurability of `w` is unnecessary for this ENNReal inequality. -/
theorem lintegral_norm_fderiv_scalar_comp_symm_image_ball_le_ae
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hQC : ∀ᵐ x ∂volume, ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hJw : ∀ᵐ x ∂volume, signedJacobian F x ≤ C * w x)
    (c : ℂ) (r : ℝ)
    (hfAE : ∀ᵐ x ∂volume.restrict (ball c r), DifferentiableAt ℝ f x) :
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
        ae_restrict_of_ae hJw, hfAE] with x hx hqc hjw hfx
      have hb := ENNReal.ofReal_le_ofReal
        (signedJacobian_mul_norm_fderiv_scalar_comp_symm_le
          F hx.1 hx.2 hfx hK hC hqc hjw)
      simpa only [ENNReal.ofReal_mul hx.2.le,
        ← mul_assoc, ← ENNReal.ofReal_mul (Real.sqrt_nonneg (K * C))] using hb
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Finite source weighted gradient produces integrability of the actual target
gradient, without assuming a Sobolev or inverse-gradient certificate. -/
theorem integrableOn_norm_fderiv_scalar_comp_symm_image_ball_ae
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hQC : ∀ᵐ x ∂volume, ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hJw : ∀ᵐ x ∂volume, signedJacobian F x ≤ C * w x)
    (c : ℂ) (r : ℝ)
    (hfAE : ∀ᵐ x ∂volume.restrict (ball c r), DifferentiableAt ℝ f x)
    (hfinite : IntegrableOn (fun x => ‖fderiv ℝ f x‖ * Real.sqrt (w x)) (ball c r)) :
    IntegrableOn (fun z => ‖fderiv ℝ (f ∘ F.symm) z‖) (F '' ball c r) := by
  have hb := lintegral_norm_fderiv_scalar_comp_symm_image_ball_le_ae
    F hK hC hLocal hRegular hQC hJw c r hfAE
  refine ⟨(measurable_fderiv ℝ (f ∘ F.symm)).norm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun z => norm_nonneg _))]
  apply hb.trans_lt
  exact ENNReal.mul_lt_top (by finiteness)
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
      (fun x => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))).mp hfinite.hasFiniteIntegral)

/-- Real inverse-gradient transport, after proving the target integral is finite.
The sole finiteness input concerns the source weighted gradient. -/
theorem integral_norm_fderiv_scalar_comp_symm_image_ball_le_ae
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {K C : ℝ}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hQC : ∀ᵐ x ∂volume, ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hJw : ∀ᵐ x ∂volume, signedJacobian F x ≤ C * w x)
    (c : ℂ) (r : ℝ)
    (hfAE : ∀ᵐ x ∂volume.restrict (ball c r), DifferentiableAt ℝ f x)
    (hfinite : IntegrableOn (fun x => ‖fderiv ℝ f x‖ * Real.sqrt (w x)) (ball c r)) :
    (∫ z in F '' ball c r, ‖fderiv ℝ (f ∘ F.symm) z‖) ≤
      Real.sqrt (K * C) * ∫ x in ball c r, ‖fderiv ℝ f x‖ * Real.sqrt (w x) := by
  have hb := lintegral_norm_fderiv_scalar_comp_symm_image_ball_le_ae
    F hK hC hLocal hRegular hQC hJw c r hfAE
  have ht := integrableOn_norm_fderiv_scalar_comp_symm_image_ball_ae
    F hK hC hLocal hRegular hQC hJw c r hfAE hfinite
  rw [← ofReal_integral_eq_lintegral_ofReal ht
    (Filter.Eventually.of_forall (fun z => norm_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal hfinite
    (Filter.Eventually.of_forall (fun x => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))),
    ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at hb
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg (Real.sqrt_nonneg _)
    (integral_nonneg (fun x => mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))))).mp hb

/-- Compactness of the continuous weight and the global derivative bound
prove source mixed-gradient finiteness without continuity of the derivative. -/
theorem integrableOn_norm_fderiv_mul_sqrt_weight_ball_of_lipschitz
    {f w : ℂ → ℝ} {Lf : ℝ≥0} (hf : LipschitzWith Lf f)
    (hw : Continuous w) (c : ℂ) (r : ℝ) :
    IntegrableOn (fun x => ‖fderiv ℝ f x‖ * Real.sqrt (w x)) (ball c r) := by
  have hmajor : IntegrableOn (fun x => (Lf : ℝ) * Real.sqrt (w x)) (ball c r) :=
    (((continuous_const.mul hw.sqrt).continuousOn.integrableOn_compact
      (isCompact_closedBall c r))).mono_set ball_subset_closedBall
  apply hmajor.mono' ((measurable_fderiv ℝ f).norm.mul hw.measurable.sqrt).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun x => by
    change ‖‖fderiv ℝ f x‖ * Real.sqrt (w x)‖ ≤ (Lf : ℝ) * Real.sqrt (w x)
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))]
    exact mul_le_mul_of_nonneg_right (norm_fderiv_le_of_lipschitz ℝ hf) (Real.sqrt_nonneg _))

/-- A globally Lipschitz source scalar has both finite actual target gradient
and the same inverse-gradient transport bound, via source Rademacher. -/
theorem inverse_gradient_transport_of_lipschitz_continuous_weight
    (F : ℂ ≃ₜ ℂ) {f w : ℂ → ℝ} {K C : ℝ} {Lf : ℝ≥0}
    (hK : 0 ≤ K) (hC : 0 ≤ C)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    (hQC : ∀ᵐ x ∂volume, ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (hJw : ∀ᵐ x ∂volume, signedJacobian F x ≤ C * w x)
    (hf : LipschitzWith Lf f) (hw : Continuous w) (c : ℂ) (r : ℝ) :
    IntegrableOn (fun z => ‖fderiv ℝ (f ∘ F.symm) z‖) (F '' ball c r) ∧
      (∫ z in F '' ball c r, ‖fderiv ℝ (f ∘ F.symm) z‖) ≤
        Real.sqrt (K * C) * ∫ x in ball c r, ‖fderiv ℝ f x‖ * Real.sqrt (w x) := by
  have hs := integrableOn_norm_fderiv_mul_sqrt_weight_ball_of_lipschitz hf hw c r
  have hfAE : ∀ᵐ x ∂volume.restrict (ball c r), DifferentiableAt ℝ f x :=
    ae_restrict_of_ae hf.ae_differentiableAt
  exact ⟨integrableOn_norm_fderiv_scalar_comp_symm_image_ball_ae
      F hK hC hLocal hRegular hQC hJw c r hfAE hs,
    integral_norm_fderiv_scalar_comp_symm_image_ball_le_ae
      F hK hC hLocal hRegular hQC hJw c r hfAE hs⟩

end RepulsiveCoulomb.PaperRoute
