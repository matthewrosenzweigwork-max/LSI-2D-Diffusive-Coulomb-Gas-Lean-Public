module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.SignedAreaBall
public import LeanResearch.RepulsiveCoulomb.PaperRoute.PlanarLogCutoff
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

@[expose] public section

/-!
# Actual scalar Dirichlet energy pulled back by a planar QC homeomorphism

The input is the same homeomorphism, its compact-ball Lipschitz bounds, and
almost-everywhere actual differentiability, positive signed Jacobian and
analytic distortion. The target scalar function is globally C1 and has
compactly supported derivative. Ballwise signed area transport proves the
whole-plane nonnegative energy estimate. Finiteness then gives integrability
and the real energy inequality. Neither the scalar function nor its pullback
is assumed to be globally L2; no energy or area certificate is an input.
-/

noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal NNReal Topology

namespace RepulsiveCoulomb.PaperRoute

/-- Compact support of the derivative suffices for global Lipschitzness. -/
theorem exists_lipschitzWith_of_contDiff_hasCompactSupport_fderiv
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport (fderiv ℝ ψ)) :
    ∃ C : ℝ≥0, LipschitzWith C ψ := by
  obtain ⟨C, hC⟩ := hs.exists_bound_of_continuous (hψ.continuous_fderiv one_ne_zero)
  refine ⟨.mk (max C 0) (le_max_right _ _), ?_⟩
  apply lipschitzWith_of_nnnorm_fderiv_le (hψ.differentiable one_ne_zero) (fun x => ?_)
  simp [← NNReal.coe_le_coe, hC x]

/-- The actual target derivative energy is integrable before change of variables. -/
theorem integrable_sq_norm_fderiv_of_contDiff_hasCompactSupport
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport (fderiv ℝ ψ)) :
    Integrable (fun z : ℂ => ‖fderiv ℝ ψ z‖ ^ 2) volume := by
  have hs2 : HasCompactSupport ((fun d : ℂ →L[ℝ] ℝ => ‖d‖ ^ 2) ∘ fderiv ℝ ψ) :=
    hs.comp_left (by simp)
  exact ((hψ.continuous_fderiv one_ne_zero).norm.pow 2).integrable_of_hasCompactSupport hs2

/-- The scalar pullback is Lipschitz on each source closed ball. -/
theorem exists_lipschitzOn_scalar_comp_closedBall
    {F : ℂ → ℂ}
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport (fderiv ℝ ψ)) (R : ℝ) :
    ∃ L : ℝ≥0, LipschitzOnWith L (ψ ∘ F) (closedBall 0 R) := by
  obtain ⟨C, hC⟩ := exists_lipschitzWith_of_contDiff_hasCompactSupport_fderiv hψ hs
  obtain ⟨L, hL⟩ := hLocal R
  exact ⟨C * L, hC.comp_lipschitzOnWith hL⟩

/-- Ordinary differentiation at source points gives the actual derivative estimate. -/
theorem sq_norm_fderiv_scalar_comp_le
    {F : ℂ → ℂ} {ψ : ℂ → ℝ} {x : ℂ} {K : ℝ}
    (hF : HasFDerivAt F (fderiv ℝ F x) x)
    (hψ : DifferentiableAt ℝ ψ (F x))
    (hK : ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x) :
    ‖fderiv ℝ (ψ ∘ F) x‖ ^ 2 ≤
      K * signedJacobian F x * ‖fderiv ℝ ψ (F x)‖ ^ 2 := by
  rw [(hψ.hasFDerivAt.comp x hF).fderiv]
  calc
    _ ≤ (‖fderiv ℝ ψ (F x)‖ * ‖fderiv ℝ F x‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (ContinuousLinearMap.opNorm_comp_le _ _) 2
    _ = ‖fderiv ℝ ψ (F x)‖ ^ 2 * ‖fderiv ℝ F x‖ ^ 2 := mul_pow _ _ _
    _ ≤ ‖fderiv ℝ ψ (F x)‖ ^ 2 * (K * signedJacobian F x) :=
      mul_le_mul_of_nonneg_left hK (sq_nonneg _)
    _ = _ := by ring

/-- Compact support in the target reduces the exact weighted transport to one
source ball. The ball is chosen from continuity of the inverse homeomorphism. -/
theorem lintegral_signedJacobian_mul_scalar_energy_eq
    (F : ℂ ≃ₜ ℂ)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hRegular : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport (fderiv ℝ ψ)) :
    (∫⁻ x : ℂ, ENNReal.ofReal (signedJacobian F x) *
      ENNReal.ofReal (‖fderiv ℝ ψ (F x)‖ ^ 2)) =
      ∫⁻ y : ℂ, ENNReal.ofReal (‖fderiv ℝ ψ y‖ ^ 2) := by
  obtain ⟨R, hR⟩ := (hs.image F.symm.continuous).isBounded.subset_ball (0 : ℂ)
  have hsource : Function.support (fun x : ℂ => ENNReal.ofReal (signedJacobian F x) *
      ENNReal.ofReal (‖fderiv ℝ ψ (F x)‖ ^ 2)) ⊆ ball 0 R := by
    intro x hx
    apply hR
    refine ⟨F x, ?_, F.symm_apply_apply x⟩
    apply subset_tsupport
    intro hz
    exact hx (by simp [hz])
  have htarget : Function.support (fun y : ℂ => ENNReal.ofReal (‖fderiv ℝ ψ y‖ ^ 2)) ⊆
      F '' ball 0 R := by
    intro y hy
    refine ⟨F.symm y, hR ?_, F.apply_symm_apply y⟩
    refine ⟨y, subset_tsupport _ ?_, rfl⟩
    intro hz
    exact hy (by simp [hz])
  rw [← setLIntegral_eq_of_support_subset hsource,
    ← setLIntegral_eq_of_support_subset htarget]
  exact (lintegral_image_ball_eq_lintegral_signedJacobian_mul_of_locallyLipschitz
    F.injective hLocal hRegular 0 R _
    (((hψ.continuous_fderiv one_ne_zero).norm.pow 2).measurable.ennreal_ofReal)).symm

/-- Nonnegative actual pullback energy from analytic distortion of this same map. -/
theorem lintegral_sq_norm_fderiv_scalar_comp_le
    (F : ℂ ≃ₜ ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport (fderiv ℝ ψ)) :
    (∫⁻ x : ℂ, ENNReal.ofReal (‖fderiv ℝ (ψ ∘ F) x‖ ^ 2)) ≤
      ENNReal.ofReal K * ∫⁻ y : ℂ, ENNReal.ofReal (‖fderiv ℝ ψ y‖ ^ 2) := by
  calc
    _ ≤ ∫⁻ x : ℂ, ENNReal.ofReal K *
        (ENNReal.ofReal (signedJacobian F x) *
          ENNReal.ofReal (‖fderiv ℝ ψ (F x)‖ ^ 2)) := by
      apply lintegral_mono_ae
      filter_upwards [hQC] with x hx
      have hb := ENNReal.ofReal_le_ofReal (sq_norm_fderiv_scalar_comp_le hx.1
        ((hψ.differentiable one_ne_zero) (F x)) hx.2.2)
      simpa only [ENNReal.ofReal_mul hK, ENNReal.ofReal_mul hx.2.1.le, mul_assoc] using hb
    _ = ENNReal.ofReal K *
        ∫⁻ x : ℂ, ENNReal.ofReal (signedJacobian F x) *
          ENNReal.ofReal (‖fderiv ℝ ψ (F x)‖ ^ 2) := by
      rw [lintegral_const_mul _ (by fun_prop)]
    _ = _ := by
      rw [lintegral_signedJacobian_mul_scalar_energy_eq F hLocal
        (hQC.mono fun _ hx => ⟨hx.1, hx.2.1⟩) hψ hs]

/-- Finiteness of the proven nonnegative energy yields integrability of the
actual pullback derivative. No global L2 assertion about the scalar is used. -/
theorem integrable_sq_norm_fderiv_scalar_comp
    (F : ℂ ≃ₜ ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport (fderiv ℝ ψ)) :
    Integrable (fun x : ℂ => ‖fderiv ℝ (ψ ∘ F) x‖ ^ 2) volume := by
  have htarget := integrable_sq_norm_fderiv_of_contDiff_hasCompactSupport hψ hs
  have hbound := lintegral_sq_norm_fderiv_scalar_comp_le F hK hLocal hQC hψ hs
  refine ⟨((measurable_fderiv ℝ (ψ ∘ F)).norm.pow_const 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => sq_nonneg _))]
  apply hbound.trans_lt
  exact ENNReal.mul_lt_top (by finiteness)
    ((hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall (fun x => sq_nonneg _))).mp
      htarget.hasFiniteIntegral)

/-- Real Dirichlet energy inequality, after both integrability claims are proved. -/
theorem integral_sq_norm_fderiv_scalar_comp_le
    (F : ℂ ≃ₜ ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hs : HasCompactSupport (fderiv ℝ ψ)) :
    (∫ x : ℂ, ‖fderiv ℝ (ψ ∘ F) x‖ ^ 2) ≤
      K * ∫ y : ℂ, ‖fderiv ℝ ψ y‖ ^ 2 := by
  have hb := lintegral_sq_norm_fderiv_scalar_comp_le F hK hLocal hQC hψ hs
  rw [← ofReal_integral_eq_lintegral_ofReal
    (integrable_sq_norm_fderiv_scalar_comp F hK hLocal hQC hψ hs)
    (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    ← ofReal_integral_eq_lintegral_ofReal
    (integrable_sq_norm_fderiv_of_contDiff_hasCompactSupport hψ hs)
    (Filter.Eventually.of_forall (fun x => sq_nonneg _)),
    ← ENNReal.ofReal_mul hK] at hb
  exact (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg hK (integral_nonneg (fun x => sq_nonneg _)))).mp hb

/-- The concrete logarithmic cutoff pulled back by this actual homeomorphism
has the finite energy needed by source-annulus oscillation. -/
theorem integral_sq_norm_fderiv_cubicLogCutoff_comp_le
    (F : ℂ ≃ₜ ℂ) {K : ℝ} (hK : 0 ≤ K)
    (hLocal : ∀ R : ℝ, ∃ L : ℝ≥0, LipschitzOnWith L F (closedBall 0 R))
    (hQC : ∀ᵐ x ∂volume,
      HasFDerivAt F (fderiv ℝ F x) x ∧ 0 < signedJacobian F x ∧
        ‖fderiv ℝ F x‖ ^ 2 ≤ K * signedJacobian F x)
    (a : ℂ) {l L : ℝ} (hl : 0 < l) (hlL : l < L) :
    (∫ x : ℂ, ‖fderiv ℝ (cubicLogCutoff a l L ∘ F) x‖ ^ 2) ≤
      9 * Real.pi * K / (2 * Real.log (L / l)) := by
  calc
    _ ≤ K * ∫ y : ℂ, ‖fderiv ℝ (cubicLogCutoff a l L) y‖ ^ 2 :=
      integral_sq_norm_fderiv_scalar_comp_le F hK hLocal hQC
        (contDiff_cubicLogCutoff hl hlL) (hasCompactSupport_fderiv_cubicLogCutoff hl hlL)
    _ ≤ K * (9 * Real.pi / (2 * Real.log (L / l))) :=
      mul_le_mul_of_nonneg_left (integral_sq_norm_fderiv_cubicLogCutoff_le hl hlL) hK
    _ = _ := by ring

end RepulsiveCoulomb.PaperRoute
