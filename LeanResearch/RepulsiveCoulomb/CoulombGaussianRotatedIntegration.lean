module

public import LeanResearch.RepulsiveCoulomb.CoulombGaussianMehlerRegularity
public import LeanResearch.RepulsiveCoulomb.CoulombGaussianRotation

@[expose] public section

/-! The entropy differentiation cancellation at the level of the actual
Gaussian integral. A rotation makes the derivative of the original input
constant along the integration-by-parts direction, so C¹ data suffice. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace InnerProductSpace
namespace RepulsiveCoulomb

/-- The inverse rotation recovers the original first coordinate. -/
theorem coulombGaussianRotate_inverse_first {a b : ℝ} (hab : a ^ 2 + b ^ 2 = 1)
    (x y : ℂ) : a • (a • x + b • y) + (-b) • ((-b) • x + a • y) = x := by
  calc
    _ = (a ^ 2 + b ^ 2) • x := by module
    _ = x := by rw [hab, one_smul]

/-- A bounded differentiable scalar composed with an affine map has a
bounded derivative with the exact scalar factor. -/
theorem coulombGaussian_affine_fderiv {h : ℂ → ℝ} (hh : Differentiable ℝ h)
    (c : ℂ) (r : ℝ) (w : ℂ) :
    fderiv ℝ (fun w => h (c + r • w)) w = r • fderiv ℝ h (c + r • w) := by
  have hd := (hh (c + r • w)).hasFDerivAt.comp w
    (((hasFDerivAt_id w).const_smul r).const_add c)
  simp only [Function.comp_def, Pi.smul_apply, id_eq] at hd
  rw [hd.fderiv]
  ext v
  simp

/-- The precise rotated Gaussian integration-by-parts identity. No semigroup
identity or entropy-dissipation assumption appears among the hypotheses. -/
theorem coulombGaussian_rotated_integrationByParts {β : ℝ} (hβ : 0 < β)
    {g h : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (hh : ContDiff ℝ 1 h)
    {Mg Dg Mh Dh : ℝ}
    (hMg : ∀ z, ‖g z‖ ≤ Mg) (hDg : ∀ z, ‖fderiv ℝ g z‖ ≤ Dg)
    (hMh : ∀ z, ‖h z‖ ≤ Mh) (hDh : ∀ z, ‖fderiv ℝ h z‖ ≤ Dh)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    β * (∫ p : ℂ × ℂ, h p.1 *
        fderiv ℝ g (a • p.1 + b • p.2) ((-b) • p.1 + a • p.2)
        ∂(coulombCenterGaussian β).prod (coulombCenterGaussian β)) =
      -b * (∫ p : ℂ × ℂ,
        fderiv ℝ h p.1 (gradient g (a • p.1 + b • p.2))
        ∂(coulombCenterGaussian β).prod (coulombCenterGaussian β)) := by
  let μ := coulombCenterGaussian β
  letI : IsProbabilityMeasure μ := coulombCenterGaussian_isProbability hβ
  let F : ℂ × ℂ → ℝ := fun p =>
    h (a • p.1 + (-b) • p.2) * fderiv ℝ g p.1 p.2
  let K : ℂ × ℂ → ℝ := fun p =>
    fderiv ℝ h (a • p.1 + (-b) • p.2) (gradient g p.1)
  have hcg := hg.continuous_fderiv (by norm_num)
  have hch := hh.continuous_fderiv (by norm_num)
  have hcgrad : Continuous (gradient g) :=
    (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp hcg
  have hMh0 : 0 ≤ Mh := (norm_nonneg (h 0)).trans (hMh 0)
  have hDg0 : 0 ≤ Dg := (norm_nonneg (fderiv ℝ g 0)).trans (hDg 0)
  have hDh0 : 0 ≤ Dh := (norm_nonneg (fderiv ℝ h 0)).trans (hDh 0)
  have hgrad (z : ℂ) : ‖gradient g z‖ ≤ Dg := by
    rw [TauCeti.norm_gradient_eq_norm_fderiv]
    exact hDg z
  have hFi : Integrable F (μ.prod μ) := by
    apply (((coulombGaussian_norm_integrable hβ).comp_snd μ).const_mul (Mh * Dg)).mono'
      (by dsimp [F]; fun_prop)
    filter_upwards [] with p
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ Mh * (Dg * ‖p.2‖) :=
        mul_le_mul (hMh _) ((ContinuousLinearMap.le_opNorm _ _).trans
          (mul_le_mul_of_nonneg_right (hDg _) (norm_nonneg _)))
          (norm_nonneg _) hMh0
      _ = _ := by ring
  have hKi : Integrable K (μ.prod μ) := by
    apply (integrable_const (Dh * Dg)).mono' (by dsimp [K]; fun_prop)
    filter_upwards [] with p
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hDh _) (hgrad _) (norm_nonneg _) hDh0)
  have hfiber (z : ℂ) : β * (∫ w, F (z, w) ∂μ) = -b * (∫ w, K (z, w) ∂μ) := by
    let hz : ℂ → ℝ := fun w => h (a • z + (-b) • w)
    have hhzc : ContDiff ℝ 1 hz := hh.comp (by dsimp [hz]; fun_prop)
    have hhzM (w : ℂ) : ‖hz w‖ ≤ Mh := hMh _
    have hhzD (w : ℂ) : ‖fderiv ℝ hz w‖ ≤ |b| * Dh := by
      rw [coulombGaussian_affine_fderiv (hh.differentiable (by norm_num)),
        norm_smul, Real.norm_eq_abs, abs_neg]
      exact mul_le_mul_of_nonneg_left (hDh _) (abs_nonneg b)
    have hi := coulombGaussian_integrationByParts hβ hhzc hhzM hhzD (gradient g z)
    have heL : (fun w => fderiv ℝ hz w (gradient g z)) =
        (fun w => -b * K (z, w)) := by
      funext w
      rw [coulombGaussian_affine_fderiv (hh.differentiable (by norm_num))]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, K]
    have heR : (fun w => ⟪w, gradient g z⟫_ℝ * hz w) = (fun w => F (z, w)) := by
      funext w
      rw [real_inner_comm, inner_gradient_left]
      exact mul_comm _ _
    rw [heL, heR, integral_const_mul] at hi
    exact hi.symm
  have hprod : β * (∫ p, F p ∂μ.prod μ) = -b * (∫ p, K p ∂μ.prod μ) := by
    rw [integral_prod _ hFi, integral_prod _ hKi, ← integral_const_mul, ← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall hfiber)
  have hrot := coulombGaussianRotate_measurePreserving hβ a b hab
  have hFrot := hrot.integral_comp' F
  have hKrot := hrot.integral_comp' K
  have hFA : (fun p => F (coulombGaussianRotateEquiv a b hab p)) =
      (fun p : ℂ × ℂ => h p.1 *
        fderiv ℝ g (a • p.1 + b • p.2) ((-b) • p.1 + a • p.2)) := by
    funext p
    simp only [F, coulombGaussianRotateEquiv_apply, coulombGaussianRotate_inverse_first hab]
  have hKA : (fun p => K (coulombGaussianRotateEquiv a b hab p)) =
      (fun p : ℂ × ℂ => fderiv ℝ h p.1 (gradient g (a • p.1 + b • p.2))) := by
    funext p
    simp only [K, coulombGaussianRotateEquiv_apply, coulombGaussianRotate_inverse_first hab]
  rw [hFA] at hFrot
  rw [hKA] at hKrot
  change β * (∫ p, _ ∂μ.prod μ) = -b * (∫ p, _ ∂μ.prod μ)
  rw [hFrot, hKrot]
  exact hprod

end RepulsiveCoulomb
