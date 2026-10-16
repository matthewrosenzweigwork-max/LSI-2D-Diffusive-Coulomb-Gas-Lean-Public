module

public import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.Rademacher
public import Mathlib.Analysis.Calculus.FDeriv.Measurable
public import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Tactic

@[expose] public section

/-! Actual Euclidean smoothing of Lipschitz scalars. The derivative is proved
by dominated differentiation and Rademacher, and converges almost everywhere
by the normalized-bump differentiation theorem. No Sobolev density, derivative
approximation, or weighted-energy certificate is assumed. -/
noncomputable section
open MeasureTheory Set Metric Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff NNReal ENNReal
namespace RepulsiveCoulomb.PaperRoute

def lipschitzSmoothingScale (n : ℕ) : ℝ := ((n : ℝ) + 1)⁻¹

theorem lipschitzSmoothingScale_pos (n : ℕ) : 0 < lipschitzSmoothingScale n := by
  unfold lipschitzSmoothingScale
  positivity

theorem lipschitzSmoothingScale_le_one (n : ℕ) : lipschitzSmoothingScale n ≤ 1 := by
  unfold lipschitzSmoothingScale
  exact inv_le_one_of_one_le₀ (by have := Nat.cast_nonneg (α := ℝ) n; linarith)

theorem lipschitzSmoothingScale_tendsto :
    Tendsto lipschitzSmoothingScale atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  exact tendsto_inv_atTop_zero.comp h

def lipschitzSmoothingBump (n : ℕ) : ContDiffBump (0 : ℂ) :=
  ⟨lipschitzSmoothingScale n / 2, lipschitzSmoothingScale n,
    by have := lipschitzSmoothingScale_pos n; positivity,
    by have := lipschitzSmoothingScale_pos n; linarith⟩

def lipschitzSmoothingKernel (n : ℕ) : ℂ → ℝ := (lipschitzSmoothingBump n).normed volume

def lipschitzMollify (f : ℂ → ℝ) (n : ℕ) : ℂ → ℝ :=
  lipschitzSmoothingKernel n ⋆[lsmul ℝ ℝ, volume] f

theorem lipschitzMollify_contDiff {f : ℂ → ℝ} (hf : Continuous f) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (lipschitzMollify f n) := by
  exact (lipschitzSmoothingBump n).hasCompactSupport_normed.contDiff_convolution_left
    (lsmul ℝ ℝ) (lipschitzSmoothingBump n).contDiff_normed hf.locallyIntegrable

theorem lipschitzMollify_tendsto {f : ℂ → ℝ} (hf : Continuous f) (x : ℂ) :
    Tendsto (fun n => lipschitzMollify f n x) atTop (𝓝 (f x)) :=
  ContDiffBump.convolution_tendsto_right_of_continuous
    lipschitzSmoothingScale_tendsto hf x

theorem lipschitzMollify_dist_le {f : ℂ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : ℂ) :
    dist (lipschitzMollify f n x) (f x) ≤ L * lipschitzSmoothingScale n := by
  apply (lipschitzSmoothingBump n).dist_normed_convolution_le
    hf.continuous.aestronglyMeasurable
  intro y hy
  exact (hf.dist_le_mul y x).trans
    (mul_le_mul_of_nonneg_left (mem_ball.mp hy).le L.coe_nonneg)

theorem lipschitz_fderiv_locallyIntegrable {f : ℂ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : LocallyIntegrable (fderiv ℝ f) volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  apply (integrableOn_const hK.measure_lt_top.ne (C := (L : ℝ))).mono'
    (measurable_fderiv ℝ f).aestronglyMeasurable.restrict
  exact Eventually.of_forall (fun x => norm_fderiv_le_of_lipschitz ℝ hf)

/-- The genuine derivative of the mollified scalar is the mollified actual
a.e. derivative. Non-differentiability points do not alter the Lebesgue integral. -/
theorem lipschitzMollify_hasFDerivAt {f : ℂ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : ℂ) :
    HasFDerivAt (lipschitzMollify f n)
      ((lipschitzSmoothingKernel n ⋆[lsmul ℝ ℝ, volume] fderiv ℝ f) x) x := by
  let k := lipschitzSmoothingKernel n
  have hk : Integrable k := (lipschitzSmoothingBump n).integrable_normed
  have hk0 (y : ℂ) : 0 ≤ k y := (lipschitzSmoothingBump n).nonneg_normed y
  have hkc : Continuous k := (lipschitzSmoothingBump n).continuous_normed
  have hFi : Integrable (fun y : ℂ => k y * f (x-y)) :=
    (lipschitzSmoothingBump n).hasCompactSupport_normed.convolutionExists_left
      (lsmul ℝ ℝ) hkc hf.continuous.locallyIntegrable x
  have hm : AEStronglyMeasurable (fun y : ℂ => k y • fderiv ℝ f (x-y)) volume := by
    apply Measurable.aestronglyMeasurable
    exact hkc.measurable.smul ((measurable_fderiv ℝ f).comp (by fun_prop))
  have hlip : ∀ᵐ y : ℂ, LipschitzOnWith (Real.nnabs (k y * L))
      (fun z : ℂ => k y * f (z-y)) univ := by
    filter_upwards with y
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro u v
    rw [dist_eq_norm, ← mul_sub, norm_mul, Real.norm_of_nonneg (hk0 y)]
    have h := hf.dist_le_mul (u-y) (v-y)
    simp only [dist_sub_right] at h
    have hc : ((Real.nnabs (k y * L) : ℝ≥0) : ℝ) = k y * L := by
      change |k y * L| = k y * L
      exact abs_of_nonneg (mul_nonneg (hk0 y) L.coe_nonneg)
    rw [hc]
    simpa only [dist_eq_norm, mul_assoc] using mul_le_mul_of_nonneg_left h (hk0 y)
  have hdiff : ∀ᵐ y : ℂ, HasFDerivAt (fun z : ℂ => k y * f (z-y))
      (k y • fderiv ℝ f (x-y)) x := by
    filter_upwards [(volume.measurePreserving_sub_left x).quasiMeasurePreserving.ae
      hf.ae_differentiableAt] with y hy
    simpa only [ContinuousLinearMap.comp_id, Function.comp_apply, id_eq] using
      (hy.hasFDerivAt.comp x ((hasFDerivAt_id x).sub_const y)).const_mul (k y)
  have h := hasFDerivAt_integral_of_dominated_loc_of_lip
    (𝕜 := ℝ) (μ := (volume : Measure ℂ)) (s := univ)
    (F := fun z y : ℂ => k y * f (z-y)) (F' := fun y => k y • fderiv ℝ f (x-y))
    (bound := fun y => k y * L) univ_mem
    (Eventually.of_forall (fun z => by exact (hkc.mul (hf.continuous.comp (by fun_prop))).aestronglyMeasurable))
    hFi hm hlip (hk.mul_const L) hdiff
  exact h.2

theorem lipschitzMollify_fderiv {f : ℂ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : ℂ) :
    fderiv ℝ (lipschitzMollify f n) x =
      ((lipschitzSmoothingKernel n ⋆[lsmul ℝ ℝ, volume] fderiv ℝ f) x) :=
  (lipschitzMollify_hasFDerivAt hf n x).fderiv

/-- The original Lipschitz bound survives smoothing without a constant loss. -/
theorem lipschitzMollify_fderiv_norm_le {f : ℂ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) (n : ℕ) (x : ℂ) :
    ‖fderiv ℝ (lipschitzMollify f n) x‖ ≤ L := by
  rw [lipschitzMollify_fderiv hf]
  change ‖∫ y : ℂ, lipschitzSmoothingKernel n y • fderiv ℝ f (x-y)‖ ≤ L
  have hi : Integrable (fun y : ℂ => lipschitzSmoothingKernel n y • fderiv ℝ f (x-y)) :=
    (lipschitzSmoothingBump n).hasCompactSupport_normed.convolutionExists_left
      (lsmul ℝ ℝ) (lipschitzSmoothingBump n).continuous_normed
      (lipschitz_fderiv_locallyIntegrable hf) x
  calc
    _ ≤ ∫ y : ℂ, ‖lipschitzSmoothingKernel n y • fderiv ℝ f (x-y)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ y : ℂ, lipschitzSmoothingKernel n y * L := by
      apply integral_mono hi.norm ((lipschitzSmoothingBump n).integrable_normed.mul_const L)
      intro y
      change ‖lipschitzSmoothingKernel n y • fderiv ℝ f (x-y)‖ ≤ lipschitzSmoothingKernel n y * L
      rw [norm_smul, Real.norm_of_nonneg (show 0 ≤ lipschitzSmoothingKernel n y from (lipschitzSmoothingBump n).nonneg_normed y)]
      exact mul_le_mul_of_nonneg_left (norm_fderiv_le_of_lipschitz ℝ hf)
        ((lipschitzSmoothingBump n).nonneg_normed y)
    _ = L := by rw [integral_mul_const]; simp [lipschitzSmoothingKernel, ContDiffBump.integral_normed]

/-- Actual a.e. convergence of the physical derivative, not only uniform
convergence of the function values. -/
theorem lipschitzMollify_fderiv_ae_tendsto {f : ℂ → ℝ} {L : ℝ≥0}
    (hf : LipschitzWith L f) : ∀ᵐ x : ℂ,
      Tendsto (fun n => fderiv ℝ (lipschitzMollify f n) x) atTop (𝓝 (fderiv ℝ f x)) := by
  have h := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable
    (φ := lipschitzSmoothingBump) (K := 2) lipschitzSmoothingScale_tendsto
    (Eventually.of_forall (fun n => by
      change lipschitzSmoothingScale n ≤ 2 * (lipschitzSmoothingScale n / 2)
      linarith)) (lipschitz_fderiv_locallyIntegrable hf)
  simpa only [lipschitzMollify_fderiv hf, lipschitzSmoothingKernel] using h

end RepulsiveCoulomb.PaperRoute
