import LeanResearch.RepulsiveCoulomb.CoulombGaussianInterpolation
import LeanResearch.RepulsiveCoulomb.CoulombGaussianLSIClosure

/-! The actual entropy interpolation is continuous, with exact endpoints.
All bounds below come from the literal Gaussian kernel; no entropy continuity
or endpoint identity is assumed. The last assembly lemma explicitly isolates
the derivative computation that is proved in the separate interpolation-IBP
module before the final sharp LSI can be asserted. -/
noncomputable section
open Set MeasureTheory Filter
open PeriodicAttractiveLogGas
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coulombGaussianInterpolation_continuous {β : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M) :
    Continuous (fun p : ℝ × ℂ => coulombGaussianInterpolation β p.1 g p.2) :=
  (coulombGaussianAverage_continuous hβ hg hM).comp
    (continuous_fst.prodMk
      ((coulombGaussianInterpolationNoise_continuous.comp continuous_fst).prodMk continuous_snd))

/-- Uniform domination of t log t on the complete bounded range of every
actual Gaussian average, including endpoints and zero values. -/
theorem coulombGaussianInterpolation_mul_log_bound {β : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M) :
    ∃ B : ℝ, ∀ (s : ℝ) (x : ℂ),
      ‖coulombGaussianInterpolation β s g x * Real.log (coulombGaussianInterpolation β s g x)‖ ≤ B := by
  obtain ⟨B, hB⟩ := (isCompact_Icc : IsCompact (Icc (-M) M)).exists_bound_of_continuousOn
    Real.continuous_mul_log.continuousOn
  refine ⟨B, ?_⟩
  intro s x
  apply hB
  have h := coulombGaussianAverage_norm_le hβ hM s (coulombGaussianInterpolationNoise s) x
  rw [Real.norm_eq_abs] at h
  exact abs_le.mp h

theorem coulombGaussianInterpolationEntropy_continuous {β : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M) :
    Continuous (coulombGaussianInterpolationEntropy β g) := by
  letI := coulombCenterGaussian_isProbability hβ
  obtain ⟨B, hB⟩ := coulombGaussianInterpolation_mul_log_bound hβ hM
  have hc := coulombGaussianInterpolation_continuous hβ hg hM
  unfold coulombGaussianInterpolationEntropy
  apply continuous_of_dominated (bound := fun _ : ℂ => B)
  · intro s
    exact (Real.continuous_mul_log.comp
      (hc.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
  · exact fun s => Eventually.of_forall (hB s)
  · exact integrable_const B
  · filter_upwards [] with x
    exact Real.continuous_mul_log.comp (hc.comp (continuous_id.prodMk continuous_const))

theorem coulombGaussianInterpolation_zero (β : ℝ) (g : ℂ → ℝ) (x : ℂ) :
    coulombGaussianInterpolation β 0 g x = ∫ y, g y ∂coulombCenterGaussian β := by
  simp [coulombGaussianInterpolation, coulombGaussianInterpolationNoise, coulombGaussianAverage]

theorem coulombGaussianInterpolation_one {β : ℝ} (hβ : 0 < β) (g : ℂ → ℝ) (x : ℂ) :
    coulombGaussianInterpolation β 1 g x = g x := by
  simp [coulombGaussianInterpolation, coulombGaussianInterpolationNoise,
    coulombGaussianAverage_zero_noise hβ]

theorem coulombGaussianInterpolationEntropy_zero {β : ℝ} (hβ : 0 < β) (g : ℂ → ℝ) :
    coulombGaussianInterpolationEntropy β g 0 =
      (∫ x, g x ∂coulombCenterGaussian β) * Real.log (∫ x, g x ∂coulombCenterGaussian β) := by
  letI := coulombCenterGaussian_isProbability hβ
  simp [coulombGaussianInterpolationEntropy, coulombGaussianInterpolation_zero]

theorem coulombGaussianInterpolationEntropy_one {β : ℝ} (hβ : 0 < β) (g : ℂ → ℝ) :
    coulombGaussianInterpolationEntropy β g 1 =
      ∫ x, g x * Real.log (g x) ∂coulombCenterGaussian β := by
  simp only [coulombGaussianInterpolationEntropy, coulombGaussianInterpolation_one hβ]

theorem coulombGaussian_bounded_mul_log_integrable {β : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M) :
    Integrable (fun x => g x * Real.log (g x)) (coulombCenterGaussian β) := by
  letI := coulombCenterGaussian_isProbability hβ
  obtain ⟨B, hB⟩ := coulombGaussianInterpolation_mul_log_bound hβ hM
  apply (integrable_const B).mono' (Real.continuous_mul_log.comp hg).aestronglyMeasurable
  filter_upwards [] with x
  simpa only [coulombGaussianInterpolation_one hβ, Function.comp_apply] using hB 1 x

theorem coulombGaussian_entropy_eq_interpolation_difference {β : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : Continuous g) {M : ℝ} (hM : ∀ z, ‖g z‖ ≤ M)
    (hpos : ∀ z, 0 ≤ g z) :
    entropy (coulombCenterGaussian β) g =
      ((coulombGaussianInterpolationEntropy β g 1 - coulombGaussianInterpolationEntropy β g 0 : ℝ) : EReal) := by
  letI := coulombCenterGaussian_isProbability hβ
  rw [entropy_eq_integral (Eventually.of_forall hpos)
    (coulombGaussian_bounded_mul_log_integrable hβ hg hM),
    coulombGaussianInterpolationEntropy_zero hβ, coulombGaussianInterpolationEntropy_one hβ]

/-- Assembly step: the sole remaining input is the explicit derivative of the
actual raw entropy integral. It must be instantiated by the Gaussian rotated
integration-by-parts theorem, never exposed as a final LSI hypothesis. -/
theorem coulombGaussian_positive_fisher_of_interpolation_derivative {β : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {M D m : ℝ}
    (hM : ∀ z, ‖g z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ g z‖ ≤ D)
    (hm : 0 < m) (hgm : ∀ z, m ≤ g z)
    (hd : ∀ s ∈ Ioo 0 1, HasDerivAt (coulombGaussianInterpolationEntropy β g)
      ((1 / (β * s)) * ∫ x, coulombGaussianFisherDensity (coulombGaussianInterpolation β s g) x
        ∂coulombCenterGaussian β) s) :
    entropy (coulombCenterGaussian β) g ≤
      (((1 / (2 * β)) * ∫ x, coulombGaussianFisherDensity g x ∂coulombCenterGaussian β : ℝ) : EReal) := by
  have h := coulombGaussian_entropy_interpolation_fisher_bound hβ
    (coulombGaussianInterpolationEntropy_continuous hβ hg.continuous hM).continuousOn hd
    (fun s hs => coulombGaussianAverage_fisher_integral hβ hg hM hD hm hgm
      s (coulombGaussianInterpolationNoise s)
      (coulombGaussianInterpolationNoise_sq hs.1.le hs.2.le))
  rw [coulombGaussian_entropy_eq_interpolation_difference hβ hg.continuous hM
    (fun z => (hm.trans_le (hgm z)).le)]
  apply EReal.coe_le_coe_iff.mpr
  convert h using 1 <;> ring

end RepulsiveCoulomb
