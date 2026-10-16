import LeanResearch.RepulsiveCoulomb.CoulombGaussianRotation
import LeanResearch.RepulsiveCoulomb.CoulombGaussianMehler

/-! Weighted Cauchy--Schwarz and the exact Fisher-information contraction of
the actual planar Mehler integral. Integrability, Gaussian invariance, and
spatial differentiation are supplied by proved density/kernel results. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coulombGaussian_weighted_square_pointwise {g : ℝ} (hg : 0 < g) (h r : ℝ) :
    2 * r * h ≤ h ^ 2 / g + r ^ 2 * g := by
  apply (mul_le_mul_iff_of_pos_right hg).mp
  have he : (h ^ 2 / g + r ^ 2 * g) * g = h ^ 2 + r ^ 2 * g ^ 2 := by
    field_simp [hg.ne'] <;> ring
  rw [he]
  nlinarith [sq_nonneg (h - r * g)]

/-- Weighted scalar Cauchy--Schwarz, obtained by integrating an actual square. -/
theorem coulombGaussian_integral_weighted_square_le
    {α : Type*} [MeasurableSpace α] (μ : Measure α) {h g : α → ℝ}
    (hg : ∀ x, 0 < g x) (hG : 0 < ∫ x, g x ∂μ)
    (hh : Integrable h μ) (hgi : Integrable g μ)
    (hqi : Integrable (fun x => h x ^ 2 / g x) μ) :
    (∫ x, h x ∂μ) ^ 2 / (∫ x, g x ∂μ) ≤ ∫ x, h x ^ 2 / g x ∂μ := by
  let r := (∫ x, h x ∂μ) / (∫ x, g x ∂μ)
  have hi := integral_mono (hh.const_mul (2 * r)) (hqi.add (hgi.const_mul (r ^ 2)))
    (fun x => coulombGaussian_weighted_square_pointwise (hg x) (h x) r)
  dsimp only [Pi.add_apply] at hi
  rw [integral_const_mul, integral_add hqi (hgi.const_mul (r ^ 2)), integral_const_mul] at hi
  have he : 2 * r * (∫ x, h x ∂μ) - r ^ 2 * (∫ x, g x ∂μ) =
      (∫ x, h x ∂μ) ^ 2 / (∫ x, g x ∂μ) := by
    dsimp only [r]
    field_simp [hG.ne'] <;> ring
  linarith

/-- The Bochner-valued weighted inequality used for the real differential. -/
theorem coulombGaussian_norm_integral_sq_div_le
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure α) {F : α → E} {g : α → ℝ}
    (hg : ∀ x, 0 < g x) (hG : 0 < ∫ x, g x ∂μ)
    (hF : Integrable F μ) (hgi : Integrable g μ)
    (hqi : Integrable (fun x => ‖F x‖ ^ 2 / g x) μ) :
    ‖∫ x, F x ∂μ‖ ^ 2 / (∫ x, g x ∂μ) ≤ ∫ x, ‖F x‖ ^ 2 / g x ∂μ := by
  have hnorm := norm_integral_le_integral_norm (f := F) (μ := μ)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hnorm 2
  exact (div_le_div_of_nonneg_right hsq hG.le).trans
    (coulombGaussian_integral_weighted_square_le μ hg hG hF.norm hgi hqi)

def coulombGaussianFisherDensity (f : ℂ → ℝ) (x : ℂ) : ℝ :=
  ‖fderiv ℝ f x‖ ^ 2 / f x

theorem coulombGaussianFisherDensity_continuous {f : ℂ → ℝ}
    (hf : ContDiff ℝ 1 f) (hpos : ∀ x, 0 < f x) : Continuous (coulombGaussianFisherDensity f) :=
  ((hf.continuous_fderiv (by norm_num)).norm.pow 2).div hf.continuous
    (fun x => (hpos x).ne')

theorem coulombGaussianFisherDensity_nonneg {f : ℂ → ℝ} (hpos : ∀ x, 0 < f x) (x : ℂ) :
    0 ≤ coulombGaussianFisherDensity f x := div_nonneg (sq_nonneg _) (hpos x).le

theorem coulombGaussianFisherDensity_bound {f : ℂ → ℝ} {D m : ℝ}
    (hm : 0 < m) (hfm : ∀ x, m ≤ f x) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (x : ℂ) :
    ‖coulombGaussianFisherDensity f x‖ ≤ D ^ 2 / m := by
  have hpos (x : ℂ) : 0 < f x := hm.trans_le (hfm x)
  rw [Real.norm_eq_abs, abs_of_nonneg (coulombGaussianFisherDensity_nonneg hpos x)]
  exact (div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hD x) 2)
    (hpos x).le).trans (div_le_div_of_nonneg_left (sq_nonneg D) hm (hfm x))

/-- Actual invariant average, deduced from the Gaussian rotation and Fubini. -/
theorem coulombGaussianAverage_integral {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (∫ x, coulombGaussianAverage β a b f x ∂coulombCenterGaussian β) =
      ∫ x, f x ∂coulombCenterGaussian β := by
  letI := coulombCenterGaussian_isProbability hβ
  have hF : Integrable (fun p : ℂ × ℂ => f (a • p.1 + b • p.2))
      ((coulombCenterGaussian β).prod (coulombCenterGaussian β)) :=
    (integrable_const M).mono' (by fun_prop) (Eventually.of_forall (fun p => hM _))
  have hfst : Integrable (fun p : ℂ × ℂ => f p.1)
      ((coulombCenterGaussian β).prod (coulombCenterGaussian β)) :=
    (integrable_const M).mono' (by fun_prop) (Eventually.of_forall (fun p => hM _))
  have h := (coulombGaussianRotate_measurePreserving hβ a b hab).integral_comp
    (coulombGaussianRotateEquiv a b hab).measurableEmbedding (fun p : ℂ × ℂ => f p.1)
  simp_rw [coulombGaussianRotateEquiv_apply] at h
  rw [integral_prod _ hF, integral_prod _ hfst] at h
  simpa only [coulombGaussianAverage, integral_const, probReal_univ, one_smul] using h

theorem coulombGaussianAverage_fderiv_continuous {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D : ℝ}
    (hM : ∀ x, ‖f x‖ ≤ M) (hD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (a b : ℝ) :
    Continuous (fderiv ℝ (coulombGaussianAverage β a b f)) := by
  letI := coulombCenterGaussian_isProbability hβ
  have hc := hf.continuous_fderiv (by norm_num)
  have hcont : Continuous (fun x : ℂ =>
      ∫ y, a • fderiv ℝ f (a • x + b • y) ∂coulombCenterGaussian β) := by
    apply continuous_of_dominated (bound := fun _ : ℂ => |a| * D)
    · intro x
      fun_prop
    · intro x
      filter_upwards [] with y
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg a)
    · exact integrable_const _
    · filter_upwards [] with y
      fun_prop
  have he : fderiv ℝ (coulombGaussianAverage β a b f) =
      (fun x => ∫ y, a • fderiv ℝ f (a • x + b • y) ∂coulombCenterGaussian β) := by
    funext x
    exact (coulombGaussianAverage_hasFDerivAt hβ hf hM hD a b x).fderiv
  rw [he]
  exact hcont

/-- Pointwise exact Fisher contraction for the genuine affine Gaussian average. -/
theorem coulombGaussianAverage_fisher_pointwise {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D m : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D)
    (hm : 0 < m) (hfm : ∀ z, m ≤ f z) (a b : ℝ) (x : ℂ) :
    coulombGaussianFisherDensity (coulombGaussianAverage β a b f) x ≤
      a ^ 2 * coulombGaussianAverage β a b (coulombGaussianFisherDensity f) x := by
  letI := coulombCenterGaussian_isProbability hβ
  have hpos (z : ℂ) : 0 < f z := hm.trans_le (hfm z)
  have hqi := coulombGaussianAverage_integrable hβ
    (coulombGaussianFisherDensity_continuous hf hpos)
    (coulombGaussianFisherDensity_bound hm hfm hD) a b x
  have hF : Integrable (fun y => fderiv ℝ f (a • x + b • y)) (coulombCenterGaussian β) := by
    have hc := hf.continuous_fderiv (by norm_num)
    exact (integrable_const D).mono' (by fun_prop) (Eventually.of_forall (fun y => hD _))
  have hG := hm.trans_le (coulombGaussianAverage_lower hβ hf.continuous hM hfm a b x)
  have h := coulombGaussian_norm_integral_sq_div_le (coulombCenterGaussian β)
    (fun y => hpos (a • x + b • y)) hG hF
    (coulombGaussianAverage_integrable hβ hf.continuous hM a b x) hqi
  unfold coulombGaussianFisherDensity
  rw [(coulombGaussianAverage_hasFDerivAt hβ hf hM hD a b x).fderiv,
    integral_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
  convert mul_le_mul_of_nonneg_left h (sq_nonneg a) using 1 <;>
    dsimp only [coulombGaussianAverage, coulombGaussianFisherDensity] <;> ring

theorem coulombGaussianAverage_continuous_fixed {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (a b : ℝ) :
    Continuous (coulombGaussianAverage β a b f) := by
  have hT : Continuous (fun x : ℂ => (a, b, x)) :=
    continuous_const.prodMk (continuous_const.prodMk continuous_id)
  exact (coulombGaussianAverage_continuous hβ hf hM).comp hT

theorem coulombGaussianAverage_bounded_integrable {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (a b : ℝ) :
    Integrable (coulombGaussianAverage β a b f) (coulombCenterGaussian β) := by
  letI := coulombCenterGaussian_isProbability hβ
  apply (integrable_const M).mono'
    (coulombGaussianAverage_continuous_fixed hβ hf hM a b).aestronglyMeasurable
  exact Eventually.of_forall (coulombGaussianAverage_norm_le hβ hM a b)

theorem coulombGaussianAverage_fisher_continuous {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D m : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D)
    (hm : 0 < m) (hfm : ∀ z, m ≤ f z) (a b : ℝ) :
    Continuous (coulombGaussianFisherDensity (coulombGaussianAverage β a b f)) := by
  unfold coulombGaussianFisherDensity
  exact ((coulombGaussianAverage_fderiv_continuous hβ hf hM hD a b).norm.pow 2).div
    (coulombGaussianAverage_continuous_fixed hβ hf.continuous hM a b)
    (fun x => (hm.trans_le (coulombGaussianAverage_lower hβ hf.continuous hM hfm a b x)).ne')

theorem coulombGaussianAverage_fisher_integrable {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D m : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D)
    (hm : 0 < m) (hfm : ∀ z, m ≤ f z) (a b : ℝ) :
    Integrable (coulombGaussianFisherDensity (coulombGaussianAverage β a b f))
      (coulombCenterGaussian β) := by
  have hpos (z : ℂ) : 0 < f z := hm.trans_le (hfm z)
  have hqi := coulombGaussianAverage_bounded_integrable hβ
    (coulombGaussianFisherDensity_continuous hf hpos)
    (coulombGaussianFisherDensity_bound hm hfm hD) a b
  apply (hqi.const_mul (a ^ 2)).mono'
    (coulombGaussianAverage_fisher_continuous hβ hf hM hD hm hfm a b).aestronglyMeasurable
  filter_upwards [] with x
  have hPpos (z : ℂ) : 0 < coulombGaussianAverage β a b f z :=
    hm.trans_le (coulombGaussianAverage_lower hβ hf.continuous hM hfm a b z)
  rw [Real.norm_eq_abs, abs_of_nonneg (coulombGaussianFisherDensity_nonneg hPpos x)]
  exact coulombGaussianAverage_fisher_pointwise hβ hf hM hD hm hfm a b x

/-- Exact integrated Fisher contraction; the coefficient a² is not weakened. -/
theorem coulombGaussianAverage_fisher_integral {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D m : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D)
    (hm : 0 < m) (hfm : ∀ z, m ≤ f z) (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    (∫ x, coulombGaussianFisherDensity (coulombGaussianAverage β a b f) x
      ∂coulombCenterGaussian β) ≤
        a ^ 2 * ∫ x, coulombGaussianFisherDensity f x ∂coulombCenterGaussian β := by
  have hpos (z : ℂ) : 0 < f z := hm.trans_le (hfm z)
  have hq := coulombGaussianFisherDensity_continuous hf hpos
  have hqb := coulombGaussianFisherDensity_bound hm hfm hD
  have hright := (coulombGaussianAverage_bounded_integrable hβ hq hqb a b).const_mul (a ^ 2)
  have hleft := coulombGaussianAverage_fisher_integrable hβ hf hM hD hm hfm a b
  have hi := integral_mono hleft hright
    (coulombGaussianAverage_fisher_pointwise hβ hf hM hD hm hfm a b)
  rw [integral_const_mul, coulombGaussianAverage_integral hβ hq hqb a b hab] at hi
  exact hi

/-- Fisher decay for the actual β-normalized Ornstein--Uhlenbeck kernel. -/
theorem coulombGaussianOU_fisher_integral {β t : ℝ} (hβ : 0 < β) (ht : 0 ≤ t)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D m : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D)
    (hm : 0 < m) (hfm : ∀ z, m ≤ f z) :
    (∫ x, coulombGaussianFisherDensity (coulombGaussianOU β t f) x ∂coulombCenterGaussian β) ≤
      Real.exp (-2 * β * t) * ∫ x, coulombGaussianFisherDensity f x ∂coulombCenterGaussian β := by
  have h := coulombGaussianAverage_fisher_integral hβ hf hM hD hm hfm
    (coulombMehlerDrift β t) (coulombMehlerNoise β t) (coulombMehler_coefficients hβ.le ht)
  have he : coulombMehlerDrift β t ^ 2 = Real.exp (-2 * β * t) := by
    unfold coulombMehlerDrift
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  simpa only [coulombGaussianOU, he] using h

end RepulsiveCoulomb
