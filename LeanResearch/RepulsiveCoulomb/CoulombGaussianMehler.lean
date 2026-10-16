import LeanResearch.RepulsiveCoulomb.CoulombGaussianExponential
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! The literal Mehler integral for the normalized planar Gaussian.
This file constructs the averaging operator from the actual density. It does
not posit a Markov semigroup, an entropy inequality, or an entropy derivative.
The noise has law Gβ, so its coefficient is sqrt(1-exp(-2βt)), rather than
sqrt((1-exp(-2βt))/β), which is the coefficient for unit-variance noise. -/
noncomputable section
open Set MeasureTheory Filter
open PeriodicAttractiveLogGas
open scoped Topology ENNReal
namespace RepulsiveCoulomb

/-- Affine Gaussian averaging, before specializing the Mehler coefficients. -/
def coulombGaussianAverage (β a b : ℝ) (f : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, f (a • x + b • y) ∂coulombCenterGaussian β

/-- The contraction coefficient in the physical β-normalized OU flow. -/
def coulombMehlerDrift (β t : ℝ) : ℝ := Real.exp (-β * t)

/-- Noise coefficient when the noise itself has law Gβ. -/
def coulombMehlerNoise (β t : ℝ) : ℝ :=
  Real.sqrt (1 - coulombMehlerDrift β t ^ 2)

/-- Actual Mehler formula, with no abstract semigroup data. -/
def coulombGaussianOU (β t : ℝ) (f : ℂ → ℝ) : ℂ → ℝ :=
  coulombGaussianAverage β (coulombMehlerDrift β t) (coulombMehlerNoise β t) f

theorem coulombMehlerDrift_pos (β t : ℝ) : 0 < coulombMehlerDrift β t :=
  Real.exp_pos _

theorem coulombMehlerDrift_le_one {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    coulombMehlerDrift β t ≤ 1 := by
  unfold coulombMehlerDrift
  exact Real.exp_le_one_iff.mpr (by nlinarith)

theorem coulombMehlerNoise_nonneg (β t : ℝ) : 0 ≤ coulombMehlerNoise β t :=
  Real.sqrt_nonneg _

theorem coulombMehler_coefficients {β t : ℝ} (hβ : 0 ≤ β) (ht : 0 ≤ t) :
    coulombMehlerDrift β t ^ 2 + coulombMehlerNoise β t ^ 2 = 1 := by
  have ha := coulombMehlerDrift_le_one hβ ht
  have ha0 := (coulombMehlerDrift_pos β t).le
  have h : 0 ≤ 1 - coulombMehlerDrift β t ^ 2 := by nlinarith
  rw [coulombMehlerNoise, Real.sq_sqrt h]
  ring

theorem coulombMehlerDrift_continuous (β : ℝ) : Continuous (coulombMehlerDrift β) := by
  unfold coulombMehlerDrift
  fun_prop

theorem coulombMehlerNoise_continuous (β : ℝ) : Continuous (coulombMehlerNoise β) := by
  unfold coulombMehlerNoise
  exact Real.continuous_sqrt.comp (continuous_const.sub ((coulombMehlerDrift_continuous β).pow 2))

theorem coulombMehlerDrift_tendsto_zero {β : ℝ} (hβ : 0 < β) :
    Tendsto (coulombMehlerDrift β) atTop (𝓝 0) := by
  unfold coulombMehlerDrift
  exact Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (by linarith : -β < 0)).2 tendsto_id)

theorem coulombMehlerNoise_tendsto_one {β : ℝ} (hβ : 0 < β) :
    Tendsto (coulombMehlerNoise β) atTop (𝓝 1) := by
  change Tendsto (fun t => Real.sqrt (1 - coulombMehlerDrift β t ^ 2)) atTop (𝓝 1)
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    ((tendsto_const_nhds (x := (1 : ℝ))).sub ((coulombMehlerDrift_tendsto_zero hβ).pow 2))
  simpa only [Function.comp_def, coulombMehlerNoise, zero_pow (by decide : 2 ≠ 0), sub_zero, Real.sqrt_one] using h

/-- Bounded continuous integrands are genuinely integrable in every fiber. -/
theorem coulombGaussianAverage_integrable {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (a b : ℝ) (x : ℂ) :
    Integrable (fun y => f (a • x + b • y)) (coulombCenterGaussian β) := by
  letI := coulombCenterGaussian_isProbability hβ
  exact (integrable_const M).mono' (by fun_prop) (Eventually.of_forall (fun y => hM _))

theorem coulombGaussianAverage_const {β : ℝ} (hβ : 0 < β) (a b c : ℝ) (x : ℂ) :
    coulombGaussianAverage β a b (fun _ => c) x = c := by
  letI := coulombCenterGaussian_isProbability hβ
  simp [coulombGaussianAverage]

theorem coulombGaussianAverage_zero_noise {β : ℝ} (hβ : 0 < β)
    (a : ℝ) (f : ℂ → ℝ) (x : ℂ) :
    coulombGaussianAverage β a 0 f x = f (a • x) := by
  letI := coulombCenterGaussian_isProbability hβ
  simp [coulombGaussianAverage]

theorem coulombGaussianOU_zero {β : ℝ} (hβ : 0 < β) (f : ℂ → ℝ) :
    coulombGaussianOU β 0 f = f := by
  funext x
  simp [coulombGaussianOU, coulombMehlerDrift, coulombMehlerNoise,
    coulombGaussianAverage_zero_noise hβ]

theorem coulombGaussianAverage_norm_le {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (a b : ℝ) (x : ℂ) :
    ‖coulombGaussianAverage β a b f x‖ ≤ M := by
  letI := coulombCenterGaussian_isProbability hβ
  simpa [coulombGaussianAverage] using
    norm_integral_le_of_norm_le_const (μ := coulombCenterGaussian β)
      (Eventually.of_forall (fun y => hM (a • x + b • y)))

/-- The actual integral preserves a positive lower bound. -/
theorem coulombGaussianAverage_lower {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {M m : ℝ} (hM : ∀ z, ‖f z‖ ≤ M)
    (hm : ∀ z, m ≤ f z) (a b : ℝ) (x : ℂ) :
    m ≤ coulombGaussianAverage β a b f x := by
  letI := coulombCenterGaussian_isProbability hβ
  have h := integral_mono (integrable_const m)
    (coulombGaussianAverage_integrable hβ hf hM a b x) (fun y => hm _)
  simpa [coulombGaussianAverage] using h

/-- Joint continuity of the genuine affine averaging operator. -/
theorem coulombGaussianAverage_continuous {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) :
    Continuous (fun p : ℝ × ℝ × ℂ => coulombGaussianAverage β p.1 p.2.1 f p.2.2) := by
  letI := coulombCenterGaussian_isProbability hβ
  unfold coulombGaussianAverage
  exact continuous_of_dominated
    (fun p => by fun_prop)
    (fun p => Eventually.of_forall (fun y => hM _))
    (integrable_const M) (Eventually.of_forall (fun y => by fun_prop))

theorem coulombGaussianOU_continuous {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) :
    Continuous (fun p : ℝ × ℂ => coulombGaussianOU β p.1 f p.2) := by
  exact (coulombGaussianAverage_continuous hβ hf hM).comp
    (((coulombMehlerDrift_continuous β).comp continuous_fst).prodMk
      (((coulombMehlerNoise_continuous β).comp continuous_fst).prodMk continuous_snd))

/-- Convergence to the Gaussian mean is an actual dominated-convergence result. -/
theorem coulombGaussianOU_tendsto_mean {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : Continuous f) {M : ℝ} (hM : ∀ z, ‖f z‖ ≤ M) (x : ℂ) :
    Tendsto (fun t => coulombGaussianOU β t f x) atTop
      (𝓝 (∫ y, f y ∂coulombCenterGaussian β)) := by
  have h := (coulombGaussianAverage_continuous hβ hf hM).continuousAt.tendsto.comp
    ((coulombMehlerDrift_tendsto_zero hβ).prodMk_nhds
      ((coulombMehlerNoise_tendsto_one hβ).prodMk_nhds (tendsto_const_nhds (x := x))))
  simpa only [Function.comp_def, coulombGaussianOU, coulombGaussianAverage, zero_smul, one_smul, zero_add] using h

/-- Spatial differentiation under the actual Gaussian integral. Both the
integrability and dominating derivative bound are proved from bounded C¹ data. -/
theorem coulombGaussianAverage_hasFDerivAt {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D)
    (a b : ℝ) (x : ℂ) :
    HasFDerivAt (coulombGaussianAverage β a b f)
      (∫ y, a • fderiv ℝ f (a • x + b • y) ∂coulombCenterGaussian β) x := by
  letI := coulombCenterGaussian_isProbability hβ
  have hd := hf.differentiable (by norm_num)
  have hc := hf.continuous_fderiv (by norm_num)
  unfold coulombGaussianAverage
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := coulombCenterGaussian β)
    (F := fun x y => f (a • x + b • y))
    (F' := fun x y => a • fderiv ℝ f (a • x + b • y))
    (x₀ := x) (s := univ)
    (bound := fun _ : ℂ => |a| * D) (Filter.univ_mem)
    (Eventually.of_forall (fun x => by fun_prop))
    (coulombGaussianAverage_integrable hβ hf.continuous hM a b x)
    (by fun_prop)
    (Eventually.of_forall (fun y x _ => ?_))
    (integrable_const _) (Eventually.of_forall (fun y x _ => ?_))
  · rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hD _) (abs_nonneg a)
  · have h := (hd (a • x + b • y)).hasFDerivAt.comp x
      (((hasFDerivAt_id x).const_smul a).add_const (b • y))
    convert h using 1 <;> ext v <;> simp

/-- No differentiability assumption on a semigroup is hidden in this formula. -/
theorem coulombGaussianOU_fderiv {β : ℝ} (hβ : 0 < β)
    {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f) {M D : ℝ}
    (hM : ∀ z, ‖f z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ f z‖ ≤ D)
    (t : ℝ) (x : ℂ) :
    fderiv ℝ (coulombGaussianOU β t f) x =
      ∫ y, coulombMehlerDrift β t •
        fderiv ℝ f (coulombMehlerDrift β t • x + coulombMehlerNoise β t • y)
        ∂coulombCenterGaussian β :=
  (coulombGaussianAverage_hasFDerivAt hβ hf hM hD _ _ x).fderiv

end RepulsiveCoulomb
