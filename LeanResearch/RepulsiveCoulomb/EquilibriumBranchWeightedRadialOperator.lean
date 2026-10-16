module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchRadialAverageSmooth
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

@[expose] public section

/-! A bounded weighted radial integral and its actual first derivative, for
Banach-valued functions. This is the quantitative input for higher density
tails: differentiating raises the radial weight by one and averages the
actual derivative, while retaining its global bound. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped Topology
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumUnitIntervalMeasure : Measure ℝ := volume.restrict (Ioc 0 1)

instance equilibriumUnitIntervalMeasure_probability : IsProbabilityMeasure equilibriumUnitIntervalMeasure :=
  ⟨by simp [equilibriumUnitIntervalMeasure, Measure.restrict_apply_univ, Real.volume_Ioc]⟩

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

def equilibriumWeightedRadialOperator (k : ℕ) (f : ℂ → V) (x : ℂ) : V :=
  ∫ s : ℝ, s ^ k • f (s • x) ∂equilibriumUnitIntervalMeasure

theorem equilibriumUnitIntervalMeasure_mem :
    ∀ᵐ s ∂equilibriumUnitIntervalMeasure, s ∈ Ioc (0 : ℝ) 1 :=
  ae_restrict_mem measurableSet_Ioc

theorem equilibriumWeightedRadialOperator_integrable (k : ℕ) {f : ℂ → V}
    (hf : Continuous f) {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, ‖f x‖ ≤ B) (x : ℂ) :
    Integrable (fun s : ℝ => s ^ k • f (s • x)) equilibriumUnitIntervalMeasure := by
  have hc : Continuous (fun s : ℝ => s ^ k • f (s • x)) :=
    (continuous_id.pow k).smul (hf.comp (by fun_prop))
  apply Integrable.of_bound hc.aestronglyMeasurable B
  filter_upwards [equilibriumUnitIntervalMeasure_mem] with s hs
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs.1.le k)]
  exact (mul_le_mul (pow_le_one₀ hs.1.le hs.2) (hbound (s • x)) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)

/-- The average has operator norm at most one on the global sup bound. -/
theorem equilibriumWeightedRadialOperator_norm_le (k : ℕ) {f : ℂ → V}
    {B : ℝ} (hB : 0 ≤ B) (hbound : ∀ x, ‖f x‖ ≤ B) (x : ℂ) :
    ‖equilibriumWeightedRadialOperator k f x‖ ≤ B := by
  unfold equilibriumWeightedRadialOperator
  have hh : ∀ᵐ s ∂equilibriumUnitIntervalMeasure, ‖s ^ k • f (s • x)‖ ≤ B := by
    filter_upwards [equilibriumUnitIntervalMeasure_mem] with s hs
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs.1.le k)]
    exact (mul_le_mul (pow_le_one₀ hs.1.le hs.2) (hbound (s • x)) (norm_nonneg _) zero_le_one).trans_eq (one_mul B)
  simpa only [probReal_univ, one_mul, mul_one] using norm_integral_le_of_norm_le_const hh

/-- Actual differentiation under the weighted radial integral, with every
integrability and domination obligation proved from finite global bounds. -/
theorem equilibriumWeightedRadialOperator_hasFDerivAt (k : ℕ) {f : ℂ → V}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfB : ∀ x, ‖f x‖ ≤ B) (hfD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) (x : ℂ) :
    HasFDerivAt (equilibriumWeightedRadialOperator k f)
      (equilibriumWeightedRadialOperator (k + 1) (fderiv ℝ f) x) x := by
  let F : ℂ → ℝ → V := fun z s => s ^ k • f (s • z)
  let F' : ℂ → ℝ → ℂ →L[ℝ] V := fun z s => s ^ (k + 1) • fderiv ℝ f (s • z)
  have hfdc : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by simp)
  have hFm (z : ℂ) : AEStronglyMeasurable (F z) equilibriumUnitIntervalMeasure := by
    have hc : Continuous (F z) := (continuous_id.pow k).smul (hf.continuous.comp (by fun_prop))
    exact hc.aestronglyMeasurable
  have hF'm : AEStronglyMeasurable (F' x) equilibriumUnitIntervalMeasure := by
    have hc : Continuous (F' x) := (continuous_id.pow (k + 1)).smul (hfdc.comp (by fun_prop))
    exact hc.aestronglyMeasurable
  have hbound : ∀ᵐ s ∂equilibriumUnitIntervalMeasure, ∀ z ∈ (univ : Set ℂ), ‖F' z s‖ ≤ D := by
    filter_upwards [equilibriumUnitIntervalMeasure_mem] with s hs
    intro z _
    dsimp only [F']
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hs.1.le (k + 1))]
    exact (mul_le_mul (pow_le_one₀ hs.1.le hs.2) (hfD (s • z)) (norm_nonneg _) zero_le_one).trans_eq (one_mul D)
  have hdiff (s : ℝ) (z : ℂ) : HasFDerivAt (fun w : ℂ => F w s) (F' z s) z := by
    have hlin := (hasFDerivAt_id (𝕜 := ℝ) z).const_smul s
    have hfd := (hf.differentiable (by simp) (s • z)).hasFDerivAt
    convert (hfd.comp z hlin).const_smul (s ^ k) using 1 <;>
      ext v <;> simp [F, F', ContinuousLinearMap.comp_apply, smul_smul, pow_succ]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := equilibriumUnitIntervalMeasure) (F := F) (F' := F') (s := univ) (bound := fun _ => D)
    univ_mem (Eventually.of_forall hFm)
    (equilibriumWeightedRadialOperator_integrable k hf.continuous hB hfB x) hF'm hbound
    (integrable_const _) (Eventually.of_forall (fun s z _ => hdiff s z))

/-- Function-level derivative identity, permitting repeated differentiation
without introducing a separate formal radial profile. -/
theorem equilibriumWeightedRadialOperator_fderiv (k : ℕ) {f : ℂ → V}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D)
    (hfB : ∀ x, ‖f x‖ ≤ B) (hfD : ∀ x, ‖fderiv ℝ f x‖ ≤ D) :
    fderiv ℝ (equilibriumWeightedRadialOperator k f) =
      equilibriumWeightedRadialOperator (k + 1) (fderiv ℝ f) := by
  funext x
  exact (equilibriumWeightedRadialOperator_hasFDerivAt k hf hB hD hfB hfD x).fderiv

/-- The scalar weight-one specialization is exactly the previous J average. -/
theorem equilibriumWeightedRadialOperator_one (ρ : ℂ → ℝ) :
    equilibriumWeightedRadialOperator 1 ρ = equilibriumRadialAverage ρ := by
  funext x
  simp only [equilibriumWeightedRadialOperator, equilibriumRadialAverage,
    equilibriumUnitIntervalMeasure, intervalIntegral.integral_of_le zero_le_one, pow_one, smul_eq_mul]

end RepulsiveCoulomb
