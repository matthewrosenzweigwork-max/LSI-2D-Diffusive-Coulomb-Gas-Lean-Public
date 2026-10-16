module

public import LeanResearch.RepulsiveCoulomb.CoulombCenterGaussian
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityMeasure
public import Mathlib.Analysis.Complex.OperatorNorm

@[expose] public section

/-! Exact exponential witnesses for the planar center Gaussian. The integrals
are computed from the literal density by translation, without Gaussian LSI,
Poincare, semigroup, or moment assumptions. -/
noncomputable section
open Set MeasureTheory Filter
open PeriodicAttractiveLogGas
open scoped Topology ENNReal
namespace RepulsiveCoulomb

/-- The actual normalized density of the planar center law. -/
def coulombGaussianDensity (β : ℝ) (z : ℂ) : ℝ :=
  (β / (2 * Real.pi)) * Real.exp (-β * ‖z‖ ^ 2 / 2)

theorem coulombGaussianDensity_eq_equilibrium (β : ℝ) (z : ℂ) :
    coulombGaussianDensity β z = equilibriumGaussian (β / 2) z := by
  unfold coulombGaussianDensity equilibriumGaussian
  congr 1
  · ring
  · congr 1
    ring

theorem coulombGaussianDensity_continuous (β : ℝ) :
    Continuous (coulombGaussianDensity β) := by
  unfold coulombGaussianDensity
  fun_prop

theorem coulombGaussianDensity_pos {β : ℝ} (hβ : 0 < β) (z : ℂ) :
    0 < coulombGaussianDensity β z := by
  rw [coulombGaussianDensity_eq_equilibrium]
  exact equilibriumGaussian_pos (by positivity) z

theorem coulombCenterGaussian_eq_density {β : ℝ} (hβ : 0 < β) :
    coulombCenterGaussian β = equilibriumDensityMeasure (coulombGaussianDensity β) :=
  coulombCenterGaussian_density hβ

theorem coulombGaussianDensity_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (coulombGaussianDensity β) := by
  have he : coulombGaussianDensity β = equilibriumGaussian (β / 2) :=
    funext (coulombGaussianDensity_eq_equilibrium β)
  rw [he]
  exact equilibriumGaussian_integrable (show 0 < β / 2 by positivity)

theorem coulombGaussianDensity_mass {β : ℝ} (hβ : 0 < β) :
    (∫ z : ℂ, coulombGaussianDensity β z) = 1 := by
  simpa only [coulombGaussianDensity_eq_equilibrium] using
    integral_equilibriumGaussian (show 0 < β / 2 by positivity)

theorem coulombCenterGaussian_integrable_iff {β : ℝ} (hβ : 0 < β) (f : ℂ → ℝ) :
    Integrable f (coulombCenterGaussian β) ↔
      Integrable (fun z => f z * coulombGaussianDensity β z) := by
  rw [coulombCenterGaussian_eq_density hβ]
  exact equilibriumDensityMeasure_integrable_iff
    (coulombGaussianDensity_continuous β).measurable
    (fun z => (coulombGaussianDensity_pos hβ z).le) f

theorem integral_coulombCenterGaussian {β : ℝ} (hβ : 0 < β) (f : ℂ → ℝ) :
    (∫ z, f z ∂coulombCenterGaussian β) =
      ∫ z : ℂ, coulombGaussianDensity β z * f z := by
  rw [coulombCenterGaussian_eq_density hβ]
  exact integral_equilibriumDensityMeasure (coulombGaussianDensity_continuous β).measurable
    (fun z => (coulombGaussianDensity_pos hβ z).le) f

theorem coulombGaussianDensity_neg (β : ℝ) (z : ℂ) :
    coulombGaussianDensity β (-z) = coulombGaussianDensity β z := by
  simp [coulombGaussianDensity]

/-- Completion of the square, at the unit translation needed for sharpness. -/
theorem coulombGaussianDensity_exponential_tilt (β : ℝ) (z : ℂ) :
    coulombGaussianDensity β z * Real.exp (β * z.re) =
      Real.exp (β / 2) * coulombGaussianDensity β (z - 1) := by
  unfold coulombGaussianDensity
  rw [mul_assoc, ← Real.exp_add, mul_left_comm, ← Real.exp_add]
  congr 2
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.one_re, Complex.one_im, sub_zero]
  ring

theorem coulombGaussianDensity_re_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z : ℂ => z.re * coulombGaussianDensity β z) := by
  have h2 : Integrable (fun z : ℂ => ‖z‖ ^ 2 * coulombGaussianDensity β z) := by
    simpa only [coulombGaussianDensity_eq_equilibrium] using
      equilibriumGaussian_secondMoment_integrable (show 0 < β / 2 by positivity)
  apply ((coulombGaussianDensity_integrable hβ).add h2).mono'
    (Complex.continuous_re.mul (coulombGaussianDensity_continuous β)).aestronglyMeasurable
  filter_upwards [] with z
  dsimp only [Pi.add_apply, Pi.mul_apply]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (coulombGaussianDensity_pos hβ z)]
  have hr : |z.re| ≤ 1 + ‖z‖ ^ 2 := by
    have h := Complex.abs_re_le_norm z
    nlinarith [sq_nonneg (‖z‖ - 1)]
  nlinarith [mul_le_mul_of_nonneg_right hr (coulombGaussianDensity_pos hβ z).le]

theorem coulombGaussianDensity_re_integral (β : ℝ) :
    (∫ z : ℂ, z.re * coulombGaussianDensity β z) = 0 := by
  have h := integral_neg_eq_self (fun z : ℂ => z.re * coulombGaussianDensity β z) volume
  simp only [Complex.neg_re, coulombGaussianDensity_neg, neg_mul, integral_neg] at h
  linarith

/-- The square of the exponential extremizer has finite mass. -/
theorem coulombGaussian_exp_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z : ℂ => Real.exp (β * z.re)) (coulombCenterGaussian β) := by
  rw [coulombCenterGaussian_integrable_iff hβ]
  have h := ((coulombGaussianDensity_integrable hβ).comp_sub_right (1 : ℂ)).const_mul
    (Real.exp (β / 2))
  exact h.congr (Eventually.of_forall (fun z => by
    change Real.exp (β / 2) * coulombGaussianDensity β (z - 1) =
      Real.exp (β * z.re) * coulombGaussianDensity β z
    rw [← coulombGaussianDensity_exponential_tilt]
    ring))

theorem coulombGaussian_exp_integral {β : ℝ} (hβ : 0 < β) :
    (∫ z : ℂ, Real.exp (β * z.re) ∂coulombCenterGaussian β) = Real.exp (β / 2) := by
  rw [integral_coulombCenterGaussian hβ]
  simp_rw [coulombGaussianDensity_exponential_tilt]
  rw [integral_const_mul, integral_sub_right_eq_self, coulombGaussianDensity_mass hβ,
    mul_one]

theorem coulombGaussian_re_exp_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z : ℂ => z.re * Real.exp (β * z.re)) (coulombCenterGaussian β) := by
  rw [coulombCenterGaussian_integrable_iff hβ]
  have h := (((coulombGaussianDensity_re_integrable hβ).add
    (coulombGaussianDensity_integrable hβ)).comp_sub_right (1 : ℂ)).const_mul
      (Real.exp (β / 2))
  exact h.congr (Eventually.of_forall (fun z => by
    dsimp only [Pi.add_apply]
    rw [Complex.sub_re, Complex.one_re]
    calc
      _ = z.re * (Real.exp (β / 2) * coulombGaussianDensity β (z - 1)) := by ring
      _ = _ := by rw [← coulombGaussianDensity_exponential_tilt]; ring))

theorem coulombGaussian_re_exp_integral {β : ℝ} (hβ : 0 < β) :
    (∫ z : ℂ, z.re * Real.exp (β * z.re) ∂coulombCenterGaussian β) =
      Real.exp (β / 2) := by
  rw [integral_coulombCenterGaussian hβ]
  have hp (z : ℂ) : coulombGaussianDensity β z * (z.re * Real.exp (β * z.re)) =
      Real.exp (β / 2) * ((z - 1).re * coulombGaussianDensity β (z - 1) +
        coulombGaussianDensity β (z - 1)) := by
    calc
      _ = z.re * (coulombGaussianDensity β z * Real.exp (β * z.re)) := by ring
      _ = _ := by
        rw [coulombGaussianDensity_exponential_tilt, Complex.sub_re, Complex.one_re]
        ring
  simp_rw [hp]
  have ht := integral_sub_right_eq_self (μ := (volume : Measure ℂ))
    (fun z : ℂ => z.re * coulombGaussianDensity β z + coulombGaussianDensity β z) (1 : ℂ)
  rw [integral_const_mul, ht,
    integral_add (coulombGaussianDensity_re_integrable hβ) (coulombGaussianDensity_integrable hβ),
    coulombGaussianDensity_re_integral, coulombGaussianDensity_mass hβ]
  ring

/-- Smooth (not compactly supported) exact extremizer. Compact approximation
is a separate theorem and must be supplied before using this for a core LSI. -/
def coulombGaussianExponentialWitness (β : ℝ) (z : ℂ) : ℝ := Real.exp ((β / 2) * z.re)

theorem coulombGaussianExponentialWitness_contDiff (β : ℝ) :
    ContDiff ℝ ⊤ (coulombGaussianExponentialWitness β) := by
  unfold coulombGaussianExponentialWitness
  exact (contDiff_const.mul Complex.reCLM.contDiff).exp

theorem coulombGaussianExponentialWitness_sq (β : ℝ) (z : ℂ) :
    coulombGaussianExponentialWitness β z ^ 2 = Real.exp (β * z.re) := by
  unfold coulombGaussianExponentialWitness
  rw [sq, ← Real.exp_add]
  congr 1
  ring

theorem coulombGaussianExponentialWitness_entropy {β : ℝ} (hβ : 0 < β) :
    entropy (coulombCenterGaussian β) (fun z => coulombGaussianExponentialWitness β z ^ 2) =
      ((β / 2 * Real.exp (β / 2) : ℝ) : EReal) := by
  letI := coulombCenterGaussian_isProbability hβ
  simp_rw [coulombGaussianExponentialWitness_sq]
  have hi : Integrable (fun z : ℂ => Real.exp (β * z.re) * Real.log (Real.exp (β * z.re)))
      (coulombCenterGaussian β) := by
    simpa only [Real.log_exp, mul_left_comm, mul_comm, mul_assoc] using
      (coulombGaussian_re_exp_integrable hβ).const_mul β
  rw [entropy_eq_integral (Eventually.of_forall fun z => (Real.exp_pos _).le) hi]
  simp_rw [Real.log_exp]
  have he : (fun z : ℂ => Real.exp (β * z.re) * (β * z.re)) =
      (fun z => β * (z.re * Real.exp (β * z.re))) := by funext z; ring
  rw [he, integral_const_mul, coulombGaussian_re_exp_integral hβ,
    coulombGaussian_exp_integral hβ, Real.log_exp]
  congr 1
  ring

theorem coulombGaussianExponentialWitness_gradient_norm (β : ℝ) (z : ℂ) :
    ‖gradient (coulombGaussianExponentialWitness β) z‖ =
      |β / 2| * coulombGaussianExponentialWitness β z := by
  have hd : HasFDerivAt (coulombGaussianExponentialWitness β)
      (Real.exp ((β / 2) * z.re) • ((β / 2) • Complex.reCLM)) z :=
    ((Complex.reCLM.hasFDerivAt).const_mul (β / 2)).exp
  rw [TauCeti.norm_gradient_eq_norm_fderiv, hd.fderiv, norm_smul, norm_smul,
    Complex.reCLM_norm, mul_one, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]
  exact mul_comm _ _

theorem coulombGaussianExponentialWitness_energy {β : ℝ} (hβ : 0 < β) :
    (∫ z, ‖gradient (coulombGaussianExponentialWitness β) z‖ ^ 2
      ∂coulombCenterGaussian β) = β ^ 2 / 4 * Real.exp (β / 2) := by
  simp_rw [coulombGaussianExponentialWitness_gradient_norm, mul_pow, sq_abs,
    coulombGaussianExponentialWitness_sq]
  rw [integral_const_mul, coulombGaussian_exp_integral hβ]
  ring


theorem coulombGaussianExponentialWitness_square_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z => coulombGaussianExponentialWitness β z ^ 2) (coulombCenterGaussian β) := by
  simpa only [coulombGaussianExponentialWitness_sq] using coulombGaussian_exp_integrable hβ

theorem coulombGaussianExponentialWitness_gradient_square_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun z => ‖gradient (coulombGaussianExponentialWitness β) z‖ ^ 2)
      (coulombCenterGaussian β) := by
  simpa only [coulombGaussianExponentialWitness_gradient_norm, mul_pow,
    coulombGaussianExponentialWitness_sq] using
      (coulombGaussian_exp_integrable hβ).const_mul (|β / 2| ^ 2)

/-- The exact noncompact witness forces the sharp rate once its inequality
has been established. Its admissibility for core inequalities is proved in
the separate compact-cutoff module. -/
theorem coulombGaussianExponentialWitness_rate_le {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (he : entropy (coulombCenterGaussian β) (fun z => coulombGaussianExponentialWitness β z ^ 2) ≤
      (((2 / ρ) * ∫ z, ‖gradient (coulombGaussianExponentialWitness β) z‖ ^ 2
        ∂coulombCenterGaussian β : ℝ) : EReal)) : ρ ≤ β := by
  rw [coulombGaussianExponentialWitness_entropy hβ,
    coulombGaussianExponentialWitness_energy hβ] at he
  have he' : β / 2 * Real.exp (β / 2) ≤
      (2 / ρ) * (β ^ 2 / 4 * Real.exp (β / 2)) := EReal.coe_le_coe_iff.mp he
  have hc : β / 2 ≤ (2 / ρ) * (β ^ 2 / 4) :=
    (mul_le_mul_iff_of_pos_right (Real.exp_pos (β / 2))).mp (by nlinarith [he'])
  have hmul := (mul_le_mul_iff_of_pos_right hρ).mpr hc
  field_simp [hρ.ne'] at hmul
  nlinarith

end RepulsiveCoulomb
