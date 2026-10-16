import LeanResearch.RepulsiveCoulomb.CoulombGaussianMehlerRegularity

/-! Differentiating the literal Mehler interpolation. Uniform domination is
proved on every compact subinterval of (0,1), using the Gaussian first moment. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal RealInnerProductSpace
namespace RepulsiveCoulomb

def coulombGaussianInterpolationNoise (s : ℝ) : ℝ := Real.sqrt (1 - s ^ 2)

def coulombGaussianInterpolation (β s : ℝ) (g : ℂ → ℝ) : ℂ → ℝ :=
  coulombGaussianAverage β s (coulombGaussianInterpolationNoise s) g

def coulombGaussianInterpolationVelocity (s : ℝ) (x y : ℂ) : ℂ :=
  x + (-s / coulombGaussianInterpolationNoise s) • y

def coulombGaussianInterpolationDerivative (β s : ℝ) (g : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, fderiv ℝ g (s • x + coulombGaussianInterpolationNoise s • y)
    (coulombGaussianInterpolationVelocity s x y) ∂coulombCenterGaussian β

def coulombGaussianInterpolationEntropy (β : ℝ) (g : ℂ → ℝ) (s : ℝ) : ℝ :=
  ∫ x, coulombGaussianInterpolation β s g x * Real.log (coulombGaussianInterpolation β s g x)
    ∂coulombCenterGaussian β

theorem coulombGaussianInterpolationNoise_pos {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    0 < coulombGaussianInterpolationNoise s := by
  apply Real.sqrt_pos.2
  nlinarith

theorem coulombGaussianInterpolationNoise_sq {s : ℝ} (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    s ^ 2 + coulombGaussianInterpolationNoise s ^ 2 = 1 := by
  rw [coulombGaussianInterpolationNoise, Real.sq_sqrt (by nlinarith : 0 ≤ 1 - s ^ 2)]
  ring

theorem coulombGaussianInterpolationNoise_continuous : Continuous coulombGaussianInterpolationNoise := by
  unfold coulombGaussianInterpolationNoise
  fun_prop

theorem coulombGaussianInterpolationNoise_hasDerivAt {s : ℝ} (hs : 0 ≤ s) (hs1 : s < 1) :
    HasDerivAt coulombGaussianInterpolationNoise (-s / coulombGaussianInterpolationNoise s) s := by
  have hp : 0 < 1 - s ^ 2 := by nlinarith
  change HasDerivAt (fun t => Real.sqrt (1 - t ^ 2)) (-s / Real.sqrt (1 - s ^ 2)) s
  have h := ((hasDerivAt_const s (1 : ℝ)).sub ((hasDerivAt_id s).pow 2)).sqrt hp.ne'
  dsimp only [Pi.sub_apply, Pi.pow_apply, id_eq] at h
  convert h using 1 <;> ring

theorem coulombGaussianInterpolationNoise_antitone {s U : ℝ}
    (hs : 0 ≤ s) (hsU : s ≤ U) :
    coulombGaussianInterpolationNoise U ≤ coulombGaussianInterpolationNoise s := by
  apply Real.sqrt_le_sqrt
  nlinarith

theorem coulombGaussianInterpolationVelocity_norm_le {s U : ℝ}
    (hU : U < 1) (hs : 0 ≤ s) (hsU : s ≤ U) (x y : ℂ) :
    ‖coulombGaussianInterpolationVelocity s x y‖ ≤
      ‖x‖ + (coulombGaussianInterpolationNoise U)⁻¹ * ‖y‖ := by
  have hU0 : 0 ≤ U := hs.trans hsU
  have hns := coulombGaussianInterpolationNoise_pos hs (hsU.trans_lt hU)
  have hnU := coulombGaussianInterpolationNoise_pos hU0 hU
  have hnoise := coulombGaussianInterpolationNoise_antitone hs hsU
  have hquot : |-s / coulombGaussianInterpolationNoise s| ≤
      (coulombGaussianInterpolationNoise U)⁻¹ := by
    rw [abs_div, abs_neg, abs_of_nonneg hs, abs_of_pos hns]
    calc
      s / coulombGaussianInterpolationNoise s ≤ 1 / coulombGaussianInterpolationNoise s :=
        div_le_div_of_nonneg_right ((hsU.trans_lt hU).le) hns.le
      _ ≤ 1 / coulombGaussianInterpolationNoise U :=
        div_le_div_of_nonneg_left (by norm_num) hnU hnoise
      _ = _ := one_div _
  unfold coulombGaussianInterpolationVelocity
  calc
    _ ≤ ‖x‖ + ‖(-s / coulombGaussianInterpolationNoise s) • y‖ := norm_add_le _ _
    _ = ‖x‖ + |-s / coulombGaussianInterpolationNoise s| * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs]
    _ ≤ _ := by linarith [mul_le_mul_of_nonneg_right hquot (norm_nonneg y)]

/-- The real affine curve has the explicitly computed interpolation velocity. -/
theorem coulombGaussianInterpolation_curve_hasDerivAt {s : ℝ}
    (hs : 0 ≤ s) (hs1 : s < 1) (x y : ℂ) :
    HasDerivAt (fun s => s • x + coulombGaussianInterpolationNoise s • y)
      (coulombGaussianInterpolationVelocity s x y) s := by
  have hd := ((hasDerivAt_id s).smul_const x).add
    ((coulombGaussianInterpolationNoise_hasDerivAt hs hs1).smul_const y)
  convert hd using 1
  · funext r
    rfl
  · simp only [one_smul, coulombGaussianInterpolationVelocity]

/-- Actual derivative of the Mehler integral in its interpolation parameter. -/
theorem coulombGaussianInterpolation_hasDerivAt {β s U : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) {M D : ℝ}
    (hM : ∀ z, ‖g z‖ ≤ M) (hD : ∀ z, ‖fderiv ℝ g z‖ ≤ D)
    (hs : 0 < s) (hsU : s < U) (hU : U < 1) (x : ℂ) :
    HasDerivAt (fun s => coulombGaussianInterpolation β s g x)
      (coulombGaussianInterpolationDerivative β s g x) s := by
  letI := coulombCenterGaussian_isProbability hβ
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ g 0)).trans (hD 0)
  have hcg := hg.continuous_fderiv (by norm_num)
  have hnoise := coulombGaussianInterpolationNoise_continuous
  have hi : Integrable (fun y : ℂ => D * (‖x‖ +
      (coulombGaussianInterpolationNoise U)⁻¹ * ‖y‖)) (coulombCenterGaussian β) :=
    ((integrable_const ‖x‖).add
      ((coulombGaussian_norm_integrable hβ).const_mul _)).const_mul D
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := coulombCenterGaussian β) (s := Ioo 0 U)
    (F := fun s y => g (s • x + coulombGaussianInterpolationNoise s • y))
    (F' := fun s y => fderiv ℝ g (s • x + coulombGaussianInterpolationNoise s • y)
      (coulombGaussianInterpolationVelocity s x y))
    (bound := fun y => D * (‖x‖ + (coulombGaussianInterpolationNoise U)⁻¹ * ‖y‖))
    (Ioo_mem_nhds hs hsU)
    (Eventually.of_forall (fun s => by fun_prop))
    (coulombGaussianAverage_integrable hβ hg.continuous hM s _ x)
    (by dsimp [coulombGaussianInterpolationVelocity]; fun_prop)
    (Eventually.of_forall (fun y r hr => ?_)) hi
    (Eventually.of_forall (fun y r hr => ?_))
  · exact hd.2
  · exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hD _)
        (coulombGaussianInterpolationVelocity_norm_le hU hr.1.le hr.2.le x y)
        (norm_nonneg _) hD0)
  · exact (hg.differentiable (by norm_num) _).hasFDerivAt.comp_hasDerivAt r
      (coulombGaussianInterpolation_curve_hasDerivAt hr.1.le (hr.2.trans hU) x y)

/-- A uniform first-moment bound for the actual interpolation derivative. -/
theorem coulombGaussianInterpolationDerivative_norm_le {β s U : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} {D : ℝ} (hD : ∀ z, ‖fderiv ℝ g z‖ ≤ D)
    (hs : 0 ≤ s) (hsU : s ≤ U) (hU : U < 1) (x : ℂ) :
    ‖coulombGaussianInterpolationDerivative β s g x‖ ≤
      D * (‖x‖ + (coulombGaussianInterpolationNoise U)⁻¹ *
        ∫ y : ℂ, ‖y‖ ∂coulombCenterGaussian β) := by
  letI := coulombCenterGaussian_isProbability hβ
  have hD0 : 0 ≤ D := (norm_nonneg (fderiv ℝ g 0)).trans (hD 0)
  have hi : Integrable (fun y : ℂ => D * (‖x‖ +
      (coulombGaussianInterpolationNoise U)⁻¹ * ‖y‖)) (coulombCenterGaussian β) :=
    ((integrable_const ‖x‖).add
      ((coulombGaussian_norm_integrable hβ).const_mul _)).const_mul D
  have hbound : ∀ᵐ y ∂coulombCenterGaussian β,
      ‖fderiv ℝ g (s • x + coulombGaussianInterpolationNoise s • y)
        (coulombGaussianInterpolationVelocity s x y)‖ ≤
      D * (‖x‖ + (coulombGaussianInterpolationNoise U)⁻¹ * ‖y‖) := by
    filter_upwards [] with y
    exact (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul (hD _) (coulombGaussianInterpolationVelocity_norm_le hU hs hsU x y)
        (norm_nonneg _) hD0)
  have h := norm_integral_le_of_norm_le hi hbound
  rw [integral_const_mul, integral_add (integrable_const _) ((coulombGaussian_norm_integrable hβ).const_mul _),
    integral_const_mul, integral_const, probReal_univ, one_smul] at h
  exact h

/-- Measurability of the parameter derivative follows from the literal
jointly continuous integrand and measurability of parameter integrals. -/
theorem coulombGaussianInterpolationDerivative_stronglyMeasurable {β : ℝ} (hβ : 0 < β)
    {g : ℂ → ℝ} (hg : ContDiff ℝ 1 g) (s : ℝ) :
    StronglyMeasurable (coulombGaussianInterpolationDerivative β s g) := by
  letI := coulombCenterGaussian_isProbability hβ
  have hcg := hg.continuous_fderiv (by norm_num)
  have hc : Continuous (fun p : ℂ × ℂ =>
      fderiv ℝ g (s • p.1 + coulombGaussianInterpolationNoise s • p.2)
        (coulombGaussianInterpolationVelocity s p.1 p.2)) := by
    dsimp [coulombGaussianInterpolationVelocity]
    fun_prop
  exact hc.stronglyMeasurable.integral_prod_right'

end RepulsiveCoulomb
