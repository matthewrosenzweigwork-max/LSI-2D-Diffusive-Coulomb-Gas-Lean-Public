import LeanResearch.RepulsiveCoulomb.CoulombGaussianExponential
import LeanResearch.RepulsiveCoulomb.PointOuterCutoff
import LeanResearch.RepulsiveCoulomb.CutoffPairEnergy

/-! Sharpness of the physical planar Gaussian logarithmic Sobolev rate.
Every cutoff is a literal compact smooth function. Mass and gradient energy
converge by Gaussian dominated convergence, and extended entropy passes by
Fatou. The resulting upper bound has no cutoff or analytic hypothesis. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open PeriodicAttractiveLogGas
open scoped Topology ENNReal
namespace RepulsiveCoulomb

/-- The analytic exponential witness is, in particular, C∞ in the exact
regularity index used by the original TestFunction class. -/
theorem coulombGaussianExponentialWitness_smooth (β : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (coulombGaussianExponentialWitness β) :=
  (coulombGaussianExponentialWitness_contDiff β).of_le le_top

def coulombGaussianSmoothCutoff (f : ℂ → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (n : ℕ) :
    TestFunction (⊤ : Opens ℂ) ℝ ⊤ :=
  ⟨fun z => pointOuterTestFunction n z * f z,
    (pointOuterTestFunction n).contDiff.mul hf,
    (pointOuterTestFunction n).hasCompactSupport.mul_right, by simp⟩

theorem coulombGaussianSmoothCutoff_apply (f : ℂ → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (n : ℕ) (z : ℂ) :
    coulombGaussianSmoothCutoff f hf n z = pointOuterTestFunction n z * f z := rfl

theorem coulombGaussian_outer_mem (n : ℕ) (z : ℂ) :
    0 ≤ pointOuterTestFunction n z ∧ pointOuterTestFunction n z ≤ 1 :=
  ⟨(pointCutoffBump 0 (pointOuterRadius n) (pointOuterRadius_pos n)).nonneg,
    (pointCutoffBump 0 (pointOuterRadius n) (pointOuterRadius_pos n)).le_one⟩

theorem coulombGaussianSmoothCutoff_tendsto (f : ℂ → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (z : ℂ) :
    Tendsto (fun n => coulombGaussianSmoothCutoff f hf n z) atTop (𝓝 (f z)) := by
  simpa only [coulombGaussianSmoothCutoff_apply, one_mul] using
    (pointOuterTestFunction_tendsto_one z).mul_const (f z)

theorem coulombGaussian_outer_gradient_tendsto (z : ℂ) :
    Tendsto (fun n => gradient (pointOuterTestFunction n : ℂ → ℝ) z) atTop (𝓝 0) := by
  obtain ⟨B, hB, hb⟩ := exists_pointCutoffBump_gradient_bound
  apply squeeze_zero_norm (a := fun n => B / pointOuterRadius n)
  · intro n
    exact hb 0 (pointOuterRadius n) (pointOuterRadius_pos n) z
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul B
    simpa only [pointOuterRadius, div_eq_mul_inv, mul_zero, one_mul] using h

theorem coulombGaussianSmoothCutoff_gradient (f : ℂ → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (n : ℕ) (z : ℂ) :
    gradient (coulombGaussianSmoothCutoff f hf n : ℂ → ℝ) z =
      pointOuterTestFunction n z • gradient f z +
        f z • gradient (pointOuterTestFunction n : ℂ → ℝ) z :=
  physical_gradient_mul ((pointOuterTestFunction n).contDiff.differentiable (by simp) z)
    (hf.differentiable (by simp) z)

theorem coulombGaussianSmoothCutoff_gradient_tendsto (f : ℂ → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (z : ℂ) :
    Tendsto (fun n => gradient (coulombGaussianSmoothCutoff f hf n : ℂ → ℝ) z)
      atTop (𝓝 (gradient f z)) := by
  simp_rw [coulombGaussianSmoothCutoff_gradient]
  have h := ((pointOuterTestFunction_tendsto_one z).smul
      (tendsto_const_nhds (x := gradient f z))).add
    ((tendsto_const_nhds (x := f z)).smul (coulombGaussian_outer_gradient_tendsto z))
  simpa only [one_smul, smul_zero, add_zero] using h

theorem coulombGaussianSmoothCutoff_mass_tendsto (μ : Measure ℂ) (f : ℂ → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hi : Integrable (fun z => f z ^ 2) μ) :
    Tendsto (fun n => ∫ z, coulombGaussianSmoothCutoff f hf n z ^ 2 ∂μ)
      atTop (𝓝 (∫ z, f z ^ 2 ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun z => f z ^ 2)
  · intro n
    exact ((coulombGaussianSmoothCutoff f hf n).continuous.pow 2).aestronglyMeasurable
  · exact hi
  · intro n
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), coulombGaussianSmoothCutoff_apply,
      mul_pow]
    have hχ := coulombGaussian_outer_mem n z
    have hχ2 : pointOuterTestFunction n z ^ 2 ≤ 1 := by nlinarith
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hχ2 (sq_nonneg (f z))
  · exact Eventually.of_forall fun z => (coulombGaussianSmoothCutoff_tendsto f hf z).pow 2

theorem coulombGaussianSmoothCutoff_energy_tendsto (μ : Measure ℂ) (f : ℂ → ℝ)
    (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f) (hi : Integrable (fun z => f z ^ 2) μ)
    (hE : Integrable (fun z => ‖gradient f z‖ ^ 2) μ) :
    Tendsto (fun n => ∫ z, ‖gradient (coulombGaussianSmoothCutoff f hf n : ℂ → ℝ) z‖ ^ 2 ∂μ)
      atTop (𝓝 (∫ z, ‖gradient f z‖ ^ 2 ∂μ)) := by
  obtain ⟨B, hB, hb⟩ := exists_pointCutoffBump_gradient_bound
  apply tendsto_integral_of_dominated_convergence
    (fun z => 2 * ‖gradient f z‖ ^ 2 + 2 * B ^ 2 * f z ^ 2)
  · intro n
    have hg : Continuous (gradient (coulombGaussianSmoothCutoff f hf n : ℂ → ℝ)) :=
      ((coulombGaussianSmoothCutoff f hf n).contDiff.gradient_right
        (m := 0) (by simp)).continuous
    exact (hg.norm.pow 2).aestronglyMeasurable
  · exact (hE.const_mul 2).add (hi.const_mul (2 * B ^ 2))
  · intro n
    filter_upwards [] with z
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hχ := coulombGaussian_outer_mem n z
    have hχ2 : pointOuterTestFunction n z ^ 2 ≤ 1 := by nlinarith
    have hR : 1 ≤ pointOuterRadius n := by
      unfold pointOuterRadius
      linarith [Nat.cast_nonneg (α := ℝ) n]
    have hgrad : ‖gradient (pointOuterTestFunction n : ℂ → ℝ) z‖ ≤ B :=
      (hb 0 (pointOuterRadius n) (pointOuterRadius_pos n) z).trans
        (div_le_self hB.le hR)
    have hgrad2 : ‖gradient (pointOuterTestFunction n : ℂ → ℝ) z‖ ^ 2 ≤ B ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hgrad 2
    have hp := physical_product_gradient_sq_le
      ((pointOuterTestFunction n).contDiff.differentiable (by simp) z)
      (hf.differentiable (by simp) z)
    change ‖gradient (coulombGaussianSmoothCutoff f hf n : ℂ → ℝ) z‖ ^ 2 ≤ _ at hp
    have h1 := mul_le_mul_of_nonneg_right hχ2 (sq_nonneg ‖gradient f z‖)
    have h2 := mul_le_mul_of_nonneg_left hgrad2 (sq_nonneg (f z))
    nlinarith
  · exact Eventually.of_forall fun z =>
      ((coulombGaussianSmoothCutoff_gradient_tendsto f hf z).norm).pow 2

/-- A core inequality applies to smooth finite-energy functions by explicit
outer cutoffs. This is the approximation argument used below, not an assumed
closure or an alternative definition of Gaussian LSI. -/
theorem coulombGaussian_core_lsi_smooth_extension (μ : Measure ℂ) (K : ℝ)
    (hcore : ∀ φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤,
      entropy μ (fun z => φ z ^ 2) ≤ ((K * ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂μ : ℝ) : EReal))
    (f : ℂ → ℝ) (hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f)
    (hi : Integrable (fun z => f z ^ 2) μ)
    (hE : Integrable (fun z => ‖gradient f z‖ ^ 2) μ) :
    entropy μ (fun z => f z ^ 2) ≤ ((K * ∫ z, ‖gradient f z‖ ^ 2 ∂μ : ℝ) : EReal) := by
  apply entropy_le_of_ae_tendsto
    (F := fun n z => coulombGaussianSmoothCutoff f hf n z ^ 2)
    (b := fun n => K * ∫ z, ‖gradient (coulombGaussianSmoothCutoff f hf n : ℂ → ℝ) z‖ ^ 2 ∂μ)
  · intro n
    exact ((coulombGaussianSmoothCutoff f hf n).continuous.pow 2).measurable.aemeasurable
  · exact Eventually.of_forall fun z => (coulombGaussianSmoothCutoff_tendsto f hf z).pow 2
  · exact coulombGaussianSmoothCutoff_mass_tendsto μ f hf hi
  · exact (coulombGaussianSmoothCutoff_energy_tendsto μ f hf hi hE).const_mul K
  · intro n
    exact hcore (coulombGaussianSmoothCutoff f hf n)

/-- Genuine sharp upper bound for the original compact smooth test class. -/
theorem coulombCenterGaussian_core_lsi_rate_le {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hLSI : ∀ φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤,
      entropy (coulombCenterGaussian β) (fun z => φ z ^ 2) ≤
        (((2 / ρ) * ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β : ℝ) : EReal)) :
    ρ ≤ β := by
  apply coulombGaussianExponentialWitness_rate_le hβ hρ
  exact coulombGaussian_core_lsi_smooth_extension (coulombCenterGaussian β) (2 / ρ)
    hLSI (coulombGaussianExponentialWitness β) (coulombGaussianExponentialWitness_smooth β)
    (coulombGaussianExponentialWitness_square_integrable hβ)
    (coulombGaussianExponentialWitness_gradient_square_integrable hβ)

/-- Above β there is an actual compactly supported smooth counterexample. -/
theorem coulombCenterGaussian_exists_core_lsi_counterexample {β ρ : ℝ}
    (hβ : 0 < β) (hρ : β < ρ) :
    ∃ φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤,
      ¬ entropy (coulombCenterGaussian β) (fun z => φ z ^ 2) ≤
        (((2 / ρ) * ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β : ℝ) : EReal) := by
  by_contra h
  push_neg at h
  exact (not_le_of_gt hρ) (coulombCenterGaussian_core_lsi_rate_le hβ (hβ.trans hρ) h)


/-- The counterexamples occur among the explicit radial cutoffs of the
exponential extremizer, rather than only in an abstract compact-test class. -/
theorem coulombCenterGaussian_exists_cutoff_lsi_counterexample {β ρ : ℝ}
    (hβ : 0 < β) (hρ : β < ρ) :
    ∃ n : ℕ,
      let φ := coulombGaussianSmoothCutoff (coulombGaussianExponentialWitness β)
        (coulombGaussianExponentialWitness_smooth β) n
      ¬ entropy (coulombCenterGaussian β) (fun z => φ z ^ 2) ≤
        (((2 / ρ) * ∫ z, ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β : ℝ) : EReal) := by
  by_contra h
  push_neg at h
  have hi := coulombGaussianExponentialWitness_square_integrable hβ
  have hE := coulombGaussianExponentialWitness_gradient_square_integrable hβ
  let f := coulombGaussianExponentialWitness β
  have hf : ContDiff ℝ (↑(⊤ : ℕ∞)) f := coulombGaussianExponentialWitness_smooth β
  apply (not_le_of_gt hρ)
  apply coulombGaussianExponentialWitness_rate_le hβ (hβ.trans hρ)
  apply entropy_le_of_ae_tendsto
    (F := fun n z => coulombGaussianSmoothCutoff f hf n z ^ 2)
    (b := fun n => (2 / ρ) * ∫ z,
      ‖gradient (coulombGaussianSmoothCutoff f hf n : ℂ → ℝ) z‖ ^ 2 ∂coulombCenterGaussian β)
  · intro n
    exact ((coulombGaussianSmoothCutoff f hf n).continuous.pow 2).measurable.aemeasurable
  · exact Eventually.of_forall fun z => (coulombGaussianSmoothCutoff_tendsto f hf z).pow 2
  · exact coulombGaussianSmoothCutoff_mass_tendsto _ f hf hi
  · exact (coulombGaussianSmoothCutoff_energy_tendsto _ f hf hi hE).const_mul (2 / ρ)
  · intro n
    exact le_of_not_gt (h n)

end RepulsiveCoulomb
