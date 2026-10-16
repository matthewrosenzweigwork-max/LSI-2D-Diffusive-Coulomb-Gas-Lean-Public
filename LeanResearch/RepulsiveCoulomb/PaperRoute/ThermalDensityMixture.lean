module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCappedLogEnergy

@[expose] public section

/-! Literal affine probability-density laws,
actual moment identities, and weak convergence under an integrable density
majorant. No logarithmic cross-energy is used. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

def thermalDensityMixture (t : ℝ) (ρ σ : ℂ → ℝ) (x : ℂ) : ℝ :=
  t * ρ x + (1 - t) * σ x

def thermalProbabilityOfDensity {ρ : ℂ → ℝ}
    (h0 : ∀ x, 0 ≤ ρ x) (hi : Integrable ρ) (hmass : (∫ x, ρ x) = 1) :
    ProbabilityMeasure ℂ :=
  ⟨equilibriumDensityMeasure ρ, equilibriumDensityMeasure_probability h0 hi hmass⟩

theorem thermalDensityMixture_measurable {ρ σ : ℂ → ℝ}
    (hρ : Measurable ρ) (hσ : Measurable σ) (t : ℝ) :
    Measurable (thermalDensityMixture t ρ σ) :=
  (hρ.const_mul t).add (hσ.const_mul (1 - t))

theorem thermalDensityMixture_nonneg {ρ σ : ℂ → ℝ}
    (hρ : ∀ x, 0 ≤ ρ x) (hσ : ∀ x, 0 ≤ σ x) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (x : ℂ) : 0 ≤ thermalDensityMixture t ρ σ x :=
  add_nonneg (mul_nonneg ht0 (hρ x)) (mul_nonneg (sub_nonneg.mpr ht1) (hσ x))

theorem thermalDensityMixture_integrable {ρ σ : ℂ → ℝ}
    (hρ : Integrable ρ) (hσ : Integrable σ) (t : ℝ) :
    Integrable (thermalDensityMixture t ρ σ) :=
  (hρ.const_mul t).add (hσ.const_mul (1 - t))

theorem thermalDensityMixture_integral {ρ σ : ℂ → ℝ}
    (hρ : Integrable ρ) (hσ : Integrable σ)
    (hmρ : (∫ x, ρ x) = 1) (hmσ : (∫ x, σ x) = 1) (t : ℝ) :
    (∫ x, thermalDensityMixture t ρ σ x) = 1 := by
  change (∫ x, t * ρ x + (1 - t) * σ x) = 1
  rw [integral_add (hρ.const_mul _) (hσ.const_mul _),
    integral_const_mul, integral_const_mul, hmρ, hmσ]
  ring

theorem thermalDensityMixture_secondMoment_integrable {ρ σ : ℂ → ℝ}
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hσ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * σ x)) (t : ℝ) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * thermalDensityMixture t ρ σ x) := by
  apply ((hρ2.const_mul t).add (hσ2.const_mul (1 - t))).congr
  exact Eventually.of_forall fun x => by dsimp [thermalDensityMixture]; ring

theorem thermalDensityMixture_secondMoment_integral {ρ σ : ℂ → ℝ}
    (hρ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * ρ x))
    (hσ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2 * σ x)) (t : ℝ) :
    (∫ x : ℂ, ‖x‖ ^ 2 * thermalDensityMixture t ρ σ x) =
      t * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) + (1 - t) * (∫ x : ℂ, ‖x‖ ^ 2 * σ x) := by
  have he : (fun x : ℂ => ‖x‖ ^ 2 * thermalDensityMixture t ρ σ x) =
      (fun x : ℂ => t * (‖x‖ ^ 2 * ρ x) + (1 - t) * (‖x‖ ^ 2 * σ x)) := by
    funext x
    dsimp [thermalDensityMixture]
    ring
  rw [he, integral_add (hρ2.const_mul _) (hσ2.const_mul _), integral_const_mul, integral_const_mul]

/-- The density mixture is exactly the affine mixture of the actual laws. -/
theorem thermalDensityMixture_measure {ρ σ : ℂ → ℝ}
    (hρm : Measurable ρ) (hσm : Measurable σ)
    (hρ0 : ∀ x, 0 ≤ ρ x) (hσ0 : ∀ x, 0 ≤ σ x)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    equilibriumDensityMeasure (thermalDensityMixture t ρ σ) =
      ENNReal.ofReal t • equilibriumDensityMeasure ρ +
        ENNReal.ofReal (1 - t) • equilibriumDensityMeasure σ := by
  have he : (fun x => ENNReal.ofReal (thermalDensityMixture t ρ σ x)) =
      ENNReal.ofReal t • (fun x => ENNReal.ofReal (ρ x)) +
        ENNReal.ofReal (1 - t) • (fun x => ENNReal.ofReal (σ x)) := by
    funext x
    simp only [thermalDensityMixture, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      ENNReal.ofReal_add (mul_nonneg ht0 (hρ0 x))
        (mul_nonneg (sub_nonneg.mpr ht1) (hσ0 x)),
      ENNReal.ofReal_mul ht0, ENNReal.ofReal_mul (sub_nonneg.mpr ht1)]
  unfold equilibriumDensityMeasure
  rw [he, withDensity_add_left ((hρm.ennreal_ofReal).const_smul _) _,
    withDensity_smul _ hρm.ennreal_ofReal, withDensity_smul _ hσm.ennreal_ofReal]

/-- Pointwise convergence under an actual integrable density majorant implies
weak convergence of the literal density probability laws. -/
theorem thermalProbabilityOfDensity_tendsto_of_dominated
    {ρs : ℕ → ℂ → ℝ} {ρ B : ℂ → ℝ}
    (hρsm : ∀ n, Measurable (ρs n)) (hρs0 : ∀ n x, 0 ≤ ρs n x)
    (hρsi : ∀ n, Integrable (ρs n)) (hρsmass : ∀ n, (∫ x, ρs n x) = 1)
    (hρm : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ)
    (hρmass : (∫ x, ρ x) = 1) (hB : Integrable B)
    (hdom : ∀ n x, ρs n x ≤ B x)
    (hpoint : ∀ x, Tendsto (fun n => ρs n x) atTop (𝓝 (ρ x))) :
    Tendsto (fun n => thermalProbabilityOfDensity (hρs0 n) (hρsi n) (hρsmass n)) atTop
      (𝓝 (thermalProbabilityOfDensity hρ0 hρi hρmass)) := by
  apply ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mpr
  intro f
  have ht := tendsto_integral_of_dominated_convergence (fun x => ‖f‖ * B x)
    (fun n => ((hρsm n).mul f.continuous.measurable).aestronglyMeasurable)
    (hB.const_mul ‖f‖)
    (fun n => Eventually.of_forall fun x => by
      change ‖ρs n x * f x‖ ≤ ‖f‖ * B x
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hρs0 n x)]
      have hB0 : 0 ≤ B x := (hρs0 n x).trans (hdom n x)
      calc
        ρs n x * ‖f x‖ ≤ B x * ‖f‖ :=
          mul_le_mul (hdom n x) (f.norm_coe_le_norm x) (norm_nonneg _) hB0
        _ = _ := mul_comm _ _)
    (Eventually.of_forall fun x => (hpoint x).mul_const (f x))
  have he (n : ℕ) : (∫ x, f x ∂(thermalProbabilityOfDensity (hρs0 n) (hρsi n) (hρsmass n))) =
      ∫ x, ρs n x * f x := integral_equilibriumDensityMeasure (hρsm n) (hρs0 n) f
  have he0 : (∫ x, f x ∂(thermalProbabilityOfDensity hρ0 hρi hρmass)) =
      ∫ x, ρ x * f x := integral_equilibriumDensityMeasure hρm hρ0 f
  simpa only [he, he0, Pi.mul_apply] using ht

end RepulsiveCoulomb.PaperRoute
