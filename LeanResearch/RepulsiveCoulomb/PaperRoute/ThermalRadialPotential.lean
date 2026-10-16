import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalCanonicalRotation
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Genuine extended logarithmic potentials
retain the positive singular infinity and have an independently integrable
negative part on P² laws. Isometry-invariant minimizer measures give radial
extended potentials. No finiteness or pointwise radiality of an arbitrary
Radon–Nikodym density representative is asserted. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb.PaperRoute

def thermalExtendedLogPotential (μ : ProbabilityMeasure ℂ) (x : ℂ) : EReal :=
  ((∫⁻ y, thermalExtendedPositiveLogKernel (x, y) ∂μ) : EReal) -
    ((∫⁻ y, ENNReal.ofReal (thermalNegativeLogKernel (x, y)) ∂μ) : EReal)

/-- Exact correspondence with the signed extended integral of the unchanged
physical logarithmic kernel. AC makes the fixed spatial diagonal null; no
pointwise full-energy finiteness is silently assumed. -/
theorem thermalExtendedLogPotential_eq_extendedIntegral
    (μ : ProbabilityMeasure ℂ) (hAC : (μ : Measure ℂ) ≪ volume) (x : ℂ) :
    thermalExtendedLogPotential μ x = equilibriumExtendedIntegral (μ : Measure ℂ)
      (fun y => equilibriumLogKernel (x - y)) := by
  let : NullSingletonClass (μ : Measure ℂ) := ⟨fun z => hAC (measure_singleton z)⟩
  have hp : (∫⁻ y, ENNReal.ofReal (equilibriumLogKernel (x - y)) ∂μ) =
      ∫⁻ y, thermalExtendedPositiveLogKernel (x, y) ∂μ := by
    apply lintegral_congr_ae
    filter_upwards [(μ : Measure ℂ).ae_ne x] with y hy
    rw [thermalExtendedPositiveLogKernel_off_diagonal hy.symm,
      ENNReal.ofReal_max, ENNReal.ofReal_zero,
      max_eq_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (-Real.log ‖x - y‖) from bot_le)]
    rfl
  have hn : (∫⁻ y, ENNReal.ofReal (-equilibriumLogKernel (x - y)) ∂μ) =
      ∫⁻ y, ENNReal.ofReal (thermalNegativeLogKernel (x, y)) ∂μ := by
    apply lintegral_congr
    intro y
    rw [thermalNegativeLogKernel_eq_negativePart, ENNReal.ofReal_max, ENNReal.ofReal_zero,
      max_eq_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (-equilibriumLogKernel (x - y)) from bot_le)]
  simp only [thermalExtendedLogPotential, equilibriumExtendedIntegral, hp, hn]

/-- Only an actually integrable point potential is identified with a real
Bochner integral. No such integrability is postulated for all points. -/
theorem thermalExtendedLogPotential_eq_integral
    (μ : ProbabilityMeasure ℂ) (hAC : (μ : Measure ℂ) ≪ volume) (x : ℂ)
    (hi : Integrable (fun y => equilibriumLogKernel (x - y)) μ) :
    thermalExtendedLogPotential μ x = ((∫ y, equilibriumLogKernel (x - y) ∂μ : ℝ) : EReal) := by
  rw [thermalExtendedLogPotential_eq_extendedIntegral μ hAC x,
    equilibriumExtendedIntegral_eq_integral hi]

theorem thermalNegativeLogPotential_integrable (μ : ProbabilityMeasure ℂ)
    (hP2 : Integrable (fun y : ℂ => ‖y‖ ^ 2) μ) (x : ℂ) :
    Integrable (fun y => thermalNegativeLogKernel (x, y)) μ := by
  have hd : Integrable (fun y : ℂ => 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) μ :=
    (integrable_const (2 * ‖x‖ ^ 2)).add (hP2.const_mul 2)
  apply hd.mono'
    (thermalNegativeLogKernel_continuous.comp (continuous_const.prodMk continuous_id)).measurable.aestronglyMeasurable
  exact Eventually.of_forall fun y => by
    change ‖thermalNegativeLogKernel (x, y)‖ ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2
    rw [Real.norm_eq_abs, abs_of_nonneg (thermalNegativeLogKernel_nonneg (x, y))]
    have hlog := (thermal_log_truncation_scalar (dist_nonneg (x := x) (y := y)) (le_refl 0)).2
    have hnon := thermalNegativeLogKernel_nonneg (x, y)
    change thermalNegativeLogKernel (x, y) - min (thermalNegativeLogKernel (x, y)) 0 ≤ _ at hlog
    simp only [min_eq_right hnon, sub_zero, neg_zero, Real.exp_zero, one_mul] at hlog
    exact hlog.trans (thermal_dist_sq_le (x, y))

theorem thermalNegativeLogPotential_lintegral_ne_top (μ : ProbabilityMeasure ℂ)
    (hP2 : Integrable (fun y : ℂ => ‖y‖ ^ 2) μ) (x : ℂ) :
    (∫⁻ y, ENNReal.ofReal (thermalNegativeLogKernel (x, y)) ∂μ) ≠ ∞ := by
  rw [← ofReal_integral_eq_lintegral_ofReal (thermalNegativeLogPotential_integrable μ hP2 x)
    (Eventually.of_forall fun y => thermalNegativeLogKernel_nonneg (x, y))]
  exact ENNReal.ofReal_ne_top

/-- On the genuine P² domain only the independently finite negative part is
converted to its ordinary real integral. Positive infinity is retained. -/
theorem thermalExtendedLogPotential_eq_positive_sub_finite_negative
    (μ : ProbabilityMeasure ℂ) (hP2 : Integrable (fun y : ℂ => ‖y‖ ^ 2) μ) (x : ℂ) :
    thermalExtendedLogPotential μ x =
      ((∫⁻ y, thermalExtendedPositiveLogKernel (x, y) ∂μ) : EReal) -
        ((∫ y, thermalNegativeLogKernel (x, y) ∂μ : ℝ) : EReal) := by
  rw [thermalExtendedLogPotential,
    ← ofReal_integral_eq_lintegral_ofReal (thermalNegativeLogPotential_integrable μ hP2 x)
      (Eventually.of_forall fun y => thermalNegativeLogKernel_nonneg (x, y)),
    EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg fun y => thermalNegativeLogKernel_nonneg (x, y))]

theorem thermalNegativeLogPotential_integral_bound (μ : ProbabilityMeasure ℂ)
    (hP2 : Integrable (fun y : ℂ => ‖y‖ ^ 2) μ) (x : ℂ) :
    (∫ y, thermalNegativeLogKernel (x, y) ∂μ) ≤
      2 * ‖x‖ ^ 2 + 2 * (∫ y : ℂ, ‖y‖ ^ 2 ∂μ) := by
  have hd : Integrable (fun y : ℂ => 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) μ :=
    (integrable_const (2 * ‖x‖ ^ 2)).add (hP2.const_mul 2)
  calc
    _ ≤ ∫ y : ℂ, (2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2) ∂μ := by
      apply integral_mono (thermalNegativeLogPotential_integrable μ hP2 x) hd
      intro y
      have hlog := (thermal_log_truncation_scalar (dist_nonneg (x := x) (y := y)) (le_refl 0)).2
      change thermalNegativeLogKernel (x, y) - min (thermalNegativeLogKernel (x, y)) 0 ≤ _ at hlog
      simp only [min_eq_right (thermalNegativeLogKernel_nonneg (x, y)), sub_zero,
        neg_zero, Real.exp_zero, one_mul] at hlog
      exact hlog.trans (thermal_dist_sq_le (x, y))
    _ = _ := by
      rw [integral_add (integrable_const _) (hP2.const_mul 2)]
      simp only [integral_const_mul, integral_const, probReal_univ, one_smul]

theorem thermalExtendedPositiveLogKernel_isometry (e : ℂ ≃ₗᵢ[ℝ] ℂ) (x y : ℂ) :
    thermalExtendedPositiveLogKernel (e x, e y) = thermalExtendedPositiveLogKernel (x, y) := by
  simp only [thermalExtendedPositiveLogKernel, thermalPositiveLogApprox, e.dist_map]

theorem thermalNegativeLogKernel_isometry (e : ℂ ≃ₗᵢ[ℝ] ℂ) (x y : ℂ) :
    thermalNegativeLogKernel (e x, e y) = thermalNegativeLogKernel (x, y) := by
  simp only [thermalNegativeLogKernel, e.dist_map]

/-- Extended-potential symmetry of an actual invariant measure. This identity
retains potentially infinite positive potential, rather than assigning a
finite real value to a nonintegrable full logarithm. -/
theorem thermalExtendedLogPotential_isometry (μ : ProbabilityMeasure ℂ)
    (e : ℂ ≃ₗᵢ[ℝ] ℂ) (hinv : Measure.map e (μ : Measure ℂ) = μ) (x : ℂ) :
    thermalExtendedLogPotential μ (e x) = thermalExtendedLogPotential μ x := by
  have hp : Measurable (fun y => thermalExtendedPositiveLogKernel (e x, y)) :=
    thermalExtendedPositiveLogKernel_measurable.comp (measurable_const.prodMk measurable_id)
  have hn : Measurable (fun y => thermalNegativeLogKernel (e x, y)) :=
    (thermalNegativeLogKernel_continuous.comp (continuous_const.prodMk continuous_id)).measurable
  have hpos : (∫⁻ y, thermalExtendedPositiveLogKernel (e x, y) ∂μ) =
      ∫⁻ y, thermalExtendedPositiveLogKernel (x, y) ∂μ := by
    calc
      _ = ∫⁻ y, thermalExtendedPositiveLogKernel (e x, y) ∂Measure.map e (μ : Measure ℂ) := by rw [hinv]
      _ = ∫⁻ y, thermalExtendedPositiveLogKernel (e x, e y) ∂μ := lintegral_map hp e.continuous.measurable
      _ = _ := lintegral_congr fun y => thermalExtendedPositiveLogKernel_isometry e x y
  have hneg : (∫⁻ y, ENNReal.ofReal (thermalNegativeLogKernel (e x, y)) ∂μ) =
      ∫⁻ y, ENNReal.ofReal (thermalNegativeLogKernel (x, y)) ∂μ := by
    calc
      _ = ∫⁻ y, ENNReal.ofReal (thermalNegativeLogKernel (e x, y))
          ∂Measure.map e (μ : Measure ℂ) := by rw [hinv]
      _ = ∫⁻ y, ENNReal.ofReal (thermalNegativeLogKernel (e x, e y)) ∂μ :=
        lintegral_map hn.ennreal_ofReal e.continuous.measurable
      _ = _ := lintegral_congr fun y => congrArg ENNReal.ofReal (thermalNegativeLogKernel_isometry e x y)
  simp only [thermalExtendedLogPotential, hpos, hneg]

/-- Equal norms give equal genuine extended potentials of every original
canonical minimizer. Negative-part integrability at both points is derived. -/
theorem thermalCanonical_minimizer_extendedPotential_eq_of_norm_eq
    {β : ℝ} (hβ : 0 < β) (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν)
    {x y : ℂ} (hxy : ‖x‖ = ‖y‖) :
    Integrable (fun z => thermalNegativeLogKernel (x, z)) μ ∧
    Integrable (fun z => thermalNegativeLogKernel (y, z)) μ ∧
    thermalExtendedLogPotential μ x = thermalExtendedLogPotential μ y := by
  have hP2 := (thermalCanonical_global_minimizer_finite_domain hβ hmin).2.1
  refine ⟨thermalNegativeLogPotential_integrable μ hP2 x,
    thermalNegativeLogPotential_integrable μ hP2 y, ?_⟩
  let e : ℂ ≃ₗᵢ[ℝ] ℂ := Submodule.reflection (ℝ ∙ (x - y))ᗮ
  have he : e x = y := Submodule.reflection_sub hxy
  have hinv := thermalCanonical_minimizer_measure_map_isometry hβ μ hmin e
  have h := thermalExtendedLogPotential_isometry μ e hinv x
  rw [he] at h
  exact h.symm

/-- An explicit radial profile for the extended potential. This is not a
pointwise assertion about an arbitrary Radon–Nikodym density representative. -/
theorem thermalCanonical_minimizer_extendedPotential_radial
    {β : ℝ} (hβ : 0 < β) (μ : ProbabilityMeasure ℂ)
    (hmin : ∀ ν : ProbabilityMeasure ℂ,
      equilibriumCanonicalFreeEnergy β μ ≤ equilibriumCanonicalFreeEnergy β ν) :
    ∃ U : ℝ → EReal, ∀ x : ℂ, thermalExtendedLogPotential μ x = U ‖x‖ := by
  refine ⟨fun r => thermalExtendedLogPotential μ (r : ℂ), ?_⟩
  intro x
  exact (thermalCanonical_minimizer_extendedPotential_eq_of_norm_eq hβ μ hmin (x := x)
    (y := (‖x‖ : ℂ)) (by simp)).2.2

end RepulsiveCoulomb.PaperRoute
