module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFreeEnergyCorrespondence

@[expose] public section

/-! The nonnegative extended objective on all probability measures. Finite
objective implies absolute continuity and the actual P2 condition; neither is
assumed for a prospective minimizing family. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumNonnegativeObjective (β : ℝ) (μ : Measure ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal β⁻¹ * InformationTheory.klDiv μ (equilibriumGaussianMeasure (β / 4)) +
    ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂μ.prod μ) +
    (∫⁻ x : ℂ, ENNReal.ofReal (equilibriumShiftedConfinement x) ∂μ)

theorem equilibriumNonnegativeFreeEnergy_eq_objective (β : ℝ) (μ : Measure ℂ) :
    equilibriumNonnegativeFreeEnergy β μ = (equilibriumNonnegativeObjective β μ : EReal) -
      ((1 : ℝ) : EReal) + ((Real.log ((β / 4) / Real.pi) / β : ℝ) : EReal) := rfl

theorem equilibriumObjective_entropy_term_le (β : ℝ) (μ : Measure ℂ) :
    ENNReal.ofReal β⁻¹ * InformationTheory.klDiv μ (equilibriumGaussianMeasure (β / 4)) ≤
      equilibriumNonnegativeObjective β μ := by
  exact (le_add_of_nonneg_right bot_le).trans (le_add_of_nonneg_right bot_le)

theorem equilibriumObjective_confinement_le (β : ℝ) (μ : Measure ℂ) :
    (∫⁻ x : ℂ, ENNReal.ofReal (equilibriumShiftedConfinement x) ∂μ) ≤
      equilibriumNonnegativeObjective β μ := le_add_of_nonneg_left bot_le

/-- Finiteness of the objective yields finite KL, rather than using finite
entropy as an admissibility hypothesis for a minimizing sequence. -/
theorem equilibriumObjective_finite_klDiv {β : ℝ} (hβ : 0 < β) {μ : Measure ℂ}
    (hG : equilibriumNonnegativeObjective β μ ≠ ∞) :
    InformationTheory.klDiv μ (equilibriumGaussianMeasure (β / 4)) ≠ ∞ := by
  intro h
  have hc : ENNReal.ofReal β⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hβ)).ne'
  have ht := equilibriumObjective_entropy_term_le β μ
  rw [h, ENNReal.mul_top hc] at ht
  exact hG (top_le_iff.mp ht)

theorem equilibriumObjective_finite_absolutelyContinuous {β : ℝ} (hβ : 0 < β)
    {μ : Measure ℂ} (hG : equilibriumNonnegativeObjective β μ ≠ ∞) : μ ≪ volume :=
  (equilibriumGaussian_absolutelyContinuous_iff (by positivity : 0 < β / 4) μ).mp
    ((InformationTheory.klDiv_ne_top_iff.mp (equilibriumObjective_finite_klDiv hβ hG)).1)

/-- Quantitative P2 coercivity is an extended integral inequality on every
probability measure, including those with infinite second moment. -/
theorem equilibriumObjective_secondMoment_bound (β : ℝ) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] :
    (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) ≤
      8 * (equilibriumNonnegativeObjective β μ + 1) := by
  have hm : Measurable (fun x : ℂ => ENNReal.ofReal (equilibriumShiftedConfinement x)) :=
    equilibriumShiftedConfinement_continuous.measurable.ennreal_ofReal
  have hp (x : ℂ) : ENNReal.ofReal (‖x‖ ^ 2) ≤
      8 * (ENNReal.ofReal (equilibriumShiftedConfinement x) + 1) := by
    have hc := equilibriumShiftedConfinement_coercive x
    have hreal : ‖x‖ ^ 2 ≤ 8 * (equilibriumShiftedConfinement x + 1) := by linarith
    have h := ENNReal.ofReal_le_ofReal hreal
    norm_num only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 8),
      ENNReal.ofReal_add (equilibriumShiftedConfinement_nonneg x) zero_le_one] at h
    simpa only [ENNReal.ofReal_ofNat, ENNReal.ofReal_one] using h
  calc
    _ ≤ ∫⁻ x : ℂ, 8 * (ENNReal.ofReal (equilibriumShiftedConfinement x) + 1) ∂μ :=
      lintegral_mono hp
    _ = 8 * ((∫⁻ x : ℂ, ENNReal.ofReal (equilibriumShiftedConfinement x) ∂μ) + 1) := by
      rw [lintegral_const_mul (8 : ℝ≥0∞)
        (f := fun x : ℂ => ENNReal.ofReal (equilibriumShiftedConfinement x) + 1)
        (hm.add measurable_const), lintegral_add_left hm]
      simp
    _ ≤ _ := mul_le_mul_right (add_le_add (equilibriumObjective_confinement_le β μ) le_rfl) 8

/-- Actual integrability of the second moment follows from finite objective. -/
theorem equilibriumObjective_finite_secondMoment {β : ℝ} {μ : Measure ℂ}
    [IsProbabilityMeasure μ] (hG : equilibriumNonnegativeObjective β μ ≠ ∞) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2) μ := by
  have hfin : 8 * (equilibriumNonnegativeObjective β μ + 1) < (∞ : ℝ≥0∞) := by finiteness
  have hmoment := (equilibriumObjective_secondMoment_bound β μ).trans_lt hfin
  exact (lintegral_ofReal_ne_top_iff_integrable (by fun_prop)
    (Eventually.of_forall (fun x : ℂ => sq_nonneg ‖x‖))).mp hmoment.ne

/-- Hence the exact canonical free energy applies to every finite-objective
probability measure; admissibility is a conclusion. -/
theorem equilibriumObjective_finite_canonical_correspondence {β : ℝ} (hβ : 0 < β)
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hG : equilibriumNonnegativeObjective β μ ≠ ∞) :
    μ ≪ volume ∧ Integrable (fun x : ℂ => ‖x‖ ^ 2) μ ∧
      equilibriumCanonicalFreeEnergy β μ = (equilibriumNonnegativeObjective β μ : EReal) -
        ((1 : ℝ) : EReal) + ((Real.log ((β / 4) / Real.pi) / β : ℝ) : EReal) := by
  have hP2 := equilibriumObjective_finite_secondMoment hG
  exact ⟨equilibriumObjective_finite_absolutelyContinuous hβ hG, hP2,
    (equilibriumFreeEnergy_correspondence hβ hP2).trans
      (equilibriumNonnegativeFreeEnergy_eq_objective β μ)⟩

end RepulsiveCoulomb
