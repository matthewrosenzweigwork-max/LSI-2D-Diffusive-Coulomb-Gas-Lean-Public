module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFreeEnergyCorrespondence
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

@[expose] public section

/-! The manuscript's exact quarter-moment coercivity, separately from the
weaker eighth-moment estimate used internally for compactness. The Gaussian
parameter here is beta/8. Entropy and positive Coulomb energy may be infinite;
the final statement uses a genuine extended second moment on every probability. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

private theorem equilibrium_quarter_coercivity_algebra {β : ℝ} (hβ : 0 < β)
    (A B : ℝ≥0∞) (r l c : ℝ) (hL : l ≤ r / 8 + 2) :
    ((r / 4 - 2 + c / β : ℝ) : EReal) ≤
      ((r / 2 : ℝ) : EReal) + ((1 / 2 : ℝ) : EReal) * ((B : EReal) - ((2 * l : ℝ) : EReal)) +
        ((β⁻¹ : ℝ) : EReal) * ((A : EReal) - ((β / 8 * r - c : ℝ) : EReal)) := by
  have hi : 0 < β⁻¹ := inv_pos.mpr hβ
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  by_cases hA : A = ∞
  · by_cases hB : B = ∞
    · subst A
      subst B
      simp only [EReal.coe_ennreal_top, EReal.top_sub_coe,
        EReal.coe_mul_top_of_pos hi, EReal.coe_mul_top_of_pos hh,
        EReal.coe_add_top, EReal.top_add_top, le_top]
    · rw [hA, ← EReal.coe_ennreal_toReal hB]
      simp only [EReal.coe_ennreal_top, EReal.top_sub_coe,
        EReal.coe_mul_top_of_pos hi, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_add_top, le_top]
  · by_cases hB : B = ∞
    · rw [hB, ← EReal.coe_ennreal_toReal hA]
      simp only [EReal.coe_ennreal_top, EReal.top_sub_coe,
        EReal.coe_mul_top_of_pos hh, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_add_top, EReal.top_add_coe, le_top]
    · rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB]
      simp only [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have he : β⁻¹ * (A.toReal - (β / 8 * r - c)) =
          β⁻¹ * A.toReal - r / 8 + c / β := by
        field_simp [hβ.ne']
        ring
      rw [he]
      have hA0 : 0 ≤ β⁻¹ * A.toReal := mul_nonneg hi.le ENNReal.toReal_nonneg
      have hB0 : 0 ≤ B.toReal := ENNReal.toReal_nonneg
      linarith

/-- Actual logarithmic absorption with coefficient exactly one eighth on
arbitrary P2 probability measures. -/
theorem equilibriumLogMoment_measure_eighth_bound {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    (∫ x : ℂ, equilibriumLogMoment x ∂μ) ≤ (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) / 8 + 2 := by
  have hi : Integrable (fun x : ℂ => (1 / 8 : ℝ) * ‖x‖ ^ 2 + 2) μ :=
    (hμ2.const_mul (1 / 8 : ℝ)).add (integrable_const 2)
  have hp (x : ℂ) : equilibriumLogMoment x ≤ (1 / 8 : ℝ) * ‖x‖ ^ 2 + 2 := by
    simpa only [show (4 * (1 / 8 : ℝ))⁻¹ = 2 by norm_num] using
      equilibriumLogMoment_le_quadratic (by norm_num : (0 : ℝ) < 1 / 8) x
  have h := integral_mono (equilibriumLogMoment_measure_integrable hμ2) hi hp
  rw [integral_add (hμ2.const_mul _) (integrable_const 2), integral_const_mul] at h
  simp only [integral_const, probReal_univ, one_smul] at h
  linarith

/-- Exact manuscript quarter-moment lower bound over the full P2 domain,
including singular measures and infinite positive entropy/interaction. -/
theorem equilibriumCanonicalFreeEnergy_quarter_coercive {β : ℝ} (hβ : 0 < β)
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    (((∫ x : ℂ, ‖x‖ ^ 2 ∂μ) / 4 - 2 + Real.log (β / (8 * Real.pi)) / β : ℝ) : EReal) ≤
      equilibriumCanonicalFreeEnergy β μ := by
  by_cases hμ : μ ≪ volume
  · letI : NullSingletonClass μ := ⟨fun x => hμ (measure_singleton x)⟩
    rw [equilibriumCanonicalFreeEnergy, if_pos ⟨hμ, hμ2⟩,
      equilibriumReferenceEntropy_eq_gaussian_klDiv (by positivity : 0 < β / 8) hμ hμ2,
      equilibriumExtendedInteraction_shift_identity hμ2]
    have he : (β / 8) / Real.pi = β / (8 * Real.pi) := by
      field_simp
    rw [he]
    exact equilibrium_quarter_coercivity_algebra hβ _ _ _ _ _
      (equilibriumLogMoment_measure_eighth_bound hμ2)
  · rw [equilibriumCanonicalFreeEnergy, if_neg (fun h => hμ h.1)]
    exact le_top

/-- The same exact quarter-moment bound on every probability measure, with the
second moment interpreted as a nonnegative extended integral. No P2, density,
or finite-positive-energy condition is a hypothesis. -/
theorem equilibriumCanonicalFreeEnergy_quarter_coercive_extended {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) :
    ((ENNReal.ofReal (1 / 4 : ℝ) * (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) : ℝ≥0∞) : EReal) -
      ((2 - Real.log (β / (8 * Real.pi)) / β : ℝ) : EReal) ≤ equilibriumCanonicalFreeEnergy β μ := by
  by_cases hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ
  · have hM : (0 : ℝ) ≤ ∫ x : ℂ, ‖x‖ ^ 2 ∂μ := integral_nonneg (fun x => sq_nonneg ‖x‖)
    have hm : (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) =
        ENNReal.ofReal (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) :=
      (ofReal_integral_eq_lintegral_ofReal hμ2 (Eventually.of_forall (fun x => sq_nonneg ‖x‖))).symm
    rw [hm, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
      EReal.coe_ennreal_ofReal, max_eq_left (mul_nonneg (by norm_num) hM), ← EReal.coe_sub]
    have he : (1 / 4 : ℝ) * (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) -
        (2 - Real.log (β / (8 * Real.pi)) / β) =
        (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) / 4 - 2 + Real.log (β / (8 * Real.pi)) / β := by ring
    rw [he]
    exact equilibriumCanonicalFreeEnergy_quarter_coercive hβ hμ2
  · rw [equilibriumCanonicalFreeEnergy, if_neg (fun h => hμ2 h.2)]
    exact le_top

end RepulsiveCoulomb
