import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalPositiveLogPortmanteau
import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalLogUniformIntegrability
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFreeEnergyCorrespondence

/-! Exact splitting of the unchanged canonical energy. The positive singular
kernel has genuine infinity on the diagonal; absolute continuity is used only
in the algebraic branch where the diagonal is null. Singular measures are
handled independently through infinite Gaussian KL. -/
noncomputable section
open MeasureTheory Real Filter
open scoped ENNReal Topology Classical
namespace RepulsiveCoulomb.PaperRoute

theorem thermalNegativeLogKernel_eq_negativePart (p : ℂ × ℂ) :
    thermalNegativeLogKernel p = max (-equilibriumLogKernel (p.1 - p.2)) 0 := by
  unfold thermalNegativeLogKernel equilibriumLogKernel
  rw [dist_eq_norm, neg_neg]
  by_cases h : ‖p.1 - p.2‖ ≤ 1
  · rw [max_eq_left h, Real.log_one,
      max_eq_right (Real.log_nonpos (norm_nonneg _) h)]
  · rw [max_eq_right (le_of_not_ge h),
      max_eq_left (Real.log_nonneg (le_of_not_ge h))]

theorem thermalExtendedInteraction_eq_positive_sub_negative (μ : ProbabilityMeasure ℂ)
    (hAC : (μ : Measure ℂ) ≪ volume)
    (hP2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    equilibriumExtendedIntegral ((μ : Measure ℂ).prod μ)
      (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) =
      (thermalPositiveLogInteraction μ : EReal) -
        ((∫ p, thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ) : ℝ) : EReal) := by
  let : NullSingletonClass (μ : Measure ℂ) := ⟨fun x => hAC (measure_singleton x)⟩
  have hne : ∀ᵐ p : ℂ × ℂ ∂((μ : Measure ℂ).prod μ), p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Eventually.of_forall (fun x => ((μ : Measure ℂ).ae_ne x).mono (fun _ h => h.symm))
  have hp : (∫⁻ p : ℂ × ℂ, ENNReal.ofReal (equilibriumLogKernel (p.1 - p.2))
      ∂((μ : Measure ℂ).prod μ)) = thermalPositiveLogInteraction μ := by
    apply lintegral_congr_ae
    exact hne.mono (fun p hp => by
      rw [thermalExtendedPositiveLogKernel_off_diagonal hp,
        ENNReal.ofReal_max, ENNReal.ofReal_zero, max_eq_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (-Real.log ‖p.1 - p.2‖) from bot_le)]
      rfl)
  have hn : (∫⁻ p : ℂ × ℂ, ENNReal.ofReal (-equilibriumLogKernel (p.1 - p.2))
      ∂((μ : Measure ℂ).prod μ)) =
      ENNReal.ofReal (∫ p, thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ)) := by
    rw [ofReal_integral_eq_lintegral_ofReal (thermalNegativeLogKernel_integrable μ hP2)
      (Eventually.of_forall thermalNegativeLogKernel_nonneg)]
    apply lintegral_congr
    intro p
    rw [thermalNegativeLogKernel_eq_negativePart, ENNReal.ofReal_max,
      ENNReal.ofReal_zero, max_eq_left (show (0 : ℝ≥0∞) ≤ ENNReal.ofReal (-equilibriumLogKernel (p.1 - p.2)) from bot_le)]
  rw [equilibriumExtendedIntegral, hp, hn, EReal.coe_ennreal_ofReal,
    max_eq_left (integral_nonneg thermalNegativeLogKernel_nonneg)]

/-- Nonnegative proof components of the literal energy, before subtracting the
finite negative logarithmic interaction. This is not a replacement objective. -/
def thermalGaussianPositiveBlock (β : ℝ) (μ : ProbabilityMeasure ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal β⁻¹ *
      InformationTheory.klDiv (μ : Measure ℂ) (equilibriumGaussianMeasure (β / 4)) +
    ENNReal.ofReal (1 / 4 : ℝ) * (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) +
    ENNReal.ofReal (1 / 2 : ℝ) * thermalPositiveLogInteraction μ

private theorem thermal_positive_block_algebra {β : ℝ} (hβ : 0 < β)
    (A B : ℝ≥0∞) (r N c : ℝ) :
    ((r / 2 : ℝ) : EReal) + ((1 / 2 : ℝ) : EReal) * ((B : EReal) - (N : EReal)) +
      ((β⁻¹ : ℝ) : EReal) * ((A : EReal) - ((β / 4 * r - c : ℝ) : EReal)) =
    (((β⁻¹ : ℝ) : EReal) * (A : EReal) + ((r / 4 : ℝ) : EReal) +
      ((1 / 2 : ℝ) : EReal) * (B : EReal)) + ((c / β - N / 2 : ℝ) : EReal) := by
  have hi : 0 < β⁻¹ := inv_pos.mpr hβ
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  by_cases hA : A = ∞
  · by_cases hB : B = ∞
    · subst A
      subst B
      simp only [EReal.coe_ennreal_top, EReal.top_sub_coe,
        EReal.coe_mul_top_of_pos hi, EReal.coe_mul_top_of_pos hh,
        EReal.coe_add_top, EReal.top_add_top, EReal.top_add_coe]
    · rw [hA, ← EReal.coe_ennreal_toReal hB]
      simp only [EReal.coe_ennreal_top, EReal.top_sub_coe,
        EReal.coe_mul_top_of_pos hi, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_add_top, EReal.top_add_coe]
  · by_cases hB : B = ∞
    · rw [hB, ← EReal.coe_ennreal_toReal hA]
      simp only [EReal.coe_ennreal_top, EReal.top_sub_coe,
        EReal.coe_mul_top_of_pos hh, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_add_top, EReal.top_add_coe]
    · rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB]
      simp only [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      field_simp [hβ.ne']; ring

/-- The exact canonical split on every P2 probability, including non-AC measures
and independently infinite entropy or positive interaction. -/
theorem thermalCanonicalFreeEnergy_eq_positiveBlock_sub_negative {β : ℝ} (hβ : 0 < β)
    (μ : ProbabilityMeasure ℂ) (hP2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    equilibriumCanonicalFreeEnergy β μ =
      (thermalGaussianPositiveBlock β μ : EReal) +
        ((Real.log ((β / 4) / Real.pi) / β -
          (∫ p, thermalNegativeLogKernel p ∂((μ : Measure ℂ).prod μ)) / 2 : ℝ) : EReal) := by
  have ha : 0 < β / 4 := by positivity
  by_cases hAC : (μ : Measure ℂ) ≪ volume
  · have hcβ : (ENNReal.ofReal β⁻¹ : EReal) = ((β⁻¹ : ℝ) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (inv_pos.mpr hβ).le]
    have hc2 : (ENNReal.ofReal (1 / 2 : ℝ) : EReal) = ((1 / 2 : ℝ) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hmoment : ((ENNReal.ofReal (1 / 4 : ℝ) *
        (∫⁻ x : ℂ, ENNReal.ofReal (‖x‖ ^ 2) ∂μ) : ℝ≥0∞) : EReal) =
        (((∫ x : ℂ, ‖x‖ ^ 2 ∂μ) / 4 : ℝ) : EReal) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hP2
        (Eventually.of_forall fun x : ℂ => sq_nonneg ‖x‖),
        ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
        EReal.coe_ennreal_ofReal,
        max_eq_left (mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg ‖x‖))]
      congr 1
      ring
    rw [equilibriumCanonicalFreeEnergy, ite_eq_left ⟨hAC, hP2⟩,
      equilibriumReferenceEntropy_eq_gaussian_klDiv ha hAC hP2,
      thermalExtendedInteraction_eq_positive_sub_negative μ hAC hP2]
    unfold thermalGaussianPositiveBlock
    rw [EReal.coe_ennreal_add, EReal.coe_ennreal_add, hmoment,
      EReal.coe_ennreal_mul, EReal.coe_ennreal_mul, hcβ, hc2]
    exact thermal_positive_block_algebra hβ _ _ _ _ _
  · have hi : ENNReal.ofReal β⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hβ)).ne'
    rw [equilibriumCanonicalFreeEnergy, ite_eq_right (fun h => hAC h.1)]
    unfold thermalGaussianPositiveBlock
    rw [equilibriumGaussian_klDiv_eq_top_of_not_ac ha hAC, ENNReal.mul_top hi,
      top_add, top_add, EReal.coe_ennreal_top, EReal.top_add_coe]

end RepulsiveCoulomb.PaperRoute
