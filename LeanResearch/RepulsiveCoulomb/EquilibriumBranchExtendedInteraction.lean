import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExtendedConfinement
import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExtendedIntegral

/-! Exact shifted interaction correspondence on the full nonatomic P2 domain.
The positive interaction is permitted to be infinite. The extended kernel
retains +infinity on the diagonal even though this measure class gives it zero
product mass. Singular measures with atoms are handled separately by the
non-AC branch of the full free-energy correspondence. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibriumExtendedKernel_ae_eq {μ : Measure ℂ} [SFinite μ] [NullSingletonClass μ] :
    equilibriumExtendedShiftedKernel =ᵐ[μ.prod μ]
      (fun p : ℂ × ℂ => ENNReal.ofReal (equilibriumLogKernel (p.1 - p.2) +
        equilibriumLogMoment p.1 + equilibriumLogMoment p.2)) := by
  have hne : ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae
      (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Eventually.of_forall (fun x => (μ.ae_ne x).mono (fun _ h => h.symm))
  exact hne.mono (fun p hp => equilibriumExtendedShiftedKernel_off_diagonal hp)

/-- Exact interaction identity, including infinite positive energy. No
integrability of the full Coulomb kernel is assumed. -/
theorem equilibriumExtendedInteraction_shift_identity {μ : Measure ℂ}
    [IsProbabilityMeasure μ] [NullSingletonClass μ]
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    equilibriumExtendedIntegral (μ.prod μ)
      (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) =
      ((∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂μ.prod μ) : EReal) -
        (2 * (∫ x : ℂ, equilibriumLogMoment x ∂μ) : ℝ) := by
  have hL := equilibriumLogMoment_measure_integrable hμ2
  have hs : Integrable (fun p : ℂ × ℂ => equilibriumLogMoment p.1 + equilibriumLogMoment p.2)
      (μ.prod μ) := (hL.comp_fst μ).add (hL.comp_snd μ)
  have hsi : (∫ p : ℂ × ℂ, equilibriumLogMoment p.1 + equilibriumLogMoment p.2 ∂μ.prod μ) =
      2 * (∫ x : ℂ, equilibriumLogMoment x ∂μ) := by
    rw [integral_add (hL.comp_fst μ) (hL.comp_snd μ),
      integral_prod _ (hL.comp_fst μ), integral_prod _ (hL.comp_snd μ)]
    simp only [integral_const, probReal_univ, one_smul]
    ring
  have hshift (p : ℂ × ℂ) :
      0 ≤ equilibriumLogKernel (p.1 - p.2) + (equilibriumLogMoment p.1 + equilibriumLogMoment p.2) := by
    linarith [equilibriumLogKernel_sub_lower p.1 p.2]
  have he := equilibriumExtendedIntegral_eq_shifted
    (equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd))
    (equilibriumLogNegative_product_integrable hμ2) hs hshift
  have hk : (∫⁻ p : ℂ × ℂ, ENNReal.ofReal (equilibriumLogKernel (p.1 - p.2) +
      (equilibriumLogMoment p.1 + equilibriumLogMoment p.2)) ∂μ.prod μ) =
        ∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂μ.prod μ := by
    apply lintegral_congr_ae
    exact (equilibriumExtendedKernel_ae_eq (μ := μ)).mono (fun p hp => by
      simpa only [add_assoc] using hp.symm)
  dsimp only [Function.comp_apply, Pi.sub_apply] at he
  rw [hk, hsi] at he
  exact he

end RepulsiveCoulomb
