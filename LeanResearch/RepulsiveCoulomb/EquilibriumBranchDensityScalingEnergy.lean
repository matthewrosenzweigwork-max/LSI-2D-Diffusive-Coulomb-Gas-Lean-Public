module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchDensityScalingBasics

@[expose] public section

/-! Exact scaling of the actual finite logarithmic interaction. The spatial
diagonal is explicitly excluded in the pointwise kernel identity and proved
null under the actual planar product reference before integration. The
manuscript coefficient is exactly minus log t in the pair energy. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

theorem equilibriumLogKernel_smul {t : ℝ} (ht : 0 < t) {z : ℂ} (hz : z ≠ 0) :
    equilibriumLogKernel (t • z) = equilibriumLogKernel z - Real.log t := by
  unfold equilibriumLogKernel
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht,
    Real.log_mul ht.ne' (norm_ne_zero_iff.mpr hz)]
  ring

/-- This identity is deliberately restricted to distinct spatial positions. -/
theorem equilibriumDensityScale_pair_integrand {t : ℝ} (ht : 0 < t)
    (ρ : ℂ → ℝ) (p : ℂ × ℂ) (hp : p.1 ≠ p.2) :
    equilibriumDensityScale t ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * equilibriumDensityScale t ρ p.2) =
      ((t ^ 2)⁻¹) ^ 2 *
        (((fun q : ℂ × ℂ => ρ q.1 * (equilibriumLogKernel (q.1 - q.2) * ρ q.2)) (t⁻¹ • p)) -
          Real.log t * ((fun q : ℂ × ℂ => ρ q.1 * ρ q.2) (t⁻¹ • p))) := by
  have hg := equilibriumLogKernel_smul (inv_pos.mpr ht) (sub_ne_zero.mpr hp)
  rw [smul_sub, Real.log_inv] at hg
  change equilibriumDensityScale t ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * equilibriumDensityScale t ρ p.2) =
    ((t ^ 2)⁻¹) ^ 2 *
      (ρ (t⁻¹ • p.1) * (equilibriumLogKernel (t⁻¹ • p.1 - t⁻¹ • p.2) * ρ (t⁻¹ • p.2)) -
        Real.log t * (ρ (t⁻¹ • p.1) * ρ (t⁻¹ • p.2)))
  rw [hg]
  unfold equilibriumDensityScale
  ring

theorem equilibriumDensityScaling_off_diagonal_ae :
    ∀ᵐ p : ℂ × ℂ ∂(volume : Measure ℂ).prod volume, p.1 ≠ p.2 := by
  apply (Measure.ae_prod_iff_ae_ae
    (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
  exact Eventually.of_forall (fun x => ((volume : Measure ℂ).ae_ne x).mono (fun _ h => h.symm))

/-- Absolute interaction integrability is preserved by every positive dilation. -/
theorem equilibriumDensityScale_logEnergy_integrable {t : ℝ} (ht : 0 < t) {ρ : ℂ → ℝ}
    (hρi : Integrable ρ)
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    Integrable (fun p : ℂ × ℂ => equilibriumDensityScale t ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * equilibriumDensityScale t ρ p.2)) (volume.prod volume) := by
  have hg := hG.comp_smul (inv_ne_zero ht.ne')
  have hp := (hρi.mul_prod hρi).comp_smul (inv_ne_zero ht.ne')
  apply ((hg.sub (hp.const_mul (Real.log t))).const_mul (((t ^ 2)⁻¹) ^ 2)).congr
  exact equilibriumDensityScaling_off_diagonal_ae.mono (fun p hp =>
    (equilibriumDensityScale_pair_integrand ht ρ p hp).symm)

/-- The actual pair-energy law with the exact dimension-two logarithmic shift. -/
theorem equilibriumDensityScale_interaction {t : ℝ} (ht : 0 < t) {ρ : ℂ → ℝ}
    (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    equilibriumDensityInteraction (equilibriumDensityScale t ρ) =
      equilibriumDensityInteraction ρ - Real.log t := by
  have hg := hG.comp_smul (inv_ne_zero ht.ne')
  have hp := (hρi.mul_prod hρi).comp_smul (inv_ne_zero ht.ne')
  have he : (fun p : ℂ × ℂ => equilibriumDensityScale t ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * equilibriumDensityScale t ρ p.2)) =ᵐ[volume.prod volume]
      (fun p : ℂ × ℂ => ((t ^ 2)⁻¹) ^ 2 *
        (((fun q : ℂ × ℂ => ρ q.1 * (equilibriumLogKernel (q.1 - q.2) * ρ q.2)) (t⁻¹ • p)) -
          Real.log t * ((fun q : ℂ × ℂ => ρ q.1 * ρ q.2) (t⁻¹ • p)))) :=
    equilibriumDensityScaling_off_diagonal_ae.mono (equilibriumDensityScale_pair_integrand ht ρ)
  rw [equilibriumDensityInteraction_eq_product (equilibriumDensityScale_logEnergy_integrable ht hρi hG),
    integral_congr_ae he, integral_const_mul, integral_sub hg (hp.const_mul _), integral_const_mul,
    Measure.integral_comp_inv_smul (volume.prod volume)
      (fun p : ℂ × ℂ => ρ p.1 * (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) t,
    Measure.integral_comp_inv_smul (volume.prod volume) (fun p : ℂ × ℂ => ρ p.1 * ρ p.2) t]
  have hmass : (∫ p : ℂ × ℂ, ρ p.1 * ρ p.2 ∂volume.prod volume) = 1 := by
    rw [integral_prod_mul ρ ρ, hρmass]
    norm_num
  rw [hmass, ← equilibriumDensityInteraction_eq_product hG]
  simp only [Module.finrank_prod, Complex.finrank_real_complex, smul_eq_mul]
  norm_num only [show 2 + 2 = 4 by norm_num]
  rw [abs_of_nonneg (pow_nonneg ht.le 4)]
  field_simp [ht.ne'] <;> ring

/-- The exact free-energy formula along the actual normalized dilation,
including the entropy coefficient two and the interaction coefficient one-half. -/
theorem equilibriumDensityScale_freeEnergy {β t : ℝ} (ht : 0 < t) {ρ : ℂ → ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρi : Integrable ρ) (hρmass : (∫ x : ℂ, ρ x) = 1)
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hG : Integrable (fun p : ℂ × ℂ => ρ p.1 *
      (equilibriumLogKernel (p.1 - p.2) * ρ p.2)) (volume.prod volume)) :
    equilibriumDensityFreeEnergy β (equilibriumDensityScale t ρ) - equilibriumDensityFreeEnergy β ρ =
      (t ^ 2 - 1) * (∫ x : ℂ, ‖x‖ ^ 2 * ρ x) / 2 - (1 / 2 + 2 / β) * Real.log t := by
  unfold equilibriumDensityFreeEnergy
  rw [integral_equilibriumDensityScale_secondMoment ht ρ,
    equilibriumDensityScale_interaction ht hρi hρmass hG,
    integral_equilibriumDensityScale_entropy ht hρ0 hρi hρmass hρH]
  ring

end RepulsiveCoulomb
