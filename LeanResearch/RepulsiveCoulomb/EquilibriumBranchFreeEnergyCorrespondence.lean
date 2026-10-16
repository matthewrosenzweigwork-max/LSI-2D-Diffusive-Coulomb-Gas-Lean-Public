module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceEntropy
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExtendedInteraction
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchFreeEnergyAlgebra

@[expose] public section

/-! Exact canonical/shifted free-energy correspondence on the whole P2
probability domain. The canonical entropy and interaction are genuine signed
extended integrals with integrable negative parts; either positive part may
be infinite. Non-AC measures have canonical value infinity. The nonnegative
objective uses the actual +infinity diagonal kernel on every measure. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Classical
namespace RepulsiveCoulomb

/-- Canonical manuscript free energy, with the usual infinite extension
outside the absolutely continuous P2 domain. On the AC branch the spatial
diagonal is product-null, so the real representative of g is legitimate. -/
def equilibriumCanonicalFreeEnergy (β : ℝ) (μ : Measure ℂ) : EReal :=
  if μ ≪ volume ∧ Integrable (fun x : ℂ => ‖x‖ ^ 2) μ then
    (((∫ x : ℂ, ‖x‖ ^ 2 ∂μ) / 2 : ℝ) : EReal) +
      ((1 / 2 : ℝ) : EReal) * equilibriumExtendedIntegral (μ.prod μ)
        (fun p : ℂ × ℂ => equilibriumLogKernel (p.1 - p.2)) +
      ((β⁻¹ : ℝ) : EReal) * equilibriumExtendedIntegral volume
        (fun x : ℂ => equilibriumReferenceDensity μ x * Real.log (equilibriumReferenceDensity μ x))
  else ⊤

/-- The direct-method objective has only nonnegative extended summands before
its finite normalization shift. It is meaningful for every probability measure,
not only measures for which ordinary real energy integrals happen to exist. -/
def equilibriumNonnegativeFreeEnergy (β : ℝ) (μ : Measure ℂ) : EReal :=
  ((ENNReal.ofReal β⁻¹ * InformationTheory.klDiv μ (equilibriumGaussianMeasure (β / 4)) +
      ENNReal.ofReal (1 / 2 : ℝ) * (∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂μ.prod μ) +
      (∫⁻ x : ℂ, ENNReal.ofReal (equilibriumShiftedConfinement x) ∂μ) : ℝ≥0∞) : EReal) -
    ((1 : ℝ) : EReal) + ((Real.log ((β / 4) / Real.pi) / β : ℝ) : EReal)

theorem integral_equilibriumShiftedConfinement {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    (∫ x : ℂ, equilibriumShiftedConfinement x ∂μ) =
      (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) / 4 - (∫ x : ℂ, equilibriumLogMoment x ∂μ) + 1 := by
  unfold equilibriumShiftedConfinement
  rw [integral_add (f := fun x : ℂ => ‖x‖ ^ 2 / 4 - equilibriumLogMoment x)
      (g := fun _ : ℂ => (1 : ℝ))
      ((hμ2.div_const 4).sub (equilibriumLogMoment_measure_integrable hμ2))
      (integrable_const 1),
    integral_sub (hμ2.div_const 4) (equilibriumLogMoment_measure_integrable hμ2), integral_div]
  simp only [integral_const, probReal_univ, one_smul]

/-- Singular measures really have infinite shifted energy because the Gaussian
reference is equivalent to planar volume. No finite-density proxy is inserted. -/
theorem equilibriumNonnegativeFreeEnergy_eq_top_of_not_ac {β : ℝ} (hβ : 0 < β)
    {μ : Measure ℂ} (hμ : ¬ μ ≪ volume) : equilibriumNonnegativeFreeEnergy β μ = ⊤ := by
  have ha : 0 < β / 4 := by positivity
  have hi : ENNReal.ofReal β⁻¹ ≠ 0 := (ENNReal.ofReal_pos.mpr (inv_pos.mpr hβ)).ne'
  unfold equilibriumNonnegativeFreeEnergy
  rw [equilibriumGaussian_klDiv_eq_top_of_not_ac ha hμ, ENNReal.mul_top hi,
    top_add, top_add, EReal.coe_ennreal_top, EReal.top_sub_coe, EReal.top_add_coe]

/-- Full P2 correspondence, including singular measures and independently
infinite entropy or positive interaction. No analytic existence property or
finite full-energy assumption is an input. -/
theorem equilibriumFreeEnergy_correspondence {β : ℝ} (hβ : 0 < β)
    {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hμ2 : Integrable (fun x : ℂ => ‖x‖ ^ 2) μ) :
    equilibriumCanonicalFreeEnergy β μ = equilibriumNonnegativeFreeEnergy β μ := by
  by_cases hμ : μ ≪ volume
  · letI : NullSingletonClass μ := ⟨fun x => hμ (measure_singleton x)⟩
    have ha : 0 < β / 4 := by positivity
    have hW : ((∫⁻ x : ℂ, ENNReal.ofReal (equilibriumShiftedConfinement x) ∂μ) : EReal) =
        ((∫ x : ℂ, ‖x‖ ^ 2 ∂μ) / 4 - (∫ x : ℂ, equilibriumLogMoment x ∂μ) + 1 : ℝ) := by
      have hn : (0 : ℝ) ≤ ∫ x : ℂ, equilibriumShiftedConfinement x ∂μ :=
        integral_nonneg equilibriumShiftedConfinement_nonneg
      rw [← ofReal_integral_eq_lintegral_ofReal (equilibriumShiftedConfinement_integrable hμ2)
        (Eventually.of_forall equilibriumShiftedConfinement_nonneg), EReal.coe_ennreal_ofReal,
        max_eq_left hn, integral_equilibriumShiftedConfinement hμ2]
    have hcβ : (ENNReal.ofReal β⁻¹ : EReal) = ((β⁻¹ : ℝ) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (inv_pos.mpr hβ).le]
    have hc2 : (ENNReal.ofReal (1 / 2 : ℝ) : EReal) = ((1 / 2 : ℝ) : EReal) := by
      rw [EReal.coe_ennreal_ofReal, max_eq_left (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    rw [equilibriumCanonicalFreeEnergy, if_pos ⟨hμ, hμ2⟩,
      equilibriumReferenceEntropy_eq_gaussian_klDiv ha hμ hμ2,
      equilibriumExtendedInteraction_shift_identity hμ2]
    unfold equilibriumNonnegativeFreeEnergy
    rw [EReal.coe_ennreal_add, EReal.coe_ennreal_add, EReal.coe_ennreal_mul,
      EReal.coe_ennreal_mul, hcβ, hc2, hW]
    exact equilibriumFreeEnergy_extended_algebra hβ
      (InformationTheory.klDiv μ (equilibriumGaussianMeasure (β / 4)))
      (∫⁻ p : ℂ × ℂ, equilibriumExtendedShiftedKernel p ∂μ.prod μ)
      (∫ x : ℂ, ‖x‖ ^ 2 ∂μ) (∫ x : ℂ, equilibriumLogMoment x ∂μ)
      (Real.log ((β / 4) / Real.pi))
  · rw [equilibriumCanonicalFreeEnergy, if_neg (fun h => hμ h.1),
      equilibriumNonnegativeFreeEnergy_eq_top_of_not_ac hβ hμ]

end RepulsiveCoulomb
