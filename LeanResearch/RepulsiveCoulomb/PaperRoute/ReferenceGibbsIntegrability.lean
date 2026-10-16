import LeanResearch.RepulsiveCoulomb.PaperRoute.ReferencePolynomialIntegrability
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchDefectiveLSI
import LeanResearch.RepulsiveCoulomb.PaperRoute.PositiveLogGibbsIntegrability

/-! Genuine canonical A and B integrability through elementary finite-N
polynomial moments. The B/core consumer selects the authored retained-collision-power
positive-log argument, without an Onsager or zero-mass positivity selection. -/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Set Filter
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem paper_reference_gibbs_energy_exp_integrable_polynomial {β s : ℝ} (hβ : 0 < β)
    (hs : s ≤ β) (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    Integrable (fun z : Fin N → ℂ => Real.exp (s * equilibriumModulatedEnergy R.density z))
      (Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) := by
  let P := Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))
  let A : (Fin N → ℂ) → ℝ := equilibriumModulatedEnergy R.density
  let K := equilibriumReferencePartition N β R
  have hK : 0 < K := equilibriumReferencePartition_canonical_pos hβ R N
  have hAm : Measurable A := equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable
  have hwm : Measurable (fun z : Fin N → ℂ => ENNReal.ofReal (Real.exp (-β * A z) / K)) :=
    ((measurable_const.mul hAm).exp.div_const K).ennreal_ofReal
  have hi := paper_reference_modulated_exp_integrable_polynomial hβ R hN (sub_nonneg.mpr hs)
  rw [equilibriumReference_coulombMeasure_eq_tilted hβ R N]
  change Integrable (fun z => Real.exp (s * A z))
    (P.withDensity (fun z => ENNReal.ofReal (Real.exp (-β * A z) / K)))
  apply (integrable_withDensity_iff hwm (Eventually.of_forall
    (fun _ => ENNReal.ofReal_lt_top))).mpr
  simp only [ENNReal.toReal_ofReal (div_nonneg (Real.exp_pos _).le hK.le)]
  apply (hi.div_const K).congr
  exact Eventually.of_forall (fun z => by
    dsimp only [A]
    rw [← mul_div_assoc, ← Real.exp_add]
    congr 2
    ring)

/-- The actual canonical modulated energy is integrable under the pushed-forward
Gibbs probability measure. Both signs are controlled before invoking L1. -/
theorem paper_reference_gibbs_energy_integrable_polynomial {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    Integrable (equilibriumModulatedEnergy R.density : (Fin N → ℂ) → ℝ)
      (Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) := by
  have hp := paper_reference_gibbs_energy_exp_integrable_polynomial hβ
    (by linarith : β / 2 ≤ β) R hN
  have hn := paper_reference_gibbs_energy_exp_integrable_polynomial hβ
    (by linarith : -(β / 2) ≤ β) R hN
  have h := ProbabilityTheory.integrable_pow_of_integrable_exp_mul
    (show β / 2 ≠ 0 by positivity) hp hn 1
  simpa only [pow_one] using h

/-- The physical configuration formulation has the same canonical energy. -/
theorem paper_reference_physical_gibbs_energy_integrable_polynomial {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    Integrable (fun z : CoulombConfig N => equilibriumModulatedEnergy R.density (WithLp.ofLp z))
      (coulombMeasure N β) := by
  have hp : MeasurePreserving (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)
      (Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) :=
    ⟨WithLp.measurable_ofLp 2 _, rfl⟩
  have hi := paper_reference_gibbs_energy_integrable_polynomial (N := N) hβ R hN
  have ht := hp.integrable_comp_of_integrable hi
  simpa only [Function.comp_def] using ht

theorem paper_thermal_B_gibbs_integrable_polynomial {N : ℕ} {β : ℝ}
    (_hN : 0 < N) (hβ : 0 < β) (R : EquilibriumConstructedReference β) :
    Integrable (conditionalEntropyBranchThermalB R) (coulombMeasure N β) :=
  paper_thermal_B_gibbs_integrable_positive_log hβ R

theorem paper_thermal_B_core_integrable_polynomial {N : ℕ} {β : ℝ}
    (hN : 0 < N) (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Integrable (conditionalEntropyBranchThermalB R) (conditionalEntropyBranchCoulombCoreLaw β φ) := by
  let := coulombMeasure_isProbability (N := N) hβ
  have hB := paper_thermal_B_gibbs_integrable_polynomial hN hβ R
  obtain ⟨M, hMpos, hM⟩ := coulomb_testFunction_c1_bound φ
  have hsq : ∀ z, ‖φ z ^ 2‖ ≤ M ^ 2 := fun z => by
    simpa only [Real.norm_eq_abs, abs_sq, sq_abs] using
      pow_le_pow_left₀ (abs_nonneg (φ z)) (hM z).1 2
  unfold conditionalEntropyBranchCoulombCoreLaw conditionalEntropyBranchDensityLaw
  apply (integrable_withDensity_iff (φ.continuous.measurable.pow_const 2).ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))).mpr
  simpa only [ENNReal.toReal_ofReal (sq_nonneg _)] using
    hB.mul_bdd (φ.continuous.measurable.pow_const 2).aestronglyMeasurable (Eventually.of_forall hsq)

end RepulsiveCoulomb.PaperRoute
