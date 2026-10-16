module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCanonicalSplitting
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPartitionBasic
public import Mathlib.Probability.Moments.IntegrableExpMul

@[expose] public section

/-! Actual integrability of the modulated energy under the canonical Gibbs
law, derived from two genuine exponential moments and the exact tilted-law
identity. No singular-log integrability premise is added. Records-only draft. -/
noncomputable section
open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibriumReference_gibbs_energy_exp_integrable {β s : ℝ} (hβ : 0 < β)
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
  have hi := equilibriumReference_modulated_exp_integrable hβ R hN (sub_nonneg.mpr hs)
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
theorem equilibriumReference_gibbs_energy_integrable {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    Integrable (equilibriumModulatedEnergy R.density : (Fin N → ℂ) → ℝ)
      (Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) := by
  have hp := equilibriumReference_gibbs_energy_exp_integrable hβ
    (by linarith : β / 2 ≤ β) R hN
  have hn := equilibriumReference_gibbs_energy_exp_integrable hβ
    (by linarith : -(β / 2) ≤ β) R hN
  have h := ProbabilityTheory.integrable_pow_of_integrable_exp_mul
    (show β / 2 ≠ 0 by positivity) hp hn 1
  simpa only [pow_one] using h

/-- The physical configuration formulation has the same canonical energy. -/
theorem equilibriumReference_physical_gibbs_energy_integrable {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    Integrable (fun z : CoulombConfig N => equilibriumModulatedEnergy R.density (WithLp.ofLp z))
      (coulombMeasure N β) := by
  have hp : MeasurePreserving (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)
      (Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β)) :=
    ⟨WithLp.measurable_ofLp 2 _, rfl⟩
  have hi := equilibriumReference_gibbs_energy_integrable (N := N) hβ R hN
  have ht := hp.integrable_comp_of_integrable hi
  simpa only [Function.comp_def] using ht

end RepulsiveCoulomb
