import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoreClosure
import LeanResearch.RepulsiveCoulomb.CoulombFormCenter
import LeanResearch.RepulsiveCoulomb.RothausTightening

/-! Records-only uncompiled full-form centering and Rothaus tightening.
Public statements and proof bodies moved unchanged from the final assembly. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb

theorem coulombFormCenter_core_value (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) :
    coulombFormValueL (N + 2) hβ (coulombFormCenter N hβ (coulombFormCore hβ φ)) =ᵐ[coulombMeasure (N + 2) β]
      (fun z => φ z - ∫ w, φ w ∂coulombMeasure (N + 2) β) := by
  rw [coulombFormCenter_value]
  have hm : poleBranchRealMean (N + 2) hβ (coulombFormValueL (N + 2) hβ (coulombFormCore hβ φ)) =
      ∫ w, φ w ∂coulombMeasure (N + 2) β :=
    (poleBranchRealMean_eq_integral hβ _).trans (integral_congr_ae (coulombFormCore_value hβ φ))
  filter_upwards [poleBranchRealCenter_coe hβ (coulombFormValueL (N + 2) hβ (coulombFormCore hβ φ)),
    coulombFormCore_value hβ φ] with z hc hv
  simpa only [hm, hv] using hc

/-- Concrete Rothaus tightening: first on bounded genuine core functions,
then by actual original-form entropy closure. Centering is in the full form,
not asserted to remain compactly supported. -/
theorem coulomb_form_tightening {N : ℕ} {β A B P : ℝ} (hβ : 0 < β) (hB : 0 ≤ B + 2)
    (hPI : ∀ u : CoulombFormDomain (N + 2) hβ,
      variance (coulombFormValueL (N + 2) hβ u : CoulombConfig (N + 2) → ℝ)
        (coulombMeasure (N + 2) β) ≤ P * coulombFormEnergy (N + 2) hβ u)
    (hdef : ∀ u : CoulombFormDomain (N + 2) hβ,
      entropy (coulombMeasure (N + 2) β) (fun z => (coulombFormValueL (N + 2) hβ u z) ^ 2) ≤
        ((A * coulombFormEnergy (N + 2) hβ u +
          B * (∫ z, (coulombFormValueL (N + 2) hβ u z) ^ 2 ∂coulombMeasure (N + 2) β) : ℝ) : EReal))
    (u : CoulombFormDomain (N + 2) hβ) :
    entropy (coulombMeasure (N + 2) β) (fun z => (coulombFormValueL (N + 2) hβ u z) ^ 2) ≤
      (((A + (B + 2) * P) * coulombFormEnergy (N + 2) hβ u : ℝ) : EReal) := by
  letI := coulombMeasure_isProbability (N := N + 2) hβ
  have hcore (φ : TestFunction (coulombDomain (N + 2)) ℝ ⊤) :
      entropy (coulombMeasure (N + 2) β) (fun z => φ z ^ 2) ≤
        (((A + (B + 2) * P) *
          (∫ z, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 2) β) : ℝ) : EReal) := by
    have hval := (coulombFormCenter_core_value N hβ φ).mono
      (fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)
    have he : coulombFormEnergy (N + 2) hβ (coulombFormCenter N hβ (coulombFormCore hβ φ)) =
        ∫ z, ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 2) β := by
      rw [coulombFormEnergy, coulombFormCenter_gradient, ← coulombFormEnergy,
        coulombFormCore_energy_eq_integral]
    have hd := hdef (coulombFormCenter N hβ (coulombFormCore hβ φ))
    rw [entropy_congr_ae hval, integral_congr_ae hval, he] at hd
    have hp := hPI (coulombFormCore hβ φ)
    rw [variance_congr (coulombFormCore_value hβ φ), coulombFormCore_energy_eq_integral,
      variance_eq_integral φ.continuous.measurable.aemeasurable] at hp
    obtain ⟨M, hMpos, hM⟩ := coulomb_testFunction_c1_bound φ
    exact bounded_defective_lsi_tightening φ.continuous.measurable
      ⟨M, fun z => (hM z).1⟩ hB hp hd
  have h := conditionalEntropyBranch_form_of_core (C := A + (B + 2) * P) (D := 0) hβ
    (fun φ => by simpa only [zero_mul, add_zero] using hcore φ) u
  simpa only [zero_mul, add_zero] using h

end RepulsiveCoulomb
