module

public import LeanResearch.RepulsiveCoulomb.CoulombPhaseIntegrability

@[expose] public section

/-! The manuscript's common-phase identity under its exact integrability hypothesis. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RepulsiveCoulomb

theorem coulomb_entire_phase_set_average {N : ℕ} {F : CoulombConfig N → ℂ}
    (hF : Differentiable ℂ F) (z : CoulombConfig N) :
    (2 * Real.pi)⁻¹ • (∫ θ in Ioc 0 (2 * Real.pi), F (coulombPhaseAction N θ z)) = F 0 := by
  have h := coulomb_entire_phase_average hF z
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity)] at h
  simpa only [circleMap, Complex.ofReal_one, one_mul, zero_add,
    coulombPhaseAction, Circle.coe_exp] using h

theorem coulomb_entire_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F : CoulombConfig N → ℂ} (hF : Differentiable ℂ F)
    (hi : Integrable F (coulombMeasure N β)) :
    (∫ z, F z ∂coulombMeasure N β) = F 0 := by
  letI := coulombMeasure_isProbability (N := N) hβ
  have hj := coulomb_phase_product_integrable hβ hF.continuous hi
  have hs := integral_integral_swap (f := fun θ z => F (coulombPhaseAction N θ z)) hj
  have ha : (2 * Real.pi)⁻¹ •
      (∫ θ in Ioc 0 (2 * Real.pi), ∫ z, F (coulombPhaseAction N θ z) ∂coulombMeasure N β) =
      ∫ _z : CoulombConfig N, F 0 ∂coulombMeasure N β := by
    rw [hs, ← integral_smul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun z => coulomb_entire_phase_set_average hF z)
  simp_rw [coulombPhaseAction_integral hβ.le] at ha
  rw [← intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_const,
    sub_zero, smul_smul, inv_mul_cancel₀ (by positivity : 2 * Real.pi ≠ 0), one_smul] at ha
  simpa using ha

theorem coulomb_common_phase_bilinear {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {F G : CoulombConfig N → ℂ} (hF : Differentiable ℂ F) (hG : Differentiable ℂ G)
    (hFG : Integrable (fun z => F z * G z) (coulombMeasure N β)) :
    (∫ z, F z * G z ∂coulombMeasure N β) = F 0 * G 0 :=
  coulomb_entire_integral hβ (hF.mul hG) hFG

end RepulsiveCoulomb
