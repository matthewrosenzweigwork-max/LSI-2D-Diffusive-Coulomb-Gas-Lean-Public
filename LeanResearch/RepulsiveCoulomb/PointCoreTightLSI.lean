module

public import LeanResearch.RepulsiveCoulomb.PointFormDefectiveLSI

@[expose] public section

/-! Rothaus tightening using the actual constant form and the proved global PI. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open PeriodicAttractiveLogGas
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointCore_uniform_tight_lsi {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
        ((K * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  obtain ⟨C, D, hC, hD, hdef⟩ := pointForm_uniform_defective_lsi (Q := Q) hγ
  obtain ⟨P, hP, hpi⟩ := pointCore_uniform_poincare (Q := Q) hγ
  refine ⟨C + (D + 2) * P, by positivity, ?_⟩
  intro m a ha y hQ φ
  let _ := pointMeasure_isProbability hγ ha y
  let μ := pointMeasure γ a y
  let c := ∫ x, φ x ∂μ
  let v := pointFormSubtractConstant hγ ha y (pointFormCore hγ ha y φ) c
  have hval : (fun x => (pointFormValueL hγ ha y v x) ^ 2) =ᵐ[μ] fun x => (φ x - c) ^ 2 :=
    (pointCore_subtractConstant_value hγ ha y φ c).mono (fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)
  have he : pointFormEnergy hγ ha y v = ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂μ := by
    rw [pointFormSubtractConstant_energy, pointFormCore_energy_eq_integral]
  have hd := hdef m a ha y hQ v
  rw [entropy_congr_ae hval, integral_congr_ae hval, he] at hd
  have hp := hpi m a ha y hQ φ
  rw [variance_eq_integral φ.continuous.measurable.aemeasurable] at hp
  obtain ⟨M, hM⟩ := testFunction_bounded (pointDomain a y) φ
  exact bounded_defective_lsi_tightening φ.continuous.measurable ⟨M, hM⟩
    (by linarith) hp hd

end RepulsiveCoulomb
