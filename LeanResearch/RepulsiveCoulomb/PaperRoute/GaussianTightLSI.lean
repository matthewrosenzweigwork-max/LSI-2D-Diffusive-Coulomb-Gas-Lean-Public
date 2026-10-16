module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianCoreGlobalSPI
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianSPIWang
public import LeanResearch.RepulsiveCoulomb.PointFormDefectiveLSI

@[expose] public section

/-! Additive experimental source. Verification status is recorded separately in evidence. New SPI, the actual Wang specialization, full-form entropy closure, and Rothaus tightening from the new PI. -/
noncomputable section
open Set MeasureTheory Filter ProbabilityTheory
open PeriodicAttractiveLogGas
open scoped Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem core_defective_lsi_of_raw_sobolev {γ Q κ S U Rbase : ℝ} (hγ : 0 < γ)
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hU : 0 < U) (hMoment : UniformFormMomentBound hγ Q U)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall γ Q Rbase) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (_ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
        ((C * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
          D * (∫ x, φ x ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  obtain ⟨A, B, hA, hB, hSPI⟩ := core_global_superPoincare hγ hκ hS hraw hU hMoment hRbase hHalf
  obtain ⟨K, hK, hKb⟩ := exists_smoothTransition_deriv_bound
  refine ⟨192 * B * K ^ 2, (4 + 384 * A) * Real.log 2, by positivity,
    mul_pos (by linarith) (Real.log_pos (by norm_num)), ?_⟩
  intro m a ha y hQ φ
  exact core_defective_lsi_of_gaussian_spi hγ ha y hA hB hK hKb (hSPI m a ha y hQ) φ

theorem form_defective_lsi_of_raw_sobolev {γ Q κ S U Rbase : ℝ} (hγ : 0 < γ)
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hU : 0 < U) (hMoment : UniformFormMomentBound hγ Q U)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall γ Q Rbase) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
      entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
        ((C * pointFormEnergy hγ ha y u + D * (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  by_cases hQ : 0 ≤ Q
  · obtain ⟨C, D, hC, hD, hb⟩ := core_defective_lsi_of_raw_sobolev hγ hκ hS hraw hU hMoment hRbase hHalf
    refine ⟨C, D, hC, hD, ?_⟩
    intro m a ha y hsum u
    exact pointForm_defective_lsi_of_core hγ ha y (hb m a ha y hsum) u
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro m a ha y hsum u
    exact (hQ ((Finset.sum_nonneg (fun j _ => ha j)).trans hsum)).elim

theorem core_tight_lsi_of_raw_sobolev {γ Q κ S U Rbase : ℝ} (hγ : 0 < γ)
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hU : 0 < U) (hMoment : UniformFormMomentBound hγ Q U)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall γ Q Rbase) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (_ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
        ((K * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  obtain ⟨C, D, hC, hD, hdef⟩ := form_defective_lsi_of_raw_sobolev hγ hκ hS hraw hU hMoment hRbase hHalf
  obtain ⟨P, hP, hpi⟩ := core_poincare_of_raw_sobolev hγ hκ hS hraw hU hMoment
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

theorem form_tight_lsi_of_raw_sobolev {γ Q κ S U Rbase : ℝ} (hγ : 0 < γ)
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hU : 0 < U) (hMoment : UniformFormMomentBound hγ Q U)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall γ Q Rbase) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
      entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
        ((K * pointFormEnergy hγ ha y u : ℝ) : EReal) := by
  obtain ⟨K, hK, hcore⟩ := core_tight_lsi_of_raw_sobolev hγ hκ hS hraw hU hMoment hRbase hHalf
  refine ⟨K, hK, ?_⟩
  intro m a ha y hQ u
  have H := pointForm_defective_lsi_of_core (C := K) (D := 0) hγ ha y
    (fun φ => by simpa only [zero_mul, add_zero] using hcore m a ha y hQ φ) u
  simpa only [zero_mul, add_zero] using H

end RepulsiveCoulomb.PaperRoute
