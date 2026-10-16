import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianTightLSI
import LeanResearch.RepulsiveCoulomb.PointDilationBranchTransport

/-! Additive experimental source. Verification status is recorded separately in evidence. Gaussian dilation using newly selected unit-Gaussian PI/LSI constants and actual physical core transport. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open PeriodicAttractiveLogGas
open scoped Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem dilation_uniform_core_of_raw_sobolev {Q κ S U Rbase : ℝ}
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hU : 0 < U) (hMoment : UniformFormMomentBound (by norm_num : (0 : ℝ) < 1) Q U)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall 1 Q Rbase) :
    ∃ P K : ℝ, 0 < P ∧ 0 < K ∧
      ∀ (γ : ℝ) (hγ : 0 < γ) (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
        (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      variance (φ : ℂ → ℝ) (pointMeasure γ a y) ≤
        (P / γ) * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) ∧
      entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
        (((K / γ) * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  obtain ⟨P, hP, hpi⟩ := core_poincare_of_raw_sobolev (γ := 1) (by norm_num) hκ hS hraw hU hMoment
  obtain ⟨K, hK, hlsi⟩ := core_tight_lsi_of_raw_sobolev (γ := 1) (by norm_num) hκ hS hraw hU hMoment hRbase hHalf
  refine ⟨P, K, hP, hK, ?_⟩
  intro γ hγ m a ha y hQ φ
  let ψ := pointDilationBranchCore a y (Real.sqrt γ) (Real.sqrt_pos.mpr hγ) φ
  have hp := hpi m a ha (fun j => Real.sqrt γ • y j) hQ ψ
  have hk := hlsi m a ha (fun j => Real.sqrt γ • y j) hQ ψ
  dsimp only [ψ] at hp hk
  rw [pointDilationBranch_core_variance hγ ha y φ, pointDilationBranch_core_energy hγ ha y φ] at hp
  rw [pointDilationBranch_core_entropy hγ ha y φ, pointDilationBranch_core_energy hγ ha y φ] at hk
  exact ⟨by simpa only [div_eq_mul_inv, mul_assoc] using hp,
    by simpa only [div_eq_mul_inv, mul_assoc] using hk⟩

theorem dilation_uniform_full_domain_of_raw_sobolev {Q κ S U Rbase : ℝ}
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hU : 0 < U) (hMoment : UniformFormMomentBound (by norm_num : (0 : ℝ) < 1) Q U)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall 1 Q Rbase) :
    ∃ P K : ℝ, 0 < P ∧ 0 < K ∧
      ∀ (γ : ℝ) (hγ : 0 < γ) (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
        (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
      variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
        (P / γ) * pointFormEnergy hγ ha y u ∧
      entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
        (((K / γ) * pointFormEnergy hγ ha y u : ℝ) : EReal) := by
  obtain ⟨P, K, hP, hK, hcore⟩ := dilation_uniform_core_of_raw_sobolev hκ hS hraw hU hMoment hRbase hHalf
  refine ⟨P, K, hP, hK, ?_⟩
  intro γ hγ m a ha y hQ u
  constructor
  · exact pointForm_poincare_of_core hγ ha y (fun φ => (hcore γ hγ m a ha y hQ φ).1) u
  · have H := pointForm_defective_lsi_of_core (C := K / γ) (D := 0) hγ ha y
      (fun φ => by simpa only [zero_mul, add_zero] using (hcore γ hγ m a ha y hQ φ).2) u
    simpa only [zero_mul, add_zero] using H

end RepulsiveCoulomb.PaperRoute
