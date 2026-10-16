import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianCoreGlobalSPI
import LeanResearch.RepulsiveCoulomb.PointUniformSuperPoincare

/-! Additive experimental source. The actual new Gaussian core SPI passes to
the full physical form domain through the conditional approximation theorem.
All upstream local and moment/half-mass witnesses remain explicit. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem form_global_superPoincare {γ Q κ S U Rbase : ℝ} (hγ : 0 < γ)
    (hκ : 1 < κ) (hS : 0 < S) (hraw : UniformRawStrongSobolev Q κ S)
    (hU : 0 < U) (hMoment : UniformFormMomentBound hγ Q U)
    (hRbase : 1 ≤ Rbase) (hHalf : UniformHalfMassBall γ Q Rbase) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ s : ℝ, 0 < s → ∀ u : PointFormDomain hγ ha y,
      (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤
        s * pointFormEnergy hγ ha y u + A * Real.exp (B / s) * (pointFormL1Mass hγ ha y u) ^ 2 := by
  obtain ⟨A, B, hA, hB, hcore⟩ :=
    core_global_superPoincare hγ hκ hS hraw hU hMoment hRbase hHalf
  refine ⟨A, B, hA, hB, ?_⟩
  intro m a ha y hQ s hs u
  exact pointForm_spi_of_core hγ ha y (hcore m a ha y hQ s hs) u

end RepulsiveCoulomb.PaperRoute
