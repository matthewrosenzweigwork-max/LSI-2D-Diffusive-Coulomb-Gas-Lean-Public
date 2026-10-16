module

public import LeanResearch.RepulsiveCoulomb.PointCoreGlobalSPI
public import LeanResearch.RepulsiveCoulomb.PointFormL1Mass

@[expose] public section

/-! Gaussian-rate super-Poincare on the actual full closed physical form. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointForm_spi_of_core {m : ℕ} {γ s β : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hcore : ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        β * (∫ x, |φ x| ∂pointMeasure γ a y) ^ 2)
    (u : PointFormDomain hγ ha y) :
    (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤
      s * pointFormEnergy hγ ha y u + β * (pointFormL1Mass hγ ha y u) ^ 2 := by
  obtain ⟨φ, hφ⟩ := pointFormCore_approximation hγ ha y u
  have hm := ((pointFormMass_continuous hγ ha y).tendsto u).comp hφ
  have he := ((pointFormEnergy_continuous hγ ha y).tendsto u).comp hφ
  have hl := ((pointFormL1Mass_continuous hγ ha y).tendsto u).comp hφ
  apply le_of_tendsto_of_tendsto hm ((tendsto_const_nhds.mul he).add (tendsto_const_nhds.mul (hl.pow 2)))
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_apply]
  rw [pointFormCore_mass_eq_integral, pointFormCore_energy_eq_integral, pointFormCore_l1_eq_integral]
  exact hcore (φ n)

theorem pointForm_uniform_superPoincare {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ s : ℝ, 0 < s → ∀ u : PointFormDomain hγ ha y,
      (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤
        s * pointFormEnergy hγ ha y u + A * Real.exp (B / s) * (pointFormL1Mass hγ ha y u) ^ 2 := by
  by_cases hQ : 0 ≤ Q
  · obtain ⟨A, B, hA, hB, hb⟩ := pointCore_global_superPoincare hγ hQ
    refine ⟨A, B, hA, hB, ?_⟩
    intro m a ha y hsum s hs u
    exact pointForm_spi_of_core hγ ha y (hb m a ha y hsum s hs) u
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro m a ha y hsum s hs u
    have hsum0 : 0 ≤ ∑ j, a j := Finset.sum_nonneg (fun j _ => ha j)
    exact (hQ (hsum0.trans hsum)).elim

theorem pointForm_uniform_superPoincare_integral {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ s : ℝ, 0 < s → ∀ u : PointFormDomain hγ ha y,
      Integrable (fun x => (pointFormValueL hγ ha y u x) ^ 2) (pointMeasure γ a y) ∧
      Integrable (fun x => |pointFormValueL hγ ha y u x|) (pointMeasure γ a y) ∧
      (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖pointFormGradientL hγ ha y u x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B / s) * (∫ x, |pointFormValueL hγ ha y u x| ∂pointMeasure γ a y) ^ 2 := by
  obtain ⟨A, B, hA, hB, hb⟩ := pointForm_uniform_superPoincare (Q := Q) hγ
  refine ⟨A, B, hA, hB, ?_⟩
  intro m a ha y hsum s hs u
  refine ⟨(Lp.memLp (pointFormValueL hγ ha y u)).integrable_sq,
    (pointFormValue_integrable hγ ha y u).abs, ?_⟩
  have h := hb m a ha y hsum s hs u
  rwa [pointFormEnergy_eq_integral] at h

end RepulsiveCoulomb
