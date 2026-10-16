module

public import LeanResearch.RepulsiveCoulomb.PointFormMean

@[expose] public section

/-! Configuration-uniform global Poincare on the full physical closed form. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace ProbabilityTheory
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

theorem pointForm_poincare_of_core {m : ℕ} {γ P : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hcore : ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      variance (φ : ℂ → ℝ) (pointMeasure γ a y) ≤
        P * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y))
    (u : PointFormDomain hγ ha y) :
    variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤ P * pointFormEnergy hγ ha y u := by
  obtain ⟨φ, hφ⟩ := pointFormCore_approximation hγ ha y u
  have hv := ((pointForm_variance_continuous hγ ha y).tendsto u).comp hφ
  have he := ((pointFormEnergy_continuous hγ ha y).tendsto u).comp hφ
  apply le_of_tendsto_of_tendsto hv (tendsto_const_nhds.mul he)
  apply Eventually.of_forall
  intro n
  dsimp only [Function.comp_apply]
  rw [pointFormCore_variance, pointFormCore_energy_eq_integral]
  exact hcore (φ n)

theorem pointForm_uniform_poincare {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ P : ℝ, 0 < P ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
    variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤ P * pointFormEnergy hγ ha y u := by
  obtain ⟨P, hP, hp⟩ := pointCore_uniform_poincare (Q := Q) hγ
  refine ⟨P, hP, ?_⟩
  intro m a ha y hQ u
  exact pointForm_poincare_of_core hγ ha y (hp m a ha y hQ) u

theorem pointForm_uniform_poincare_integral {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ P : ℝ, 0 < P ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
    Integrable (fun x : ℂ => (pointFormValueL hγ ha y u x -
      (∫ z, pointFormValueL hγ ha y u z ∂pointMeasure γ a y)) ^ 2) (pointMeasure γ a y) ∧
    (∫ x, (pointFormValueL hγ ha y u x -
      (∫ z, pointFormValueL hγ ha y u z ∂pointMeasure γ a y)) ^ 2 ∂pointMeasure γ a y) ≤
      P * (∫ x, ‖pointFormGradientL hγ ha y u x‖ ^ 2 ∂pointMeasure γ a y) := by
  obtain ⟨P, hP, hp⟩ := pointForm_uniform_poincare (Q := Q) hγ
  refine ⟨P, hP, ?_⟩
  intro m a ha y hQ u
  let _ := pointMeasure_isProbability hγ ha y
  have hm : MemLp (fun x : ℂ => pointFormValueL hγ ha y u x -
      (∫ z, pointFormValueL hγ ha y u z ∂pointMeasure γ a y)) 2 (pointMeasure γ a y) := by
    convert! (Lp.memLp (pointFormValueL hγ ha y u)).sub
      (memLp_const (∫ z, pointFormValueL hγ ha y u z ∂pointMeasure γ a y)) using 1
  refine ⟨hm.integrable_sq, ?_⟩
  have h := hp m a ha y hQ u
  rw [variance_eq_integral (Lp.aestronglyMeasurable (pointFormValueL hγ ha y u)).aemeasurable,
    pointFormEnergy_eq_integral] at h
  exact h

end RepulsiveCoulomb
