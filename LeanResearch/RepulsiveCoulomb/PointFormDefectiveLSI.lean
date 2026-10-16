module

public import LeanResearch.RepulsiveCoulomb.PointCoreDefectiveLSI

@[expose] public section

/-! Actual entropy lower semicontinuity extends the defective estimate to the
full closed form, without assuming entropy integrability of the limit. -/
noncomputable section
open Set MeasureTheory Filter
open PeriodicAttractiveLogGas
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointForm_defective_lsi_of_core {m : ℕ} {γ C D : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hcore : ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
      entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
        ((C * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
          D * (∫ x, φ x ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal))
    (u : PointFormDomain hγ ha y) :
    entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
      ((C * pointFormEnergy hγ ha y u + D * (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  obtain ⟨φ, hφ⟩ := pointFormCore_approximation hγ ha y u
  have hv := ((pointFormValueL hγ ha y).continuous.tendsto u).comp hφ
  have he := ((pointFormEnergy_continuous hγ ha y).tendsto u).comp hφ
  have hm := ((pointFormMass_continuous hγ ha y).tendsto u).comp hφ
  apply entropy_sq_le_of_tendsto hv ((tendsto_const_nhds.mul he).add (tendsto_const_nhds.mul hm))
  intro n
  dsimp only [Function.comp_apply]
  have hval : (fun x => (pointFormValueL hγ ha y (pointFormCore hγ ha y (φ n)) x) ^ 2) =ᵐ[pointMeasure γ a y]
      fun x => φ n x ^ 2 := (pointFormCore_value hγ ha y (φ n)).mono (fun _ hx => congrArg (fun t : ℝ => t ^ 2) hx)
  rw [entropy_congr_ae hval, pointFormCore_energy_eq_integral, pointFormCore_mass_eq_integral]
  exact hcore (φ n)

theorem pointForm_uniform_defective_lsi {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C D : ℝ, 0 < C ∧ 0 < D ∧
      ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ),
      (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
      entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
        ((C * pointFormEnergy hγ ha y u + D * (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  by_cases hQ : 0 ≤ Q
  · obtain ⟨C, D, hC, hD, hb⟩ := pointCore_uniform_defective_lsi hγ hQ
    refine ⟨C, D, hC, hD, ?_⟩
    intro m a ha y hsum u
    exact pointForm_defective_lsi_of_core hγ ha y (hb m a ha y hsum) u
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro m a ha y hsum u
    exact (hQ ((Finset.sum_nonneg (fun j _ => ha j)).trans hsum)).elim

end RepulsiveCoulomb
