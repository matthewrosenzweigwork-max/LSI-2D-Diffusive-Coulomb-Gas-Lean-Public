import LeanResearch.RepulsiveCoulomb.PointFormMomentClosure

/-! Manuscript cor:U-bound on the full actual closed physical form domain.
The constant is independent of point number, exponents and locations. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

theorem pointForm_weighted_moment_bound {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2) (pointMeasure γ a y) ∧
      (∫ x, ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := pointCore_weighted_moment_bound (Q := Q) hγ
  refine ⟨C, hC, ?_⟩
  intro m a ha y hQ u
  exact pointForm_moment_bound_of_core hγ ha y hC.le (hc m a ha y hQ) u

theorem pointForm_uniform_quadratic_moment {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2) (pointMeasure γ a y) ∧
      (∫ x, ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤ C *
        ((∫ x, ‖pointFormGradientL hγ ha y u x‖ ^ 2 ∂pointMeasure γ a y) +
          (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y)) := by
  obtain ⟨C, hC, hc⟩ := pointForm_weighted_moment_bound (Q := Q) hγ
  refine ⟨C, hC, ?_⟩
  intro m a ha y hQ u
  obtain ⟨hi, hu⟩ := hc m a ha y hQ u
  refine ⟨hi, ?_⟩
  calc
    _ ≤ C * ‖u‖ ^ 2 := hu
    _ = _ := by
      rw [pointForm_norm_sq, pointFormValue_norm_sq_eq_integral, pointFormEnergy_eq_integral]
      ring

end RepulsiveCoulomb
