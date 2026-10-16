module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicScoreUncertainty
public import LeanResearch.RepulsiveCoulomb.PointFormMomentClosure

@[expose] public section

/-! Canonical atomic-maximal confinement on the actual full physical form domain.
Ground-state identities convert the new uncertainty bound to U*(5+4*gamma);
Fatou closure proves moment integrability before the real moment estimate.

Proof bodies are adapted from the corresponding frozen score/annular/moment
modules. This new application replaces every hardwired old weak-force, bad-area,
uncertainty and moment producer with the new finite-atomic maximal route.
Generic cutoff, overlap, integrability, ground-state and Fatou identities are
reused unchanged; actual proof-body dependencies are audited separately. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem atomic_pointCore_weighted_moment_bound {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ), (∀ j, 0 ≤ a j) →
    ∀ y : Fin m → ℂ, (∑ j, a j ≤ Q) →
    ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
    (∫ x, ‖x‖ ^ 2 * φ x ^ 2 ∂pointMeasure γ a y) ≤ C *
      ((∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        (∫ x, φ x ^ 2 ∂pointMeasure γ a y)) := by
  obtain ⟨U, hU, hu⟩ := atomic_pointScore_uncertainty (Q := Q) hγ
  let C := U * (5 + 4 * γ)
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro m a ha y hQ φ
  let ψ := pointGroundStateCore hγ ha y φ
  have hu' := hu m a ha y hQ ψ
  have hg := pointGroundState_energy_identity hγ ha y φ
  have hm := pointGroundState_mass_integral hγ ha y φ
  have hx := pointGroundState_moment_integral hγ ha y φ
  change (∫ x : ℂ, ψ x ^ 2) = _ at hm
  change (∫ x : ℂ, ‖x‖ ^ 2 * ψ x ^ 2) = _ at hx
  rw [hm, hx] at hu'
  rw [pointGroundState_mass_integral] at hg
  have he : 0 ≤ ∫ x : ℂ, ‖gradient (ψ : ℂ → ℝ) x‖ ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hE : 0 ≤ ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y := integral_nonneg (fun _ => sq_nonneg _)
  have hM : 0 ≤ ∫ x, φ x ^ 2 ∂pointMeasure γ a y := integral_nonneg (fun _ => sq_nonneg _)
  have hb : (∫ x : ℂ, ‖gradient (ψ : ℂ → ℝ) x‖ ^ 2) +
      (∫ x : ℂ, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2) + (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
      4 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
      (4 * γ + 1) * (∫ x, φ x ^ 2 ∂pointMeasure γ a y) := by
    change (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) =
      (∫ x : ℂ, ‖gradient (ψ : ℂ → ℝ) x‖ ^ 2) +
        (1 / 4 : ℝ) * (∫ x : ℂ, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2) -
        γ * (∫ x, φ x ^ 2 ∂pointMeasure γ a y) at hg
    nlinarith only [hg, he]
  have hc : 4 * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
      (4 * γ + 1) * (∫ x, φ x ^ 2 ∂pointMeasure γ a y) ≤
      (5 + 4 * γ) * ((∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        (∫ x, φ x ^ 2 ∂pointMeasure γ a y)) := by
    nlinarith [mul_nonneg hγ.le hE]
  have h := hu'.trans ((mul_le_mul_of_nonneg_left hb hU.le).trans
    (mul_le_mul_of_nonneg_left hc hU.le))
  simpa only [C, mul_assoc] using h

theorem atomic_pointForm_weighted_moment_bound {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2) (pointMeasure γ a y) ∧
      (∫ x, ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤ C * ‖u‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := atomic_pointCore_weighted_moment_bound (Q := Q) hγ
  refine ⟨C, hC, ?_⟩
  intro m a ha y hQ u
  exact pointForm_moment_bound_of_core hγ ha y hC.le (hc m a ha y hQ) u

theorem atomic_pointForm_uniform_quadratic_moment {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
      (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2) (pointMeasure γ a y) ∧
      (∫ x, ‖x‖ ^ 2 * (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) ≤ C *
        ((∫ x, ‖pointFormGradientL hγ ha y u x‖ ^ 2 ∂pointMeasure γ a y) +
          (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y)) := by
  obtain ⟨C, hC, hc⟩ := atomic_pointForm_weighted_moment_bound (Q := Q) hγ
  refine ⟨C, hC, ?_⟩
  intro m a ha y hQ u
  obtain ⟨hi, hu⟩ := hc m a ha y hQ u
  refine ⟨hi, ?_⟩
  calc
    _ ≤ C * ‖u‖ ^ 2 := hu
    _ = _ := by
      rw [pointForm_norm_sq, pointFormValue_norm_sq_eq_integral, pointFormEnergy_eq_integral]
      ring

end RepulsiveCoulomb.PaperRoute
