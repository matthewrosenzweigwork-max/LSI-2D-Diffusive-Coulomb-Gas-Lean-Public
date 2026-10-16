module

public import LeanResearch.RepulsiveCoulomb.PointGroundStateEnergy

@[expose] public section

/-! The configuration-uniform weighted moment bound on the actual smooth core.
Extension to the full closed form is a separate remaining step. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointGroundState_weighted_value_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (b : ℂ → ℝ) (hb : Continuous b) :
    (∫ x : ℂ, b x * (pointGroundStateCore hγ ha y φ x) ^ 2) =
      ∫ x, b x * φ x ^ 2 ∂pointMeasure γ a y := by
  let _ := pointMeasure_isProbability hγ ha y
  have hs : HasCompactSupport (fun x : ℂ => φ x ^ 2) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  have hi : Integrable (fun x : ℂ => b x * φ x ^ 2) (pointMeasure γ a y) :=
    (hb.mul (φ.continuous.pow 2)).integrable_of_hasCompactSupport hs.mul_left
  rw [pointMeasure_integral_density_of_integrable hγ ha y _ hi]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [pointGroundStateCore_sq]
  ring

theorem pointGroundState_mass_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x : ℂ, (pointGroundStateCore hγ ha y φ x) ^ 2) = ∫ x, φ x ^ 2 ∂pointMeasure γ a y := by
  simpa using pointGroundState_weighted_value_integral hγ ha y φ (fun _ => 1) continuous_const

theorem pointGroundState_moment_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x : ℂ, ‖x‖ ^ 2 * (pointGroundStateCore hγ ha y φ x) ^ 2) =
      ∫ x, ‖x‖ ^ 2 * φ x ^ 2 ∂pointMeasure γ a y :=
  pointGroundState_weighted_value_integral hγ ha y φ (fun x => ‖x‖ ^ 2) (continuous_norm.pow 2)

theorem pointCore_weighted_moment_bound {γ Q : ℝ} (hγ : 0 < γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ) (a : Fin m → ℝ), (∀ j, 0 ≤ a j) →
    ∀ y : Fin m → ℂ, (∑ j, a j ≤ Q) →
    ∀ φ : TestFunction (pointDomain a y) ℝ ⊤,
    (∫ x, ‖x‖ ^ 2 * φ x ^ 2 ∂pointMeasure γ a y) ≤ C *
      ((∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        (∫ x, φ x ^ 2 ∂pointMeasure γ a y)) := by
  obtain ⟨U, hU, hu⟩ := pointScore_uncertainty (Q := Q) hγ
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

end RepulsiveCoulomb
