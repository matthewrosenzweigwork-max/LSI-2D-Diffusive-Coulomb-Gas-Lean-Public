module

public import LeanResearch.RepulsiveCoulomb.CoulombFormApproximation

@[expose] public section

/-! Actual mass and physical energy integrals for the full particle form. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombFormValue_norm_sq_eq_integral (N : ℕ) {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    ‖coulombFormValueL N hβ u‖ ^ 2 = ∫ x, (coulombFormValueL N hβ u x) ^ 2 ∂coulombMeasure N β := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simp [real_inner_self_eq_norm_sq]

theorem coulombFormValue_square_integrable (N : ℕ) {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    Integrable (fun x => (coulombFormValueL N hβ u x) ^ 2) (coulombMeasure N β) :=
  (Lp.memLp (coulombFormValueL N hβ u)).integrable_sq

theorem coulombFormGradient_square_integrable (N : ℕ) {β : ℝ} (hβ : 0 < β) (u : CoulombFormDomain N hβ) :
    Integrable (fun x => ‖coulombFormGradientL N hβ u x‖ ^ 2) (coulombMeasure N β) :=
  (Lp.memLp (coulombFormGradientL N hβ u)).norm.integrable_sq

theorem coulombFormCore_mass_eq_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ x, (coulombFormValueL N hβ (coulombFormCore hβ φ) x) ^ 2 ∂coulombMeasure N β) =
      ∫ x, φ x ^ 2 ∂coulombMeasure N β := by
  apply integral_congr_ae
  filter_upwards [coulombFormCore_value hβ φ] with x hx
  rw [hx]

theorem coulombFormCore_energy_eq_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombFormEnergy N hβ (coulombFormCore hβ φ) =
      ∫ x, ‖gradient (φ : CoulombConfig N → ℝ) x‖ ^ 2 ∂coulombMeasure N β := by
  rw [coulombFormEnergy_eq_integral]
  apply integral_congr_ae
  filter_upwards [coulombFormCore_gradient hβ φ] with x hx
  rw [hx]

theorem coulombFormCore_norm_sq_eq_integrals {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    ‖coulombFormCore hβ φ‖ ^ 2 = (∫ x, φ x ^ 2 ∂coulombMeasure N β) +
      (∫ x, ‖gradient (φ : CoulombConfig N → ℝ) x‖ ^ 2 ∂coulombMeasure N β) := by
  rw [coulombForm_norm_sq, coulombFormValue_norm_sq_eq_integral,
    coulombFormCore_mass_eq_integral, coulombFormCore_energy_eq_integral]

end RepulsiveCoulomb
