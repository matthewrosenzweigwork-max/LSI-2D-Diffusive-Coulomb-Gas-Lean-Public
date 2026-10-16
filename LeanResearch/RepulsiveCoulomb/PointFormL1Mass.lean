module

public import LeanResearch.RepulsiveCoulomb.PointFormMean

@[expose] public section

/-! Continuity of the actual L1 mass on the full physical form domain. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def pointFormL1Mass {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) : ℝ :=
  ∫ x, |pointFormValueL hγ ha y u x| ∂pointMeasure γ a y

theorem pointFormL1Mass_eq_inner {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) :
    pointFormL1Mass hγ ha y u =
      inner ℝ (pointFormValueL hγ ha y (pointConstantForm hγ ha y))
        (lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : ℝ)‖ = 0) (pointFormValueL hγ ha y u)) := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pointConstantForm_value hγ ha y,
    lipschitzWith_one_norm.coeFn_compLp (norm_zero : ‖(0 : ℝ)‖ = 0) (pointFormValueL hγ ha y u)] with x hx hn
  rw [hx, hn]
  simp [Real.norm_eq_abs]

theorem pointFormL1Mass_continuous {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    Continuous (pointFormL1Mass hγ ha y) := by
  simp_rw [funext (pointFormL1Mass_eq_inner hγ ha y)]
  exact ((innerSL ℝ (pointFormValueL hγ ha y (pointConstantForm hγ ha y))).continuous.comp
    (lipschitzWith_one_norm.continuous_compLp (norm_zero : ‖(0 : ℝ)‖ = 0))).comp
    (pointFormValueL hγ ha y).continuous

theorem pointFormCore_l1_eq_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    pointFormL1Mass hγ ha y (pointFormCore hγ ha y φ) = ∫ x, |φ x| ∂pointMeasure γ a y := by
  apply integral_congr_ae
  filter_upwards [pointFormCore_value hγ ha y φ] with x hx
  rw [hx]

theorem pointFormMass_continuous {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    Continuous (fun u : PointFormDomain hγ ha y => ∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) := by
  simp_rw [← pointFormValue_norm_sq_eq_integral]
  exact (pointFormValueL hγ ha y).continuous.norm.pow 2

theorem pointFormCore_mass_eq_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    (∫ x, (pointFormValueL hγ ha y (pointFormCore hγ ha y φ) x) ^ 2 ∂pointMeasure γ a y) =
      ∫ x, φ x ^ 2 ∂pointMeasure γ a y := by
  apply integral_congr_ae
  filter_upwards [pointFormCore_value hγ ha y φ] with x hx
  rw [hx]

end RepulsiveCoulomb
