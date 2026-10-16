module

public import LeanResearch.RepulsiveCoulomb.PointCorePoincare

@[expose] public section

/-! Actual mean and variance continuity on the full physical form domain. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace ProbabilityTheory
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

def pointFormMeanL {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    PointFormDomain hγ ha y →L[ℝ] ℝ :=
  (innerSL ℝ (pointFormValueL hγ ha y (pointConstantForm hγ ha y))).comp (pointFormValueL hγ ha y)

theorem pointFormMeanL_eq_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) :
    pointFormMeanL hγ ha y u = ∫ x, pointFormValueL hγ ha y u x ∂pointMeasure γ a y := by
  change inner ℝ (pointFormValueL hγ ha y (pointConstantForm hγ ha y)) (pointFormValueL hγ ha y u) = _
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [pointConstantForm_value hγ ha y] with x hx
  rw [hx]
  simp

theorem pointFormValue_integrable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) :
    Integrable (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) := by
  let _ := pointMeasure_isProbability hγ ha y
  exact MemLp.integrable (by norm_num) (Lp.memLp (pointFormValueL hγ ha y u))

theorem pointForm_variance_eq_norm_mean {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) :
    variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) =
      ‖pointFormValueL hγ ha y u‖ ^ 2 - (pointFormMeanL hγ ha y u) ^ 2 := by
  let _ := pointMeasure_isProbability hγ ha y
  rw [variance_eq_sub (Lp.memLp (pointFormValueL hγ ha y u))]
  change (∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y) -
    (∫ x, pointFormValueL hγ ha y u x ∂pointMeasure γ a y) ^ 2 = _
  rw [← pointFormValue_norm_sq_eq_integral, ← pointFormMeanL_eq_integral]

theorem pointForm_variance_continuous {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    Continuous (fun u : PointFormDomain hγ ha y =>
      variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y)) := by
  simp_rw [pointForm_variance_eq_norm_mean]
  exact ((pointFormValueL hγ ha y).continuous.norm.pow 2).sub ((pointFormMeanL hγ ha y).continuous.pow 2)

theorem pointFormEnergy_continuous {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    Continuous (pointFormEnergy hγ ha y) := by
  exact (pointFormGradientL hγ ha y).continuous.norm.pow 2

theorem pointFormCore_variance {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    variance (pointFormValueL hγ ha y (pointFormCore hγ ha y φ) : ℂ → ℝ) (pointMeasure γ a y) =
      variance (φ : ℂ → ℝ) (pointMeasure γ a y) :=
  variance_congr (pointFormCore_value hγ ha y φ)

theorem pointFormCore_energy_eq_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    pointFormEnergy hγ ha y (pointFormCore hγ ha y φ) =
      ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y := by
  rw [pointFormEnergy_eq_integral]
  apply integral_congr_ae
  filter_upwards [pointFormCore_gradient hγ ha y φ] with x hx
  rw [hx]

end RepulsiveCoulomb
