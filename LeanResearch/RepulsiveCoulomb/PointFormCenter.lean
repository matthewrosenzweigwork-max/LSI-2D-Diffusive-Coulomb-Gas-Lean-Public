module

public import LeanResearch.RepulsiveCoulomb.PointUniformMomentBound
public import LeanResearch.RepulsiveCoulomb.PointConstantDomain

@[expose] public section

/-! Subtraction of actual constants inside the full physical form domain. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

def pointFormSubtractConstant {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) (c : ℝ) : PointFormDomain hγ ha y :=
  u - c • pointConstantForm hγ ha y

theorem pointFormSubtractConstant_value {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) (c : ℝ) :
    pointFormValueL hγ ha y (pointFormSubtractConstant hγ ha y u c) =ᵐ[pointMeasure γ a y]
      (fun x => pointFormValueL hγ ha y u x - c) := by
  unfold pointFormSubtractConstant
  rw [map_sub, map_smul]
  filter_upwards [Lp.coeFn_sub (pointFormValueL hγ ha y u)
      (c • pointFormValueL hγ ha y (pointConstantForm hγ ha y)),
    Lp.coeFn_smul c (pointFormValueL hγ ha y (pointConstantForm hγ ha y)),
    pointConstantForm_value hγ ha y] with x hx hs hc
  change (pointFormValueL hγ ha y u - c • pointFormValueL hγ ha y (pointConstantForm hγ ha y)) x = _
  rw [hx]
  change pointFormValueL hγ ha y u x -
    (c • pointFormValueL hγ ha y (pointConstantForm hγ ha y)) x = pointFormValueL hγ ha y u x - c
  rw [hs]
  change pointFormValueL hγ ha y u x -
    c * pointFormValueL hγ ha y (pointConstantForm hγ ha y) x = pointFormValueL hγ ha y u x - c
  rw [hc, mul_one]

theorem pointFormSubtractConstant_gradient {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) (c : ℝ) :
    pointFormGradientL hγ ha y (pointFormSubtractConstant hγ ha y u c) = pointFormGradientL hγ ha y u := by
  simp [pointFormSubtractConstant, map_sub, map_smul, pointConstantForm_gradient]

theorem pointFormSubtractConstant_energy {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) (c : ℝ) :
    pointFormEnergy hγ ha y (pointFormSubtractConstant hγ ha y u c) = pointFormEnergy hγ ha y u := by
  rw [pointFormEnergy, pointFormSubtractConstant_gradient, pointFormEnergy]

theorem pointCore_subtractConstant_value {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (c : ℝ) :
    pointFormValueL hγ ha y (pointFormSubtractConstant hγ ha y (pointFormCore hγ ha y φ) c) =ᵐ[pointMeasure γ a y]
      (fun x => φ x - c) := by
  filter_upwards [pointFormSubtractConstant_value hγ ha y (pointFormCore hγ ha y φ) c,
    pointFormCore_value hγ ha y φ] with x hx hφ
  exact hx.trans (by rw [hφ])

theorem pointCore_subtractConstant_norm_sq {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (c : ℝ) :
    ‖pointFormSubtractConstant hγ ha y (pointFormCore hγ ha y φ) c‖ ^ 2 =
      (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        (∫ x, (φ x - c) ^ 2 ∂pointMeasure γ a y) := by
  have hv : (∫ x, (pointFormValueL hγ ha y (pointFormSubtractConstant hγ ha y (pointFormCore hγ ha y φ) c) x) ^ 2 ∂pointMeasure γ a y) =
      ∫ x, (φ x - c) ^ 2 ∂pointMeasure γ a y := by
    apply integral_congr_ae
    filter_upwards [pointCore_subtractConstant_value hγ ha y φ c] with x hx
    exact congrArg (fun t : ℝ => t ^ 2) hx
  have hg : pointFormEnergy hγ ha y (pointFormCore hγ ha y φ) =
      ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y := by
    rw [pointFormEnergy_eq_integral]
    apply integral_congr_ae
    filter_upwards [pointFormCore_gradient hγ ha y φ] with x hx
    rw [hx]
  rw [pointForm_norm_sq, pointFormValue_norm_sq_eq_integral, pointFormSubtractConstant_energy, hv, hg]
  ring

theorem pointCore_subtractConstant_square_integrable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) (c : ℝ) :
    Integrable (fun x : ℂ => (φ x - c) ^ 2) (pointMeasure γ a y) := by
  have h := (Lp.memLp (pointFormValueL hγ ha y
    (pointFormSubtractConstant hγ ha y (pointFormCore hγ ha y φ) c))).integrable_sq
  apply h.congr
  filter_upwards [pointCore_subtractConstant_value hγ ha y φ c] with x hx
  exact congrArg (fun t : ℝ => t ^ 2) hx

end RepulsiveCoulomb
