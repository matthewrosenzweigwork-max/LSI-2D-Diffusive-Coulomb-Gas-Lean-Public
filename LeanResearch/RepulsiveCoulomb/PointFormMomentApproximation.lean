module

public import LeanResearch.RepulsiveCoulomb.PointCoreMomentBound
public import LeanResearch.RepulsiveCoulomb.DoubleOscillationFatou
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Exact norm/integral and finiteness adapters for closing the weighted
quadratic-moment estimate on the actual complete form domain. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators ENNReal
namespace RepulsiveCoulomb

theorem pointFormValue_norm_sq_eq_integral {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (u : PointFormDomain hγ ha y) :
    ‖pointFormValueL hγ ha y u‖ ^ 2 =
      ∫ x, (pointFormValueL hγ ha y u x) ^ 2 ∂pointMeasure γ a y := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs, sq_abs] using real_inner_self_eq_norm_sq (pointFormValueL hγ ha y u x)

theorem pointFormCore_norm_sq_eq_integrals {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    ‖pointFormCore hγ ha y φ‖ ^ 2 =
      (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
      (∫ x, φ x ^ 2 ∂pointMeasure γ a y) := by
  have hv : (∫ x, (pointFormValueL hγ ha y (pointFormCore hγ ha y φ) x) ^ 2 ∂pointMeasure γ a y) =
      ∫ x, φ x ^ 2 ∂pointMeasure γ a y := by
    apply integral_congr_ae
    filter_upwards [pointFormCore_value hγ ha y φ] with x hx
    rw [hx]
  have hg : (∫ x, ‖pointFormGradientL hγ ha y (pointFormCore hγ ha y φ) x‖ ^ 2 ∂pointMeasure γ a y) =
      ∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y := by
    apply integral_congr_ae
    filter_upwards [pointFormCore_gradient hγ ha y φ] with x hx
    rw [hx]
  rw [pointForm_norm_sq, pointFormValue_norm_sq_eq_integral, pointFormEnergy_eq_integral, hv, hg]
  ring

theorem pointCore_moment_integrable {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    Integrable (fun x : ℂ => ‖x‖ ^ 2 * φ x ^ 2) (pointMeasure γ a y) := by
  let _ := pointMeasure_isProbability hγ ha y
  have hs : HasCompactSupport (fun x : ℂ => φ x ^ 2) :=
    φ.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by simp)
  exact ((continuous_norm.pow 2).mul (φ.continuous.pow 2)).integrable_of_hasCompactSupport hs.mul_left

end RepulsiveCoulomb
