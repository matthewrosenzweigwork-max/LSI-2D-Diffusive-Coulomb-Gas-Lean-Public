module

public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.Analysis.Sobolev.RellichKondrachov
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-! Actual Euclidean applications of the pinned Rellich theorem.
The physical real Hilbert gradient, not a gradient relative to a weighted
reference measure, occurs in the integral hypothesis. This module does not
assert the separate ground-state or tail estimates for the Gibbs ensemble.
-/
set_option maxHeartbeats 800000
noncomputable section
open MeasureTheory TopologicalSpace Metric Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [BorelSpace E]

def testFunctionW1p0 (Ω : Opens E) (φ : TestFunction Ω ℝ ⊤) :
    TauCeti.W1p0 (volume : Measure E) Ω 2 :=
  ⟨TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ,
    TauCeti.W1p.ofTestFunctionₗ_mem_w1p0Submodule φ⟩

theorem testFunctionW1p0_value (Ω : Opens E) (φ : TestFunction Ω ℝ ⊤) :
    TauCeti.W1p0.valueL (testFunctionW1p0 Ω φ) =
      TauCeti.testFunctionLp (mu := volume) 2 φ := by
  simp [testFunctionW1p0, TauCeti.W1p0.valueL_apply]

theorem testFunctionW1p0_norm_sq (Ω : Opens E) (φ : TestFunction Ω ℝ ⊤) :
    ‖testFunctionW1p0 Ω φ‖ ^ 2 = (∫ x in Ω, (φ x) ^ 2) +
      ∫ x in Ω, ‖gradient (φ : E → ℝ) x‖ ^ 2 := by
  change ‖TauCeti.W1p.ofTestFunctionₗ volume Ω 2 φ‖ ^ 2 = _
  rw [TauCeti.W1p.norm_sq_eq_norm_value_sq_add_norm_gradient_sq,
    ← TauCeti.W1p.integral_value_sq_eq_norm_value_sq,
    ← TauCeti.W1p.integral_norm_gradient_sq_eq_norm_gradient_sq]
  congr 1
  · apply integral_congr_ae
    filter_upwards [TauCeti.testFunctionLp_apply_ae (mu := volume) 2 φ] with x hx
    simp [TauCeti.W1p.value_ofTestFunctionₗ, hx]
  · apply integral_congr_ae
    filter_upwards [TauCeti.gradientTestFunctionLp_apply_ae (mu := volume) 2 φ] with x hx
    simp [TauCeti.W1p.gradient_ofTestFunctionₗ, hx]

theorem euclidean_testFunction_rellich (Ω : Opens E) (hΩ : Bornology.IsBounded (Ω : Set E))
    (C : ℝ) : IsCompact (closure ((fun φ : TestFunction Ω ℝ ⊤ ↦
      TauCeti.testFunctionLp (mu := volume) 2 φ) ''
      {φ | (∫ x in Ω, (φ x) ^ 2) + ∫ x in Ω, ‖gradient (φ : E → ℝ) x‖ ^ 2 ≤ C})) := by
  let T := TauCeti.W1p0.valueL (mu := (volume : Measure E)) (Omega := Ω) (p := 2)
  have hc : IsCompactOperator T :=
    TauCeti.W1p0.isCompactOperator_valueL (mu := (volume : Measure E)) (Omega := Ω) (p := 2) (by norm_num) hΩ
  have hK := hc.isCompact_closure_image_closedBall (|C| + 1)
  apply hK.of_isClosed_subset isClosed_closure
  apply closure_mono
  rintro _ ⟨φ, hφ, rfl⟩
  refine ⟨testFunctionW1p0 Ω φ, ?_, testFunctionW1p0_value Ω φ⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hs : ‖testFunctionW1p0 Ω φ‖ ^ 2 ≤ C := by
    rw [testFunctionW1p0_norm_sq]
    exact hφ
  nlinarith [norm_nonneg (testFunctionW1p0 Ω φ), le_abs_self C, abs_nonneg C, sq_nonneg |C|]

end RepulsiveCoulomb
