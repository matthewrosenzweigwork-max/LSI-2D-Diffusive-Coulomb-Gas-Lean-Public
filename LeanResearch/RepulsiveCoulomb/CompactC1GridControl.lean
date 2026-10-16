module

public import LeanResearch.RepulsiveCoulomb.TriangularGridApproximationError
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Topology.UniformSpace.HeineCantor

@[expose] public section

/-! Actual global controls for a compact C1 observable, without a C2 assumption. -/
noncomputable section
open Set
open scoped NNReal
namespace RepulsiveCoulomb

theorem compactC1_fderiv_uniformContinuous {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : UniformContinuous (fderiv ℝ f) := by
  have hdf : HasCompactSupport (fderiv ℝ f) := hc.fderiv (𝕜 := ℝ)
  exact hdf.uniformContinuous_of_continuous (hf.continuous_fderiv one_ne_zero)

theorem compactC1_exists_lipschitz {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) : ∃ C : ℝ≥0, LipschitzWith C f := by
  have hdf : HasCompactSupport (fderiv ℝ f) := hc.fderiv (𝕜 := ℝ)
  obtain ⟨C,hC⟩ := hdf.exists_bound_of_continuous (hf.continuous_fderiv one_ne_zero)
  have hC0 : 0 ≤ C := (norm_nonneg (fderiv ℝ f 0)).trans (hC 0)
  refine ⟨⟨C,hC0⟩,lipschitzWith_of_nnnorm_fderiv_le (hf.differentiable (by norm_num)) ?_⟩
  intro z
  change ‖fderiv ℝ f z‖ ≤ C
  exact hC z

theorem compactC1_grid_value_error {f : ℂ → ℝ} (hf : ContDiff ℝ 1 f)
    (hc : HasCompactSupport f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ) (hh : 0 < h) (z : ℂ),
      |sampledGridApproximation f hc h hh z - f z| ≤ C*h := by
  obtain ⟨C,hC⟩ := compactC1_exists_lipschitz hf hc
  exact ⟨2*(C:ℝ),by positivity,fun h hh z => sampledGridApproximation_abs_error hc hC h hh z⟩

theorem sampledGridApproximation_continuous (f : ℂ → ℝ) (hc : HasCompactSupport f)
    (h : ℝ) (hh : 0 < h) : Continuous (sampledGridApproximation f hc h hh) :=
  (triangularGridInterpolant_lipschitz (compactGridSamples f hc h hh)).continuous.comp
    (continuous_const_smul h⁻¹)

end RepulsiveCoulomb
