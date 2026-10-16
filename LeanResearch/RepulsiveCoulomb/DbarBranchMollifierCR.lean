import LeanResearch.RepulsiveCoulomb.DbarBranchMollifierTest
import LeanResearch.RepulsiveCoulomb.DbarBranchClassicalCR

/-! Interior smoothing preserves the actual weak Cauchy-Riemann equations.
The data are elements of the original weighted L2 weak kernel; the smooth
functions below are defined by honest Lebesgue convolution after compact
localization. No weak-to-classical regularity is assumed. -/
noncomputable section
open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology Convolution Distributions
namespace RepulsiveCoulomb

theorem coulombScalarMollify_directional {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (coulombMeasure N β))
    (z v : CoulombConfig N) :
    fderiv ℝ (coulombScalarMollify K ψ f) z v =
      ∫ y, fderiv ℝ (ψ.normed volume) (z - y) v • K.indicator (f : CoulombConfig N → ℂ) y := by
  let u : CoulombConfig N → ℂ := K.indicator (f : CoulombConfig N → ℂ)
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := (ContinuousLinearMap.lsmul ℝ ℝ).flip
  have hu : LocallyIntegrable u volume :=
    (coulombL2_indicator_integrable_volume hβ hK hKΩ f).locallyIntegrable
  have hψ : ContDiff ℝ (⊤ : ℕ∞) (ψ.normed volume) := (ψ.contDiff_normed (μ := volume))
  have hd := (ψ.hasCompactSupport_normed (μ := volume)).hasFDerivAt_convolution_right L hu (hψ.of_le (by simp)) z
  have hInt := ((ψ.hasCompactSupport_normed (μ := volume)).fderiv ℝ).convolutionExists_right
    (L.precompR (CoulombConfig N)) hu (hψ.continuous_fderiv (by simp)) z
  have heq : coulombScalarMollify K ψ f = u ⋆[L, volume] ψ.normed volume :=
    (convolution_flip (ContinuousLinearMap.lsmul ℝ ℝ)).symm
  rw [heq, hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hInt]
  rfl

theorem coulombScalarMollify_directional_test {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (coulombMeasure N β))
    (z v : CoulombConfig N) (hball : closedBall z ψ.rOut ⊆ K) :
    fderiv ℝ (coulombScalarMollify K ψ f) z v =
      -(∫ y, (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v
        (coulombMollifierTest ψ z (hball.trans hKΩ))) y • f y) := by
  rw [coulombScalarMollify_directional hβ hK hKΩ ψ f z v,
    ← coulombMollifierTest_lineDeriv_indicator_pairing ψ z v hKΩ hball f, ← integral_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun y => by
    dsimp only
    rw [coulombMollifierTest_lineDeriv, neg_smul, neg_neg]

theorem coulombScalarMollify_dbar_zero {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (coulombMeasure N β))
    (hf : (f, 0) ∈ coulombMaxDbarGraph hβ) (z : CoulombConfig N)
    (hball : closedBall z ψ.rOut ⊆ K) : coulombDbar (coulombScalarMollify K ψ f) z = 0 := by
  have hzero : coulombL2Distribution hβ (0 : Lp ℂ 2 (coulombMeasure N β)) = 0 :=
    map_zero (coulombL2DistributionLinear hβ ℂ)
  ext i
  change coulombDbarCoordinate (coulombScalarMollify K ψ f) z i = 0
  rw [coulombDbarCoordinate,
    coulombScalarMollify_directional_test hβ hK hKΩ ψ f z _ hball,
    coulombScalarMollify_directional_test hβ hK hKΩ ψ f z _ hball]
  have hi := hf i (coulombMollifierTest ψ z (hball.trans hKΩ))
  rw [coulombWeakDbarConstraintL_apply, map_zero, hzero] at hi
  simp only [zero_apply, zero_add, coulombL2Distribution_apply, Complex.real_smul,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hi
  linear_combination -hi

theorem coulombScalarMollify_complex_differentiableAt {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (f : Lp ℂ 2 (coulombMeasure N β))
    (hf : (f, 0) ∈ coulombMaxDbarGraph hβ) (z : CoulombConfig N)
    (hball : closedBall z ψ.rOut ⊆ K) : DifferentiableAt ℂ (coulombScalarMollify K ψ f) z :=
  coulombDifferentiableAt_of_real_and_dbar_zero
    ((coulombScalarMollify_contDiff hβ hK hKΩ ψ f).differentiable (by simp) z)
    (coulombScalarMollify_dbar_zero hβ hK hKΩ ψ f hf z hball)

end RepulsiveCoulomb
