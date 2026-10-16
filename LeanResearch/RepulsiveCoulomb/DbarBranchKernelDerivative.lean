module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactVolumeCore

@[expose] public section

/-! Transfer a directional derivative between the two genuine compact factors
of convolution, both pointwise and in the actual Lebesgue-L2 classes. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology Convolution Distributions
namespace RepulsiveCoulomb

def dbarRealKernelDerivative {N : ℕ} (v : CoulombConfig N)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) :
    TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤ :=
  TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v ψ

theorem dbarRealKernelDerivative_apply {N : ℕ} (v : CoulombConfig N)
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤) (x : CoulombConfig N) :
    dbarRealKernelDerivative v ψ x = fderiv ℝ (ψ : CoulombConfig N → ℝ) x v := by
  rw [dbarRealKernelDerivative, TestFunction.lineDerivCLM_eq_fderivCLM]
  rw [TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) _ (by simp)]

theorem dbarCompact_convolution_derivative_exchange {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) (v : CoulombConfig N) :
    dbarRealKernelDerivative v ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ : CoulombConfig N → ℂ) =
      ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (dbarVolumeCoreDerivative v φ : CoulombConfig N → ℂ) := by
  let L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  have hψloc : LocallyIntegrable (ψ : CoulombConfig N → ℝ) volume := ψ.continuous.locallyIntegrable
  have hφloc : LocallyIntegrable (φ : CoulombConfig N → ℂ) volume := φ.continuous.locallyIntegrable
  ext x
  have hl := ψ.hasCompactSupport.hasFDerivAt_convolution_left (μ := volume) L
    (ψ.contDiff.of_le (by simp)) hφloc x
  have hr := φ.hasCompactSupport.hasFDerivAt_convolution_right (μ := volume) L
    hψloc (φ.contDiff.of_le (by simp)) x
  have hil := (ψ.hasCompactSupport.fderiv ℝ).convolutionExists_left (μ := volume) (L.precompL (CoulombConfig N))
    (ψ.contDiff.continuous_fderiv (by simp)) hφloc x
  have hir := (φ.hasCompactSupport.fderiv ℝ).convolutionExists_right (μ := volume) (L.precompR (CoulombConfig N))
    hψloc (φ.contDiff.continuous_fderiv (by simp)) x
  have he := congrArg (fun D : CoulombConfig N →L[ℝ] ℂ => D v) (hl.unique hr)
  rw [convolution_def, convolution_def, ContinuousLinearMap.integral_apply hil,
    ContinuousLinearMap.integral_apply hir] at he
  simpa only [convolution_def, dbarRealKernelDerivative_apply, dbarVolumeCoreDerivative_apply,
    ContinuousLinearMap.precompL_apply, ContinuousLinearMap.precompR_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply, L] using he

theorem dbarVolumeKernelLp_core_coe {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) :
    dbarVolumeKernelLp ψ (dbarVolumeCoreValue φ) =ᵐ[volume]
      ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] (φ : CoulombConfig N → ℂ) := by
  have hi : Integrable (dbarVolumeCoreValue φ : CoulombConfig N → ℂ) volume :=
    (φ.continuous.integrable_of_hasCompactSupport φ.hasCompactSupport).congr
      (dbarVolumeCoreValue_coe φ).symm
  have hc := convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (f := (ψ : CoulombConfig N → ℝ))
    ae_eq_rfl (dbarVolumeCoreValue_coe φ)
  exact (dbarVolumeKernelLp_coe ψ _ hi).trans (Eventually.of_forall fun x => congrFun hc x)

theorem dbarVolumeKernelLp_derivative_exchange {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤) (v : CoulombConfig N) :
    dbarVolumeKernelLp (dbarRealKernelDerivative v ψ) (dbarVolumeCoreValue φ) =
      dbarVolumeKernelLp ψ (dbarVolumeCoreValue (dbarVolumeCoreDerivative v φ)) := by
  apply Lp.ext
  filter_upwards [dbarVolumeKernelLp_core_coe (dbarRealKernelDerivative v ψ) φ,
    dbarVolumeKernelLp_core_coe ψ (dbarVolumeCoreDerivative v φ)] with x hl hr
  rw [hl, hr, dbarCompact_convolution_derivative_exchange]

def dbarBumpKernelTest {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N)) :
    TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤ :=
  ⟨ψ.normed volume, ψ.contDiff_normed (μ := volume), ψ.hasCompactSupport_normed (μ := volume), subset_univ _⟩

theorem dbarBumpKernelTest_mollifier {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    dbarVolumeKernelLp (dbarBumpKernelTest ψ) f = coulombVolumeLpMollify ψ f := by
  simp only [dbarVolumeKernelLp, coulombVolumeLpMollify, convolution_def, zero_sub]
  rfl

theorem dbarVolumeKernelLp_add {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (f g : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    dbarVolumeKernelLp ψ (f + g) = dbarVolumeKernelLp ψ f + dbarVolumeKernelLp ψ g := by
  unfold dbarVolumeKernelLp
  simp_rw [map_add, smul_add]
  exact integral_add (dbarVolumeKernelLp_integrable ψ f) (dbarVolumeKernelLp_integrable ψ g)

theorem dbarVolumeKernelLp_sub {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    (f g : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    dbarVolumeKernelLp ψ (f - g) = dbarVolumeKernelLp ψ f - dbarVolumeKernelLp ψ g := by
  unfold dbarVolumeKernelLp
  simp_rw [map_sub, smul_sub]
  exact integral_sub (dbarVolumeKernelLp_integrable ψ f) (dbarVolumeKernelLp_integrable ψ g)

theorem dbarVolumeLpMollify_sub {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    (f g : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    coulombVolumeLpMollify ψ (f - g) = coulombVolumeLpMollify ψ f - coulombVolumeLpMollify ψ g := by
  simp only [← dbarBumpKernelTest_mollifier, dbarVolumeKernelLp_sub]

end RepulsiveCoulomb
