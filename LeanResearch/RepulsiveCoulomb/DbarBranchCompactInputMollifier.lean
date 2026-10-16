import LeanResearch.RepulsiveCoulomb.DbarBranchJointMollification

/-! Compactly supported L2 inputs are mollified into genuine compact smooth
test functions. Their literal directional derivatives represent the L2
kernels used in the simultaneous weak-system convergence theorem. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology Convolution Distributions Pointwise
namespace RepulsiveCoulomb

theorem dbarCompactInput_integrable {N : ℕ} {f : CoulombConfig N → ℂ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f) : Integrable f volume := by
  have hi := (hf.locallyIntegrable (by norm_num)).integrableOn_isCompact hfc.isCompact
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp hi

def dbarCompactInputMollifyTest {N : ℕ} {f : CoulombConfig N → ℂ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (ψ : ContDiffBump (0 : CoulombConfig N)) :
    TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤ :=
  ⟨ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f,
    (ψ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left (μ := volume)
      (n := (⊤ : ℕ∞)) (ContinuousLinearMap.lsmul ℝ ℝ)
      (ψ.contDiff_normed (μ := volume)) (hf.locallyIntegrable (by norm_num)),
    (ψ.hasCompactSupport_normed (μ := volume)).convolution (ContinuousLinearMap.lsmul ℝ ℝ) hfc,
    subset_univ _⟩

theorem dbarCompactInputMollifyTest_value {N : ℕ} {f : CoulombConfig N → ℂ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (ψ : ContDiffBump (0 : CoulombConfig N)) :
    dbarVolumeCoreValue (dbarCompactInputMollifyTest hf hfc ψ) =
      coulombVolumeLpMollify ψ (hf.toLp f) := by
  have hfi : Integrable (hf.toLp f : CoulombConfig N → ℂ) volume :=
    (dbarCompactInput_integrable hf hfc).congr hf.coeFn_toLp.symm
  have he := convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ) (f := ψ.normed volume)
    ae_eq_rfl hf.coeFn_toLp
  apply Lp.ext
  filter_upwards [dbarVolumeCoreValue_coe (dbarCompactInputMollifyTest hf hfc ψ),
    coulombVolumeLpMollify_coe ψ (hf.toLp f) hfi] with z hcore hm
  rw [hcore, hm, he]
  rfl

theorem dbarKernel_convolution_fderiv {N : ℕ}
    (ψ : TestFunction (⊤ : Opens (CoulombConfig N)) ℝ ⊤)
    {f : CoulombConfig N → ℂ} (hf : LocallyIntegrable f volume) (z v : CoulombConfig N) :
    fderiv ℝ (ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z v =
      (dbarRealKernelDerivative v ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z := by
  let L : ℝ →L[ℝ] ℂ →L[ℝ] ℂ := ContinuousLinearMap.lsmul ℝ ℝ
  have hd := ψ.hasCompactSupport.hasFDerivAt_convolution_left (μ := volume) L
    (ψ.contDiff.of_le (by simp)) hf z
  have hi := (ψ.hasCompactSupport.fderiv ℝ).convolutionExists_left (μ := volume) (L.precompL (CoulombConfig N))
    (ψ.contDiff.continuous_fderiv (by simp)) hf z
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hi]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by
    simp only [dbarRealKernelDerivative_apply, ContinuousLinearMap.precompL_apply]
    rfl

theorem dbarCompactInputMollifyTest_derivative_value {N : ℕ} {f : CoulombConfig N → ℂ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N) :
    dbarVolumeCoreValue (dbarVolumeCoreDerivative v (dbarCompactInputMollifyTest hf hfc ψ)) =
      dbarVolumeKernelLp (dbarRealKernelDerivative v (dbarBumpKernelTest ψ)) (hf.toLp f) := by
  have hfi : Integrable (hf.toLp f : CoulombConfig N → ℂ) volume :=
    (dbarCompactInput_integrable hf hfc).congr hf.coeFn_toLp.symm
  have he := convolution_congr (ContinuousLinearMap.lsmul ℝ ℝ)
    (f := (dbarRealKernelDerivative v (dbarBumpKernelTest ψ) : CoulombConfig N → ℝ))
    ae_eq_rfl hf.coeFn_toLp
  apply Lp.ext
  filter_upwards [dbarVolumeCoreValue_coe
      (dbarVolumeCoreDerivative v (dbarCompactInputMollifyTest hf hfc ψ)),
    dbarVolumeKernelLp_coe (dbarRealKernelDerivative v (dbarBumpKernelTest ψ)) (hf.toLp f) hfi] with z hcore hk
  rw [hcore, hk, he, dbarVolumeCoreDerivative_apply]
  change fderiv ℝ (dbarBumpKernelTest ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) z v = _
  exact dbarKernel_convolution_fderiv (dbarBumpKernelTest ψ) (hf.locallyIntegrable (by norm_num)) z v

theorem dbarCompactInputMollifyTest_support {N : ℕ} {f : CoulombConfig N → ℂ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (ψ : ContDiffBump (0 : CoulombConfig N)) {K : Set (CoulombConfig N)}
    (hK : IsCompact K) (hsupp : Function.support f ⊆ K) :
    tsupport (dbarCompactInputMollifyTest hf hfc ψ : CoulombConfig N → ℂ) ⊆
      Metric.closedBall 0 ψ.rOut + K := by
  apply closure_minimal _ ((isCompact_closedBall _ _).add hK).isClosed
  change Function.support (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f) ⊆ _
  apply (support_convolution_subset (ContinuousLinearMap.lsmul ℝ ℝ)).trans
  apply add_subset_add _ hsupp
  rw [ψ.support_normed_eq (μ := volume)]
  exact Metric.ball_subset_closedBall

def dbarCompactInputMollifyCollisionTest {N : ℕ} {f : CoulombConfig N → ℂ}
    (hf : MemLp f 2 volume) (hfc : HasCompactSupport f)
    (ψ : ContDiffBump (0 : CoulombConfig N)) {K : Set (CoulombConfig N)}
    (hK : IsCompact K) (hsupp : Function.support f ⊆ K)
    (hmargin : Metric.closedBall (0 : CoulombConfig N) ψ.rOut + K ⊆
      (coulombDomain N : Set (CoulombConfig N))) :
    TestFunction (coulombDomain N) ℂ ⊤ :=
  ⟨dbarCompactInputMollifyTest hf hfc ψ,
    (dbarCompactInputMollifyTest hf hfc ψ).contDiff,
    (dbarCompactInputMollifyTest hf hfc ψ).hasCompactSupport,
    (dbarCompactInputMollifyTest_support hf hfc ψ hK hsupp).trans hmargin⟩

end RepulsiveCoulomb
