module

public import LeanResearch.RepulsiveCoulomb.DbarBranchKernelDerivative
public import LeanResearch.RepulsiveCoulomb.DbarBranchScaledBumpMoment

@[expose] public section

/-! The first-order kernel is genuinely the differential commutator on the
dense compact smooth core. The coefficient derivative is literal; its
cancellation reduces the limit to the checked strong mollifier limit. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology Convolution Distributions
namespace RepulsiveCoulomb

theorem dbarVolumeFriedrichsKernel_split {N : ℕ} {A B : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N)))
    (hB : MemLp B ⊤ (volume : Measure (CoulombConfig N)))
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    dbarVolumeFriedrichsKernel hA hB ψ v f =
      dbarVolumeMulL hA (dbarVolumeKernelLp (dbarRealKernelDerivative v (dbarBumpKernelTest ψ)) f) -
        dbarVolumeKernelLp (dbarRealKernelDerivative v (dbarBumpKernelTest ψ)) (dbarVolumeMulL hA f) +
        coulombVolumeLpMollify ψ (dbarVolumeMulL hB f) := by
  let k := dbarRealKernelDerivative v (dbarBumpKernelTest ψ)
  have hi := dbarVolumeKernelLp_integrable k f
  have hiA := (dbarVolumeMulL hA).integrable_comp hi
  have hiAf := dbarVolumeKernelLp_integrable k (dbarVolumeMulL hA f)
  have hfirst : (∫ t, ((fderiv ℝ (ψ.normed volume) t) v) • dbarVolumeTranslationComm hA (-t) f) =
      dbarVolumeMulL hA (dbarVolumeKernelLp k f) - dbarVolumeKernelLp k (dbarVolumeMulL hA f) := by
    calc
      _ = ∫ t, dbarVolumeMulL hA (k t • Measure.translateLp volume 2 (-t) f) -
          k t • Measure.translateLp volume 2 (-t) (dbarVolumeMulL hA f) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun t => by
          dsimp only [k]
          rw [dbarRealKernelDerivative_apply]
          change ((fderiv ℝ (ψ.normed volume) t) v) •
            (dbarVolumeMulL hA (Measure.translateLp volume 2 (-t) f) -
              Measure.translateLp volume 2 (-t) (dbarVolumeMulL hA f)) = _
          rw [smul_sub, map_smul]
          rfl
      _ = _ := by
        rw [integral_sub hiA hiAf, (dbarVolumeMulL hA).integral_comp_comm hi]
        rfl
  unfold dbarVolumeFriedrichsKernel
  rw [hfirst]

theorem dbarVolumeFriedrichsKernel_core_identity {N : ℕ}
    (A φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N) :
    dbarVolumeFriedrichsKernel (A.memLp_top (μ := volume))
      ((dbarVolumeCoreDerivative v A).memLp_top (μ := volume)) ψ v (dbarVolumeCoreValue φ) =
      dbarVolumeMulL (A.memLp_top (μ := volume))
        (coulombVolumeLpMollify ψ (dbarVolumeCoreValue (dbarVolumeCoreDerivative v φ))) -
      coulombVolumeLpMollify ψ
        (dbarVolumeMulL (A.memLp_top (μ := volume)) (dbarVolumeCoreValue (dbarVolumeCoreDerivative v φ))) := by
  have hprod : dbarVolumeCoreValue (dbarVolumeCoreDerivative v (dbarVolumeCoreProduct A φ)) =
      dbarVolumeMulL (A.memLp_top (μ := volume)) (dbarVolumeCoreValue (dbarVolumeCoreDerivative v φ)) +
        dbarVolumeMulL ((dbarVolumeCoreDerivative v A).memLp_top (μ := volume)) (dbarVolumeCoreValue φ) := by
    rw [dbarVolumeCoreProduct_derivative]
    change dbarVolumeCoreValueLinear N (_ + _) = _
    rw [map_add]
    change dbarVolumeCoreValue (dbarVolumeCoreProduct A (dbarVolumeCoreDerivative v φ)) +
      dbarVolumeCoreValue (dbarVolumeCoreProduct (dbarVolumeCoreDerivative v A) φ) = _
    rw [dbarVolumeCoreProduct_value, dbarVolumeCoreProduct_value]
  rw [dbarVolumeFriedrichsKernel_split, ← dbarVolumeCoreProduct_value,
    dbarVolumeKernelLp_derivative_exchange, dbarVolumeKernelLp_derivative_exchange,
    hprod, dbarVolumeKernelLp_add]
  simp only [dbarBumpKernelTest_mollifier]
  abel

theorem dbarVolumeFriedrichsKernel_core_tendsto {N : ℕ} {ι : Type*} {l : Filter ι}
    (A φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (ψ : ι → ContDiffBump (0 : CoulombConfig N))
    (hψ : Tendsto (fun i => (ψ i).rOut) l (𝓝 0)) (v : CoulombConfig N) :
    Tendsto (fun i => dbarVolumeFriedrichsKernel (A.memLp_top (μ := volume))
      ((dbarVolumeCoreDerivative v A).memLp_top (μ := volume)) (ψ i) v (dbarVolumeCoreValue φ)) l (𝓝 0) := by
  simp_rw [dbarVolumeFriedrichsKernel_core_identity]
  exact dbarVolumeMollifier_mul_comm_tendsto (A.memLp_top (μ := volume)) ψ hψ
    (dbarVolumeCoreValue (dbarVolumeCoreDerivative v φ))

end RepulsiveCoulomb
