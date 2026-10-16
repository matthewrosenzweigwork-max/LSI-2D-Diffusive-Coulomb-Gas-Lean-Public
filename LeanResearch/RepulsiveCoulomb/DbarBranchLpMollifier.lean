module

public import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel
public import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.MeasureTheory.Function.Lp.Translation
public import Mathlib.Analysis.Calculus.BumpFunction.Convolution

@[expose] public section

/-! Norm-convergent interior regularization at the level of actual Lebesgue L2
classes. The scalar-convolution representative and weak-equation preservation
are subsequent obligations; no point evaluation on L2 is used here. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology Convolution
namespace RepulsiveCoulomb

def coulombVolumeLpMollify {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) : Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  (ψ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
    (fun h : CoulombConfig N => Measure.translateLp volume 2 h f)) 0

theorem coulombVolumeLpMollify_norm_le {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) : ‖coulombVolumeLpMollify ψ f‖ ≤ ‖f‖ := by
  rw [coulombVolumeLpMollify, convolution_def]
  calc
    _ ≤ ∫ y, ‖ψ.normed volume y • Measure.translateLp volume 2 (0 - y) f‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ y, ψ.normed volume y * ‖f‖ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun y => by
        change ‖ψ.normed volume y • Measure.translateLp volume 2 (0 - y) f‖ = ψ.normed volume y * ‖f‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (ψ.nonneg_normed (μ := volume) y)]
        simp
    _ = ‖f‖ := by rw [integral_mul_const, ψ.integral_normed, one_mul]

theorem coulombVolumeLpMollify_tendsto {N : ℕ} {ι : Type*} {l : Filter ι}
    (ψ : ι → ContDiffBump (0 : CoulombConfig N))
    (hψ : Tendsto (fun i => (ψ i).rOut) l (𝓝 0))
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Tendsto (fun i => coulombVolumeLpMollify (ψ i) f) l (𝓝 f) := by
  have h := ContDiffBump.convolution_tendsto_right_of_continuous
    (μ := (volume : Measure (CoulombConfig N))) hψ
    (Measure.continuous_translateLp (mu := volume) (p := 2) (by norm_num) f) (0 : CoulombConfig N)
  simpa only [coulombVolumeLpMollify, Measure.translateLp_zero] using h

end RepulsiveCoulomb
