module

public import LeanResearch.RepulsiveCoulomb.WeightedPointNormalization
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

@[expose] public section

/-! The planar Ladyzhenskaya inequality (manuscript Lemma 3.5).
We apply the endpoint Sobolev inequality to the square, use its actual
Fréchet derivative, and then apply Hölder with exponents two and two.
The gradient is the real Hilbert-space gradient on the Euclidean plane.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal NNReal
namespace RepulsiveCoulomb

/-- A fixed finite constant; it does not depend on the test function. -/
def planarLadyzhenskayaConstant : ℝ≥0 :=
  2 * eLpNormLESNormFDerivOneConst (volume : Measure ℂ) 2

theorem eLpNorm_gradient_eq_fderiv {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v)
    (p : ℝ≥0∞) :
    eLpNorm (gradient v) p volume = eLpNorm (fderiv ℝ v) p volume := by
  have hd := hv.continuous_fderiv one_ne_zero
  have hg : Continuous (gradient v) := (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp hd
  apply eLpNorm_congr_norm_ae hg.aestronglyMeasurable hd.aestronglyMeasurable
  filter_upwards [] with z
  simp [gradient]

theorem planar_ladyzhenskaya_eLpNorm {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) :
    eLpNorm v 4 volume ^ 2 ≤ (planarLadyzhenskayaConstant : ℝ≥0∞) *
      eLpNorm v 2 volume * eLpNorm (gradient v) 2 volume := by
  have hd : Continuous (fderiv ℝ v) := hv.continuous_fderiv one_ne_zero
  have hv2 : ContDiff ℝ 1 (fun z ↦ v z ^ 2) := hv.pow 2
  have hc2 : HasCompactSupport (fun z ↦ v z ^ 2) := by
    convert hc.mul_right (f' := v) using 1
    funext z
    exact pow_two (v z)
  have hp : NNReal.HolderConjugate (Module.finrank ℝ ℂ) 2 := by
    rw [Complex.finrank_real_complex]
    exact ⟨by norm_num, by norm_num, by norm_num⟩
  have hs := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure ℂ) hv2 hc2 hp
  have hnorm : eLpNorm (fun z ↦ v z ^ 2) 2 volume = eLpNorm v 4 volume ^ 2 := by
    have h := eLpNorm_norm_rpow (μ := volume) (p := 2) v hv.continuous.aestronglyMeasurable
      (by norm_num : (0 : ℝ) < 2)
    norm_num [Real.rpow_two, Real.norm_eq_abs, sq_abs, ENNReal.rpow_two] at h
    exact h
  have hderiv : fderiv ℝ (fun z ↦ v z ^ 2) =
      (2 : ℝ) • (v • fderiv ℝ v) := by
    funext z
    have h := ((hv.differentiable one_ne_zero z).hasFDerivAt.pow 2).fderiv
    simpa [Pi.smul_apply, nsmul_eq_mul, smul_smul] using h
  have hholder := eLpNorm_smul_le_mul_eLpNorm (μ := volume) (φ := v) (f := fderiv ℝ v) (p := 2) (q := 2) (r := 1)
    hv.continuous.aestronglyMeasurable hd.aestronglyMeasurable
  norm_num only [ENNReal.coe_ofNat, NNReal.coe_ofNat] at hs
  have hscale : eLpNorm (fderiv ℝ (fun z ↦ v z ^ 2)) 1 volume ≤
      2 * eLpNorm (v • fderiv ℝ v) 1 volume := by
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := volume)
      (g := v • fderiv ℝ v) (c := (2 : ℝ))
      (hv2.continuous_fderiv one_ne_zero).aestronglyMeasurable
      (by
        filter_upwards [] with z
        rw [hderiv]
        simp [Pi.smul_apply, norm_smul]) 1
    norm_num at h
    exact h
  rw [hnorm] at hs
  rw [eLpNorm_gradient_eq_fderiv hv]
  calc
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure ℂ) 2 : ℝ≥0∞) *
        (2 * eLpNorm (v • fderiv ℝ v) 1 volume) :=
      hs.trans (by gcongr)
    _ ≤ (eLpNormLESNormFDerivOneConst (volume : Measure ℂ) 2 : ℝ≥0∞) *
        (2 * (eLpNorm v 2 volume * eLpNorm (fderiv ℝ v) 2 volume)) := by
      gcongr
    _ = _ := by simp only [planarLadyzhenskayaConstant, ENNReal.coe_mul,
      ENNReal.coe_ofNat]; ring

/-- The finite real-norm form of manuscript Lemma 3.5. -/
theorem planar_ladyzhenskaya {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) :
    lpNorm v 4 volume ^ 2 ≤ (planarLadyzhenskayaConstant : ℝ) *
      lpNorm v 2 volume * lpNorm (gradient v) 2 volume := by
  have hv2 : MemLp v 2 volume := hv.continuous.memLp_of_hasCompactSupport hc
  have hd2 : MemLp (fderiv ℝ v) 2 volume :=
    (hv.continuous_fderiv one_ne_zero).memLp_of_hasCompactSupport (hc.fderiv ℝ)
  have hg : eLpNorm (gradient v) 2 volume ≠ ⊤ := by
    rw [eLpNorm_gradient_eq_fderiv hv]
    exact hd2.ne
  have hfinite : ((planarLadyzhenskayaConstant : ℝ≥0∞) *
      eLpNorm v 2 volume * eLpNorm (gradient v) 2 volume) ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hv2.ne) hg
  have h := ENNReal.toReal_mono hfinite (planar_ladyzhenskaya_eLpNorm hv hc)
  simpa [lpNorm, ENNReal.toReal_pow, ENNReal.toReal_mul] using h

end RepulsiveCoulomb
