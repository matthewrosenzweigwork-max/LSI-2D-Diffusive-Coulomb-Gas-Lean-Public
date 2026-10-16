import LeanResearch.RepulsiveCoulomb.DbarBranchTranslationMultiplier

/-! The literal L2-valued first-order Friedrichs kernel and its quantitative
bound. The derivative moment is exposed explicitly; kernel cancellation and
weak differential identification are separate subsequent obligations. -/
noncomputable section
open Set MeasureTheory Filter
open scoped NNReal Topology
namespace RepulsiveCoulomb

def dbarBumpDerivativeMoment {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    (v : CoulombConfig N) : ℝ :=
  ∫ t, ‖(fderiv ℝ (ψ.normed volume) t) v‖ * ‖t‖

theorem dbarBumpDerivativeMoment_integrable {N : ℕ}
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N) :
    Integrable (fun t => ‖(fderiv ℝ (ψ.normed volume) t) v‖ * ‖t‖) volume := by
  have hc : Continuous (fun t => (fderiv ℝ (ψ.normed volume) t) v) :=
    ((ψ.contDiff_normed (μ := volume) (n := 1)).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  exact (hc.norm.mul continuous_norm).integrable_of_hasCompactSupport
    (((ψ.hasCompactSupport_normed (μ := volume)).fderiv_apply (𝕜 := ℝ) v).norm.mul_right)

def dbarVolumeFriedrichsKernel {N : ℕ} {A B : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N)))
    (hB : MemLp B ⊤ (volume : Measure (CoulombConfig N)))
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  (∫ t, ((fderiv ℝ (ψ.normed volume) t) v) • dbarVolumeTranslationComm hA (-t) f) +
    coulombVolumeLpMollify ψ (dbarVolumeMulL hB f)

theorem dbarVolumeFriedrichsKernel_integrable {N : ℕ} {A : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N)))
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    Integrable (fun t => ((fderiv ℝ (ψ.normed volume) t) v) •
      dbarVolumeTranslationComm hA (-t) f) volume := by
  have hc : Continuous (fun t => (fderiv ℝ (ψ.normed volume) t) v) :=
    ((ψ.contDiff_normed (μ := volume) (n := 1)).fderiv_right (m := 0) (by norm_num)).continuous.clm_apply continuous_const
  exact (hc.smul ((dbarVolumeTranslationComm_continuous hA f).comp continuous_neg)).integrable_of_hasCompactSupport
    (((ψ.hasCompactSupport_normed (μ := volume)).fderiv_apply (𝕜 := ℝ) v).smul_right)

theorem dbarVolumeFriedrichsKernel_norm_le {N : ℕ} {A B : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N)))
    (hB : MemLp B ⊤ (volume : Measure (CoulombConfig N))) {C : ℝ≥0}
    (hLip : LipschitzWith C A) {M : ℝ} (hM : ∀ᵐ x ∂volume, ‖B x‖ ≤ M)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    ‖dbarVolumeFriedrichsKernel hA hB ψ v f‖ ≤
      ((C : ℝ) * dbarBumpDerivativeMoment ψ v + M) * ‖f‖ := by
  have hfirst : ‖∫ t, ((fderiv ℝ (ψ.normed volume) t) v) •
      dbarVolumeTranslationComm hA (-t) f‖ ≤
      (C : ℝ) * dbarBumpDerivativeMoment ψ v * ‖f‖ := by
    calc
      _ ≤ ∫ t, (‖(fderiv ℝ (ψ.normed volume) t) v‖ * ‖t‖) * ((C : ℝ) * ‖f‖) := by
        apply norm_integral_le_of_norm_le
          ((dbarBumpDerivativeMoment_integrable ψ v).mul_const ((C : ℝ) * ‖f‖))
        exact Eventually.of_forall fun t => by
          rw [norm_smul]
          have ht := dbarVolumeTranslationComm_norm_le hA hLip (-t) f
          rw [norm_neg] at ht
          calc
            _ ≤ ‖(fderiv ℝ (ψ.normed volume) t) v‖ * ((C : ℝ) * ‖t‖ * ‖f‖) :=
              mul_le_mul_of_nonneg_left ht (norm_nonneg _)
            _ = _ := by ring
      _ = _ := by rw [integral_mul_const]; unfold dbarBumpDerivativeMoment; ring
  have hsecond : ‖coulombVolumeLpMollify ψ (dbarVolumeMulL hB f)‖ ≤ M * ‖f‖ :=
    (coulombVolumeLpMollify_norm_le ψ _).trans (dbarVolumeMulL_norm_le hB hM f)
  calc
    _ ≤ ‖∫ t, ((fderiv ℝ (ψ.normed volume) t) v) • dbarVolumeTranslationComm hA (-t) f‖ +
        ‖coulombVolumeLpMollify ψ (dbarVolumeMulL hB f)‖ := norm_add_le _ _
    _ ≤ (C : ℝ) * dbarBumpDerivativeMoment ψ v * ‖f‖ + M * ‖f‖ := add_le_add hfirst hsecond
    _ = _ := by ring

end RepulsiveCoulomb
