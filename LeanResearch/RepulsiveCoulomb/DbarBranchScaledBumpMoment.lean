module

public import LeanResearch.RepulsiveCoulomb.DbarBranchFriedrichsKernel
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

@[expose] public section

/-! A single fixed-shape smooth mollifier family has an exactly scale-invariant
first derivative moment. This discharges the radius-uniform constant needed
by the actual first-order Friedrichs kernel bound. -/
noncomputable section
open Set MeasureTheory Filter Module
open scoped NNReal Topology
namespace RepulsiveCoulomb

def dbarScaledBump {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    {ε : ℝ} (hε : 0 < ε) : ContDiffBump (0 : CoulombConfig N) where
  rIn := ε * ψ.rIn
  rOut := ε * ψ.rOut
  rIn_pos := mul_pos hε ψ.rIn_pos
  rIn_lt_rOut := mul_lt_mul_of_pos_left ψ.rIn_lt_rOut hε

theorem dbarScaledBump_apply {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    {ε : ℝ} (hε : 0 < ε) (x : CoulombConfig N) :
    dbarScaledBump ψ hε x = ψ (ε⁻¹ • x) := by
  rw [ContDiffBump.apply, ContDiffBump.apply]
  have hr : (ε * ψ.rOut) / (ε * ψ.rIn) = ψ.rOut / ψ.rIn := by
    field_simp [hε.ne', ψ.rIn_pos.ne']
  simp only [dbarScaledBump, hr, sub_zero, mul_inv_rev, smul_smul]

theorem dbarScaledBump_integral {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    {ε : ℝ} (hε : 0 < ε) :
    (∫ x, dbarScaledBump ψ hε x) = ε ^ finrank ℝ (CoulombConfig N) * ∫ x, ψ x := by
  simp_rw [dbarScaledBump_apply]
  simpa only [smul_eq_mul] using Measure.integral_comp_inv_smul_of_nonneg volume (fun x => ψ x) hε.le

theorem dbarScaledBump_normed {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    {ε : ℝ} (hε : 0 < ε) (x : CoulombConfig N) :
    (dbarScaledBump ψ hε).normed volume x =
      (ε ^ finrank ℝ (CoulombConfig N))⁻¹ * ψ.normed volume (ε⁻¹ • x) := by
  rw [ContDiffBump.normed_def, dbarScaledBump_apply, dbarScaledBump_integral,
    ContDiffBump.normed_def]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

theorem dbarScaledBump_fderiv_apply {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    {ε : ℝ} (hε : 0 < ε) (x v : CoulombConfig N) :
    (fderiv ℝ ((dbarScaledBump ψ hε).normed volume) x) v =
      (ε ^ finrank ℝ (CoulombConfig N))⁻¹ * ε⁻¹ *
        (fderiv ℝ (ψ.normed volume) (ε⁻¹ • x)) v := by
  have he : (dbarScaledBump ψ hε).normed volume =
      fun w => (ε ^ finrank ℝ (CoulombConfig N))⁻¹ * ψ.normed volume (ε⁻¹ • w) :=
    funext (dbarScaledBump_normed ψ hε)
  have hlin : HasFDerivAt (fun w : CoulombConfig N => ε⁻¹ • w)
      (ε⁻¹ • ContinuousLinearMap.id ℝ (CoulombConfig N)) x :=
    (hasFDerivAt_id x).const_smul ε⁻¹
  have hd := (((ψ.contDiff_normed (μ := volume) (n := 1)).differentiable (by norm_num)
    (ε⁻¹ • x)).hasFDerivAt.comp x hlin).const_mul
      ((ε ^ finrank ℝ (CoulombConfig N))⁻¹)
  have hfd := hd.fderiv
  change fderiv ℝ (fun w => (ε ^ finrank ℝ (CoulombConfig N))⁻¹ *
    ψ.normed volume (ε⁻¹ • w)) x = _ at hfd
  rw [he, hfd]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]
  ring

theorem dbarScaledBump_derivativeMoment {N : ℕ} (ψ : ContDiffBump (0 : CoulombConfig N))
    {ε : ℝ} (hε : 0 < ε) (v : CoulombConfig N) :
    dbarBumpDerivativeMoment (dbarScaledBump ψ hε) v = dbarBumpDerivativeMoment ψ v := by
  have hpow : 0 < ε ^ finrank ℝ (CoulombConfig N) := pow_pos hε _
  have he (x : CoulombConfig N) :
      ‖(fderiv ℝ ((dbarScaledBump ψ hε).normed volume) x) v‖ * ‖x‖ =
        (ε ^ finrank ℝ (CoulombConfig N))⁻¹ *
          (‖(fderiv ℝ (ψ.normed volume) (ε⁻¹ • x)) v‖ * ‖ε⁻¹ • x‖) := by
    rw [dbarScaledBump_fderiv_apply ψ hε]
    simp only [norm_mul, Real.norm_eq_abs, abs_inv, abs_of_pos hε, abs_of_pos hpow,
      norm_smul]
    ring
  unfold dbarBumpDerivativeMoment
  simp_rw [he]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg volume
    (fun x : CoulombConfig N => ‖(fderiv ℝ (ψ.normed volume) x) v‖ * ‖x‖) hε.le]
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hpow.ne', one_mul]

theorem dbarScaledBump_friedrichs_uniform_bound {N : ℕ} {A B : CoulombConfig N → ℂ}
    (hA : MemLp A ⊤ (volume : Measure (CoulombConfig N)))
    (hB : MemLp B ⊤ (volume : Measure (CoulombConfig N))) {C : ℝ≥0}
    (hLip : LipschitzWith C A) {M : ℝ} (hM : ∀ᵐ x ∂volume, ‖B x‖ ≤ M)
    (ψ : ContDiffBump (0 : CoulombConfig N)) (v : CoulombConfig N)
    {ε : ℝ} (hε : 0 < ε) (f : Lp ℂ 2 (volume : Measure (CoulombConfig N))) :
    ‖dbarVolumeFriedrichsKernel hA hB (dbarScaledBump ψ hε) v f‖ ≤
      ((C : ℝ) * dbarBumpDerivativeMoment ψ v + M) * ‖f‖ := by
  simpa only [dbarScaledBump_derivativeMoment] using
    dbarVolumeFriedrichsKernel_norm_le hA hB hLip hM (dbarScaledBump ψ hε) v f

end RepulsiveCoulomb
