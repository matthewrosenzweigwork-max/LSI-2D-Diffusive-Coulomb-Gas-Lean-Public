import LeanResearch.RepulsiveCoulomb.PaperRoute.LogFundamentalSolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! The literal logarithmic potential of a smooth compact source.
All row integrals are genuinely integrable. The physical Poisson equation is
proved from the new test-function fundamental solution by convolution calculus. -/
noncomputable section
open MeasureTheory InnerProductSpace Filter Set
open scoped Topology ContDiff Convolution
namespace RepulsiveCoulomb.PaperRoute

def planarLogKernel (z : ℂ) : ℝ := -Real.log ‖z‖

theorem planarLogKernel_split (z : ℂ) :
    planarLogKernel z = max (-Real.log ‖z‖) 0 - Real.log (max 1 ‖z‖) := by
  unfold planarLogKernel
  by_cases hz : ‖z‖ ≤ 1
  · rw [max_eq_left hz, Real.log_one, sub_zero,
      max_eq_left (neg_nonneg.mpr (Real.log_nonpos (norm_nonneg z) hz))]
  · have hn : 0 ≤ Real.log ‖z‖ := Real.log_nonneg (le_of_not_ge hz)
    rw [max_eq_right (le_of_not_ge hz), max_eq_right (neg_nonpos.mpr hn), zero_sub]

theorem planarLogKernel_locallyIntegrable : LocallyIntegrable planarLogKernel volume := by
  have hc : Continuous (fun z : ℂ => Real.log (max 1 ‖z‖)) :=
    (continuous_const.max continuous_norm).log (fun z => ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
  have hi := logPositive_integrable.locallyIntegrable.sub hc.locallyIntegrable
  have he : planarLogKernel = (fun z : ℂ => max (-Real.log ‖z‖) 0) -
      (fun z : ℂ => Real.log (max 1 ‖z‖)) := funext planarLogKernel_split
  rw [he]
  exact hi

def smoothLogPotential (η : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ y, planarLogKernel y * η (x - y)

theorem smoothLogPotential_eq_convolution (η : ℂ → ℝ) :
    smoothLogPotential η = planarLogKernel ⋆[ContinuousLinearMap.mul ℝ ℝ] η := rfl

theorem smoothLogPotential_integrable {η : ℂ → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) (x : ℂ) :
    Integrable (fun y => planarLogKernel y * η (x - y)) :=
  hηc.convolutionExists_right (ContinuousLinearMap.mul ℝ ℝ) planarLogKernel_locallyIntegrable hη x

theorem smoothLogPotential_integrable_swap {η : ℂ → ℝ} (hη : Continuous η)
    (hηc : HasCompactSupport η) (x : ℂ) :
    Integrable (fun y => planarLogKernel (x - y) * η y) := by
  simpa only [sub_sub_self] using (smoothLogPotential_integrable hη hηc x).comp_sub_left x

theorem smoothLogPotential_eq_swap (η : ℂ → ℝ) (x : ℂ) :
    smoothLogPotential η x = ∫ y, planarLogKernel (x - y) * η y :=
  convolution_eq_swap (ContinuousLinearMap.mul ℝ ℝ)

theorem smoothLogPotential_contDiff {n : ℕ∞} {η : ℂ → ℝ}
    (hη : ContDiff ℝ n η) (hηc : HasCompactSupport η) :
    ContDiff ℝ n (smoothLogPotential η) :=
  hηc.contDiff_convolution_right (ContinuousLinearMap.mul ℝ ℝ) planarLogKernel_locallyIntegrable hη

/-- The actual Fréchet derivative, written as a Bochner integral of linear maps. -/
theorem smoothLogPotential_hasFDerivAt {η : ℂ → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (x : ℂ) :
    HasFDerivAt (smoothLogPotential η)
      (∫ y, planarLogKernel y • fderiv ℝ η (x - y)) x := by
  have h := hηc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    planarLogKernel_locallyIntegrable hη x
  convert! h using 1

/-- Directional form of the actual differentiated convolution. -/
theorem smoothLogPotential_fderiv {η : ℂ → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (x v : ℂ) :
    fderiv ℝ (smoothLogPotential η) x v =
      ∫ y, planarLogKernel y * fderiv ℝ η (x - y) v := by
  have h := hηc.hasFDerivAt_convolution_right (ContinuousLinearMap.mul ℝ ℝ)
    planarLogKernel_locallyIntegrable hη x
  rw [show fderiv ℝ (smoothLogPotential η) x = _ from h.fderiv]
  exact convolution_precompR_apply (ContinuousLinearMap.mul ℝ ℝ)
    planarLogKernel_locallyIntegrable (hηc.fderiv ℝ) (hη.continuous_fderiv one_ne_zero) x v

/-- Genuine integrability of the derivative-valued row used above. -/
theorem smoothLogPotential_fderiv_integrable {η : ℂ → ℝ}
    (hη : ContDiff ℝ 1 η) (hηc : HasCompactSupport η) (x : ℂ) :
    Integrable (fun y => planarLogKernel y • fderiv ℝ η (x - y)) := by
  have hi := (hηc.fderiv ℝ).convolutionExists_right
    ((ContinuousLinearMap.mul ℝ ℝ).precompR ℂ) planarLogKernel_locallyIntegrable
    (hη.continuous_fderiv one_ne_zero) x
  convert! hi using 1

theorem smoothLogPotential_second_fderiv {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (x v w : ℂ) :
    fderiv ℝ (fun z => fderiv ℝ (smoothLogPotential η) z v) x w =
      ∫ y, planarLogKernel y * fderiv ℝ (fun z => fderiv ℝ η z v) (x - y) w := by
  have hη1 : ContDiff ℝ 1 η := hη.of_le (by norm_num)
  have hd : ContDiff ℝ 1 (fun z => fderiv ℝ η z v) :=
    (hη.fderiv_right (by norm_num)).clm_apply contDiff_const
  have he : (fun z => fderiv ℝ (smoothLogPotential η) z v) =
      smoothLogPotential (fun z => fderiv ℝ η z v) := by
    funext z
    exact smoothLogPotential_fderiv hη1 hηc z v
  rw [he]
  exact smoothLogPotential_fderiv hd (hηc.fderiv_apply ℝ v) x w

theorem smoothLogPotential_second_fderiv_integrable {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (x v w : ℂ) :
    Integrable (fun y => planarLogKernel y * fderiv ℝ (fun z => fderiv ℝ η z v) (x - y) w) := by
  have hd : ContDiff ℝ 1 (fun z => fderiv ℝ η z v) :=
    (hη.fderiv_right (by norm_num)).clm_apply contDiff_const
  have hc := (hd.continuous_fderiv one_ne_zero).clm_apply (continuous_const (y := w))
  exact smoothLogPotential_integrable hc ((hηc.fderiv_apply ℝ v).fderiv_apply ℝ w) x

/-- The physical Laplacian is the literal convolution with the source Laplacian. -/
theorem smoothLogPotential_laplacian_convolution {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (x : ℂ) :
    Laplacian.laplacian (smoothLogPotential η) x =
      ∫ y, planarLogKernel y * Laplacian.laplacian η (x - y) := by
  have hh : ContDiff ℝ 2 (smoothLogPotential η) := smoothLogPotential_contDiff (n := 2) hη hηc
  rw [laplacian_eq_second_fderiv hh]
  dsimp only
  rw [smoothLogPotential_second_fderiv hη hηc, smoothLogPotential_second_fderiv hη hηc]
  rw [← integral_add (smoothLogPotential_second_fderiv_integrable hη hηc x 1 1)
    (smoothLogPotential_second_fderiv_integrable hη hηc x Complex.I Complex.I)]
  congr 1
  funext y
  rw [laplacian_eq_second_fderiv hη]
  dsimp only
  ring

/-- Reflection contributes a minus sign to an actual first derivative. -/
theorem fderiv_comp_sub_left_apply {η : ℂ → ℝ} (hη : Differentiable ℝ η)
    (x y v : ℂ) :
    fderiv ℝ (fun z => η (x - z)) y v = -(fderiv ℝ η (x - y) v) := by
  have h := (hη (x - y)).hasFDerivAt.comp y
    ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
  have he := h.fderiv
  change fderiv ℝ (fun z => η (x - z)) y = _ at he
  rw [he]
  simp

/-- In the Hessian trace, the two reflection signs cancel. -/
theorem laplacian_comp_sub_left {η : ℂ → ℝ} (hη : ContDiff ℝ 2 η)
    (x y : ℂ) :
    Laplacian.laplacian (fun z => η (x - z)) y = Laplacian.laplacian η (x - y) := by
  have hcomp : ContDiff ℝ 2 (fun z => η (x - z)) :=
    hη.comp (contDiff_const.sub contDiff_id)
  have hd (v : ℂ) : ContDiff ℝ 1 (fun z => fderiv ℝ η z v) :=
    (hη.fderiv_right (by norm_num)).clm_apply contDiff_const
  have he (v : ℂ) : (fun z => fderiv ℝ (fun w => η (x - w)) z v) =
      (fun z => -(fderiv ℝ η (x - z) v)) := by
    funext z
    exact fderiv_comp_sub_left_apply (hη.differentiable (by norm_num)) x z v
  have hsecond (v : ℂ) :
      fderiv ℝ (fun z => fderiv ℝ (fun w => η (x - w)) z v) y v =
        fderiv ℝ (fun z => fderiv ℝ η z v) (x - y) v := by
    rw [he]
    change fderiv ℝ (-(fun z => fderiv ℝ η (x - z) v)) y v = _
    rw [fderiv_neg]
    simp only [neg_apply]
    rw [fderiv_comp_sub_left_apply ((hd v).differentiable one_ne_zero), neg_neg]
  rw [laplacian_eq_second_fderiv hcomp, laplacian_eq_second_fderiv hη]
  dsimp only
  rw [hsecond 1, hsecond Complex.I]

/-- Pointwise Poisson equation for the literal potential of a compact C2 source. -/
theorem smoothLogPotential_laplacian {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (x : ℂ) :
    Laplacian.laplacian (smoothLogPotential η) x = (-2 * Real.pi) * η x := by
  have htest : ContDiff ℝ 2 (fun y => η (x - y)) :=
    hη.comp (contDiff_const.sub contDiff_id)
  have htestc : HasCompactSupport (fun y => η (x - y)) :=
    hηc.comp_homeomorph (Homeomorph.subLeft x)
  have hid := (log_fundamental_solution htest htestc).2
  rw [smoothLogPotential_laplacian_convolution hη hηc]
  simpa only [laplacian_comp_sub_left hη, planarLogKernel, sub_zero] using hid

/-- The Hessian entries are the literal differentiated integrals. -/
theorem smoothLogPotential_iteratedFDeriv_two {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (x v w : ℂ) :
    iteratedFDeriv ℝ 2 (smoothLogPotential η) x ![w, v] =
      ∫ y, planarLogKernel y * iteratedFDeriv ℝ 2 η (x - y) ![w, v] := by
  rw [← second_fderiv_apply_eq_iterated (smoothLogPotential_contDiff (n := 2) hη hηc)]
  simpa only [second_fderiv_apply_eq_iterated hη] using smoothLogPotential_second_fderiv hη hηc x v w

theorem smoothLogPotential_laplacian_integrable {η : ℂ → ℝ}
    (hη : ContDiff ℝ 2 η) (hηc : HasCompactSupport η) (x : ℂ) :
    Integrable (fun y => planarLogKernel y * Laplacian.laplacian η (x - y)) :=
  smoothLogPotential_integrable (continuous_laplacian_of_contDiff_two hη)
    (hasCompactSupport_laplacian hη hηc) x

end RepulsiveCoulomb.PaperRoute
