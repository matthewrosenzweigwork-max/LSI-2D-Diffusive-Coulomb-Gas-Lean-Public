module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCircularRegularization
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Nonnegative continuous approximants to the genuinely extended logarithmic
interaction. The diagonal is +infinity, never the real-log default value zero.
These are exact kernel identities for the full P2 direct method. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

def equilibriumShiftedKernelApprox (n : ℕ) (p : ℂ × ℂ) : ℝ :=
  equilibriumCircularKernel (Real.exp (-(n : ℝ))) (p.1 - p.2) +
    equilibriumLogMoment p.1 + equilibriumLogMoment p.2

def equilibriumExtendedShiftedKernel (p : ℂ × ℂ) : ℝ≥0∞ :=
  ⨆ n : ℕ, ENNReal.ofReal (equilibriumShiftedKernelApprox n p)

theorem equilibriumShiftedKernelApprox_continuous (n : ℕ) :
    Continuous (equilibriumShiftedKernelApprox n) :=
  (((equilibriumCircularKernel_continuous (Real.exp_pos _)).comp
    (continuous_fst.sub continuous_snd)).add
    (equilibriumLogMoment_continuous.comp continuous_fst)).add
      (equilibriumLogMoment_continuous.comp continuous_snd)

theorem equilibriumShiftedKernelApprox_nonneg (n : ℕ) (p : ℂ × ℂ) :
    0 ≤ equilibriumShiftedKernelApprox n p := by
  have he : Real.exp (-(n : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Nat.cast_nonneg n))
  have hx := norm_nonneg p.1
  have hy := norm_nonneg p.2
  have hprod : 1 ≤ (1 + ‖p.1‖) * (1 + ‖p.2‖) := by nlinarith
  have hnorm : ‖p.1 - p.2‖ ≤ (1 + ‖p.1‖) * (1 + ‖p.2‖) := by
    nlinarith [norm_sub_le p.1 p.2]
  have hb : max (Real.exp (-(n : ℝ))) ‖p.1 - p.2‖ ≤
      (1 + ‖p.1‖) * (1 + ‖p.2‖) := max_le (he.trans hprod) hnorm
  have hp : 0 < max (Real.exp (-(n : ℝ))) ‖p.1 - p.2‖ :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  have hl := Real.log_le_log hp hb
  rw [Real.log_mul (by positivity : 1 + ‖p.1‖ ≠ 0)
    (by positivity : 1 + ‖p.2‖ ≠ 0)] at hl
  unfold equilibriumShiftedKernelApprox equilibriumCircularKernel equilibriumLogMoment
  linarith

theorem equilibriumShiftedKernelApprox_monotone (p : ℂ × ℂ) :
    Monotone (fun n : ℕ => equilibriumShiftedKernelApprox n p) := by
  intro n m hnm
  have hnm' : (n : ℝ) ≤ m := by exact_mod_cast hnm
  have he : Real.exp (-(m : ℝ)) ≤ Real.exp (-(n : ℝ)) :=
    Real.exp_le_exp.mpr (neg_le_neg hnm')
  have hp : 0 < max (Real.exp (-(m : ℝ))) ‖p.1 - p.2‖ :=
    (Real.exp_pos _).trans_le (le_max_left _ _)
  have hl := Real.log_le_log hp (max_le_max_right ‖p.1 - p.2‖ he)
  unfold equilibriumShiftedKernelApprox equilibriumCircularKernel
  linarith

/-- The extended kernel agrees with the literal shifted kernel away from the
spatial diagonal, regardless of any index labels. -/
theorem equilibriumExtendedShiftedKernel_off_diagonal {x y : ℂ} (hxy : x ≠ y) :
    equilibriumExtendedShiftedKernel (x, y) =
      ENNReal.ofReal (equilibriumLogKernel (x - y) + equilibriumLogMoment x + equilibriumLogMoment y) := by
  apply le_antisymm
  · apply iSup_le
    intro n
    apply ENNReal.ofReal_le_ofReal
    have h := equilibriumCircularKernel_le_logKernel (Real.exp_pos (-(n : ℝ)))
      (sub_ne_zero.mpr hxy)
    unfold equilibriumShiftedKernelApprox
    linarith
  · have hn : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
    obtain ⟨n, hng⟩ := exists_nat_ge (-Real.log ‖x - y‖)
    have he : Real.exp (-(n : ℝ)) ≤ ‖x - y‖ := by
      have h := Real.exp_le_exp.mpr (show -(n : ℝ) ≤ Real.log ‖x - y‖ by linarith)
      simpa only [Real.exp_log hn] using h
    have hid : equilibriumShiftedKernelApprox n (x, y) =
        equilibriumLogKernel (x - y) + equilibriumLogMoment x + equilibriumLogMoment y := by
      simp only [equilibriumShiftedKernelApprox, equilibriumCircularKernel,
        max_eq_right he, equilibriumLogKernel]
    rw [← hid]
    exact le_iSup (fun m : ℕ => ENNReal.ofReal (equilibriumShiftedKernelApprox m (x, y))) n

/-- The required singular diagonal value is genuinely infinity. -/
theorem equilibriumExtendedShiftedKernel_diagonal (x : ℂ) :
    equilibriumExtendedShiftedKernel (x, x) = ∞ := by
  apply top_unique
  rw [← ENNReal.iSup_natCast]
  apply iSup_le
  intro n
  have hid : equilibriumShiftedKernelApprox n (x, x) = (n : ℝ) + 2 * equilibriumLogMoment x := by
    simp only [equilibriumShiftedKernelApprox, sub_self, norm_zero, equilibriumCircularKernel,
      max_eq_left (Real.exp_pos _).le, Real.log_exp, neg_neg]
    ring
  have hl : (n : ℝ≥0∞) ≤ ENNReal.ofReal (equilibriumShiftedKernelApprox n (x, x)) := by
    rw [hid]
    have h : (n : ℝ) ≤ (n : ℝ) + 2 * equilibriumLogMoment x := by
      linarith [equilibriumLogMoment_nonneg x]
    simpa only [ENNReal.ofReal_natCast] using ENNReal.ofReal_le_ofReal h
  exact hl.trans (le_iSup (fun m : ℕ => ENNReal.ofReal (equilibriumShiftedKernelApprox m (x, x))) n)

theorem equilibriumExtendedShiftedKernel_measurable : Measurable equilibriumExtendedShiftedKernel :=
  Measurable.iSup (fun n => (equilibriumShiftedKernelApprox_continuous n).measurable.ennreal_ofReal)

end RepulsiveCoulomb
