module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExponentialLayercake
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

@[expose] public section

/-! Actual improper integrals and constant algebra for exponential layer cake.
The N-dependent truncated exponential is controlled by the exact log-N cutoff;
no uniform partition estimate is assumed by these integral lemmas. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibrium_lintegral_exp_Iic (d : ℝ) :
    (∫⁻ s : ℝ in Iic d, ENNReal.ofReal (Real.exp s)) = ENNReal.ofReal (Real.exp d) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_Iic d)
    (Eventually.of_forall (fun s => (Real.exp_pos s).le)), integral_exp_Iic]

/-- The truncation may be empty when d<0; this bound remains valid without a
hidden positive-length interval assumption. -/
theorem equilibrium_lintegral_truncated_exp_le (d : ℝ) :
    (∫⁻ s : ℝ in Ioi 0, (Iic d).indicator (fun s => ENNReal.ofReal (Real.exp s)) s) ≤
      ENNReal.ofReal (Real.exp d) := by
  have h := setLIntegral_le_lintegral (μ := (volume : Measure ℝ)) (Ioi 0)
    ((Iic d).indicator (fun s => ENNReal.ofReal (Real.exp s)))
  have he : (∫⁻ s : ℝ, (Iic d).indicator (fun s => ENNReal.ofReal (Real.exp s)) s) =
      ENNReal.ofReal (Real.exp d) := by
    rw [lintegral_indicator measurableSet_Iic, equilibrium_lintegral_exp_Iic]
  exact h.trans_eq he

/-- The decaying term has its actual half-line integral, with q>1 exactly. -/
theorem equilibrium_lintegral_exp_decay {q : ℝ} (hq : 1 < q) :
    (∫⁻ s : ℝ in Ioi 0, ENNReal.ofReal (Real.exp ((1 - q) * s))) =
      ENNReal.ofReal (1 / (q - 1)) := by
  have ha : 1 - q < 0 := by linarith
  rw [← ofReal_integral_eq_lintegral_ofReal (integrableOn_exp_mul_Ioi ha 0)
    (Eventually.of_forall (fun s => (Real.exp_pos _).le)), integral_exp_mul_Ioi ha 0]
  simp only [mul_zero, Real.exp_zero]
  congr 1
  rw [show 1 - q = -(q - 1) by ring]
  simp only [neg_div_neg_eq, one_div]

/-- N^-r cancels the exponential of a*log N whenever r>=a, uniformly for N>=1. -/
theorem equilibrium_log_cutoff_power_cancellation {n a r b : ℝ} (hn : 1 ≤ n) (har : a ≤ r) :
    n ^ (-r) * Real.exp (a * Real.log n + b) ≤ Real.exp b := by
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hlog : 0 ≤ Real.log n := Real.log_nonneg hn
  have he : (-r) * Real.log n + (a * Real.log n + b) ≤ b := by
    nlinarith [mul_nonneg (sub_nonneg.mpr har) hlog]
  rw [Real.rpow_def_of_pos hn0, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith

/-- Constant algebra after the two actual layer-cake integrals. -/
theorem equilibrium_nelson_integrated_constant {n a r b q C : ℝ}
    (hn : 1 ≤ n) (har : a ≤ r) (hq : 1 < q) (hC : 0 ≤ C) :
    Real.exp 1 * (1 + C *
      (n ^ (-r) * Real.exp (a * Real.log n + b - 1) + Real.exp (-q) / (q - 1))) ≤
      Real.exp 1 + C * Real.exp b + C / (q - 1) := by
  have hfirst : Real.exp 1 * (n ^ (-r) * Real.exp (a * Real.log n + b - 1)) ≤ Real.exp b := by
    have he : Real.exp 1 * (n ^ (-r) * Real.exp (a * Real.log n + b - 1)) =
        n ^ (-r) * Real.exp (a * Real.log n + b) := by
      rw [mul_left_comm, ← Real.exp_add]
      congr 2
      ring
    rw [he]
    exact equilibrium_log_cutoff_power_cancellation hn har
  have hsecond : Real.exp 1 * (Real.exp (-q) / (q - 1)) ≤ 1 / (q - 1) := by
    have he : Real.exp 1 * Real.exp (-q) ≤ 1 := by
      rw [← Real.exp_add]
      exact Real.exp_le_one_iff.mpr (by linarith)
    have h := div_le_div_of_nonneg_right he (by linarith : 0 ≤ q - 1)
    simpa only [mul_div_assoc] using h
  have h1 := mul_le_mul_of_nonneg_left hfirst hC
  have h2 := mul_le_mul_of_nonneg_left hsecond hC
  calc
    _ = Real.exp 1 + C * (Real.exp 1 * (n ^ (-r) * Real.exp (a * Real.log n + b - 1))) +
        C * (Real.exp 1 * (Real.exp (-q) / (q - 1))) := by ring
    _ ≤ Real.exp 1 + C * Real.exp b + C * (1 / (q - 1)) :=
      add_le_add (add_le_add le_rfl h1) h2
    _ = _ := by ring

end RepulsiveCoulomb
