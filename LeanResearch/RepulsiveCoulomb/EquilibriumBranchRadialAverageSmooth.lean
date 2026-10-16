import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Exact compact-convolution representation of the radial average and its
smoothness at every finite order. The average is J(x)=integral_0^1 s*rho(s*x)ds;
the thermal score uses 1-2*pi*J. A fixed smooth cutoff equals one on the
reflected integration interval [-1,0]. No square-root smoothness or extension
of a one-sided radial profile is used. -/
noncomputable section
open MeasureTheory Real Set Filter Metric ContinuousLinearMap
open scoped Topology Convolution
open scoped ENNReal
namespace RepulsiveCoulomb

def equilibriumRadialAverage (ρ : ℂ → ℝ) (x : ℂ) : ℝ :=
  ∫ s in (0 : ℝ)..1, s * ρ (s • x)

def equilibriumRadialAverageCutoff : ContDiffBump (0 : ℝ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

def equilibriumRadialAverageInterval : ℝ → ℝ := (Icc 0 1).indicator (fun _ => 1)

def equilibriumRadialAverageKernel (ρ : ℂ → ℝ) (x : ℂ) (s : ℝ) : ℝ :=
  equilibriumRadialAverageCutoff s * (-s) * ρ ((-s) • x)

theorem equilibriumRadialAverageCutoff_reflected {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    equilibriumRadialAverageCutoff (-s) = 1 := by
  apply equilibriumRadialAverageCutoff.one_of_mem_closedBall
  change dist (-s) (0 : ℝ) ≤ 2
  rw [dist_zero_right, Real.norm_eq_abs, abs_neg, abs_of_nonneg hs.1]
  linarith [hs.2]

theorem equilibriumRadialAverageInterval_integrable : Integrable equilibriumRadialAverageInterval := by
  apply (integrable_indicator_iff measurableSet_Icc).mpr
  exact (show Continuous (fun _ : ℝ => (1 : ℝ)) from continuous_const).integrableOn_Icc

/-- Exact equality with the actual convolution, including its fixed reflected
cutoff. This is the correspondence needed before using convolution smoothness. -/
theorem equilibriumRadialAverage_eq_convolution (ρ : ℂ → ℝ) (x : ℂ) :
    equilibriumRadialAverage ρ x =
      (equilibriumRadialAverageInterval ⋆[lsmul ℝ ℝ, volume]
        equilibriumRadialAverageKernel ρ x) 0 := by
  symm
  change (∫ s : ℝ, equilibriumRadialAverageInterval s *
      equilibriumRadialAverageKernel ρ x (0 - s)) = _
  have he : (fun s : ℝ => equilibriumRadialAverageInterval s *
      equilibriumRadialAverageKernel ρ x (0 - s)) =
      (Icc (0 : ℝ) 1).indicator (fun s => s * ρ (s • x)) := by
    funext s
    by_cases hs : s ∈ Icc (0 : ℝ) 1
    · simp only [equilibriumRadialAverageInterval, Set.indicator_of_mem hs,
        equilibriumRadialAverageKernel, zero_sub, neg_neg,
        equilibriumRadialAverageCutoff_reflected hs, one_mul]
    · simp only [equilibriumRadialAverageInterval, Set.indicator_of_notMem hs, zero_mul]
  rw [he, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  rfl

/-- The radial averaging operator preserves every C^n order. -/
theorem equilibriumRadialAverage_contDiff {n : ℕ∞} {ρ : ℂ → ℝ} (hρ : ContDiff ℝ n ρ) :
    ContDiff ℝ n (equilibriumRadialAverage ρ) := by
  have hg : ContDiff ℝ n (fun p : ℂ × ℝ => equilibriumRadialAverageKernel ρ p.1 p.2) := by
    exact ((equilibriumRadialAverageCutoff.contDiff.comp contDiff_snd).mul contDiff_snd.neg).mul
      (hρ.comp (contDiff_snd.neg.smul contDiff_fst))
  have hsupport : ∀ (x : ℂ) (s : ℝ), x ∈ (univ : Set ℂ) → s ∉ closedBall (0 : ℝ) 3 →
      equilibriumRadialAverageKernel ρ x s = 0 := by
    intro x s _ hs
    have hd : 3 < dist s (0 : ℝ) := by simpa only [Metric.mem_closedBall, not_le] using hs
    have hc : equilibriumRadialAverageCutoff s = 0 :=
      equilibriumRadialAverageCutoff.zero_of_le_dist hd.le
    simp only [equilibriumRadialAverageKernel, hc, zero_mul]
  have hc := contDiffOn_convolution_right_with_param_comp (lsmul ℝ ℝ)
    (v := fun _ : ℂ => (0 : ℝ)) (f := equilibriumRadialAverageInterval)
    (g := equilibriumRadialAverageKernel ρ) (s := univ) (k := closedBall (0 : ℝ) 3)
    contDiffOn_const isOpen_univ (isCompact_closedBall _ _) hsupport
    equilibriumRadialAverageInterval_integrable.locallyIntegrable hg.contDiffOn
  rw [contDiffOn_univ] at hc
  have he : equilibriumRadialAverage ρ =
      (fun x : ℂ => (equilibriumRadialAverageInterval ⋆[lsmul ℝ ℝ, volume]
        equilibriumRadialAverageKernel ρ x) 0) := funext (equilibriumRadialAverage_eq_convolution ρ)
  rw [he]
  exact hc

end RepulsiveCoulomb
