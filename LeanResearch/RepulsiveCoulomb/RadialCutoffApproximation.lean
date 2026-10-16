module

public import LeanResearch.RepulsiveCoulomb.RadialPrimitive
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.SpecificLimits.Basic

@[expose] public section

/-! Smooth radial masks shrink to the origin and recover the integral of every
continuous nonnegative radial density by dominated convergence. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology
namespace RepulsiveCoulomb

def radialMaskBump (n : ℕ) : ContDiffBump (0 : ℝ) :=
  ⟨1 / (n + 1 : ℝ), 2 / (n + 1 : ℝ), by positivity, by
    apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩

def radialMask (n : ℕ) (t : ℝ) : ℝ := 1 - radialMaskBump n t

theorem radialMask_bounds (n : ℕ) (t : ℝ) : 0 ≤ radialMask n t ∧ radialMask n t ≤ 1 := by
  have h0 := (radialMaskBump n).nonneg (x := t)
  have h1 := (radialMaskBump n).le_one (x := t)
  dsimp [radialMask]
  constructor <;> linarith

theorem radialMask_continuous (n : ℕ) : Continuous (radialMask n) :=
  continuous_const.sub (radialMaskBump n).continuous

theorem radialMask_zero (n : ℕ) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) (1 / (n + 1 : ℝ))) :
    radialMask n t = 0 := by
  unfold radialMask
  rw [(radialMaskBump n).one_of_mem_closedBall]
  · ring
  · simpa only [radialMaskBump, mem_closedBall, dist_zero_right, Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2

theorem radialMask_eventually_one {t : ℝ} (ht : 0 < t) :
    ∀ᶠ n : ℕ in atTop, radialMask n t = 1 := by
  have hlim : Tendsto (fun n : ℕ => 2 / (n + 1 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  filter_upwards [hlim.eventually (gt_mem_nhds ht)] with n hn
  unfold radialMask
  rw [(radialMaskBump n).zero_of_le_dist]
  · ring
  · simpa only [radialMaskBump, dist_zero_right, Real.norm_eq_abs, abs_of_pos ht] using hn.le

theorem radialMask_integral_tendsto (h : ℝ → ℝ) (hc : Continuous h) (hn : ∀ t, 0 ≤ h t)
    {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun n : ℕ => ∫ t in (0 : ℝ)..r, radialMask n t * h t) atTop
      (𝓝 (∫ t in (0 : ℝ)..r, h t)) := by
  simp only [intervalIntegral.integral_of_le hr]
  apply tendsto_integral_of_dominated_convergence h
  · intro n
    exact ((radialMask_continuous n).mul hc).aestronglyMeasurable
  · exact (hc.intervalIntegrable 0 r).1
  · intro n
    filter_upwards [] with t
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (radialMask_bounds n t).1 (hn t))]
    exact mul_le_of_le_one_left (hn t) (radialMask_bounds n t).2
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    apply tendsto_const_nhds.congr'
    filter_upwards [radialMask_eventually_one ht.1] with n hn
    rw [hn, one_mul]

end RepulsiveCoulomb
