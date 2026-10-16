import LeanResearch.RepulsiveCoulomb.PointWeightedRegionArea

/-! A genuine weighted isoperimetric upper bound for a bounded region whose
frontier is covered by one C1 path. Uniform in all point configurations of bounded
total exponent. This is not yet the localized relative separator inequality. -/
noncomputable section
open Set MeasureTheory Metric
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb

theorem rawPointPathLength_mono_interval {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {γ : ℝ → ℂ}
    (hγ : ContDiff ℝ 1 γ) {s t u v : ℝ} (hst : s ≤ t) (huv : u ≤ v)
    (hus : u ≤ s) (htv : t ≤ v) :
    rawPointPathLength a y γ s t ≤ rawPointPathLength a y γ u v := by
  have h := pointConformalPathELength_mono (fun j => 2 * a j) y γ hus htv
  rw [pointDoublePathELength_eq_rawPointPathLength ha y hγ hst,
    pointDoublePathELength_eq_rawPointPathLength ha y hγ huv] at h
  exact (ENNReal.ofReal_le_ofReal_iff (rawPointPathLength_nonneg a y γ huv)).mp h

theorem pointSquaredRegionArea_le_boundaryLength_sq {m : ℕ} {Q : ℝ}
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q)
    (y : Fin m → ℂ) {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    {s t : ℝ} (hst : s ≤ t) {U : Set ℂ} (hU : Bornology.IsBounded U)
    (hfront : frontier U ⊆ γ '' Icc s t) :
    (rawPointMeasure (fun j => 2 * a j) y).real U ≤
      Real.pi * Real.exp (8 * Q) * rawPointPathLength a y γ s t ^ 2 := by
  obtain ⟨v, hv, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hst)
    ((hγ.continuous.sub continuous_const).norm.continuousOn)
  have hf : frontier U ⊆ closedBall (γ s) ‖γ v - γ s‖ := by
    intro z hz
    obtain ⟨r, hr, rfl⟩ := hfront hz
    rw [mem_closedBall, dist_eq_norm]
    exact hmax hr
  have hb := pointSquaredRegionArea_le_rawPointPathLength_sq ha hQ y hγ hv.1 hU hf
  have hl := rawPointPathLength_mono_interval ha y hγ hv.1 hst le_rfl hv.2
  have hn := rawPointPathLength_nonneg a y γ hv.1
  have hs : rawPointPathLength a y γ s v ^ 2 ≤ rawPointPathLength a y γ s t ^ 2 := by
    nlinarith
  exact hb.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end RepulsiveCoulomb
