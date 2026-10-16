module

public import LeanResearch.RepulsiveCoulomb.DyadicMomentBound
public import LeanResearch.RepulsiveCoulomb.DyadicTruncationEnergy
public import LeanResearch.RepulsiveCoulomb.SmoothTruncationMean

@[expose] public section

/-! Actual smooth-truncation upgrade of a uniform mean-centered weak estimate
for all C1 observables. Half support controls the means of the truncations;
all dyadic gradient energies are summed on disjoint value bands. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem smooth_truncation_superlevel_bound (μ ν : Measure ℂ) [IsFiniteMeasure μ] [NeZero μ]
    {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u)
    (hhalf : μ.real {x | 0 < u x} ≤ μ.real univ / 2)
    {q κ : ℝ} {W : ℝ≥0∞}
    (hweak : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ q) * μ {x | t < ‖v x - (⨍ z, v z ∂μ)‖} ≤
        W * (∫⁻ x, ENNReal.ofReal (‖gradient v x‖ ^ 2) ∂ν) ^ κ)
    {a : ℝ} (ha : 0 < a) :
    ENNReal.ofReal ((4 * a) ^ q) * μ {x | 2 * a ≤ u x} ≤
      ENNReal.ofReal ((16 : ℝ) ^ q) * W *
        (∫⁻ x, ENNReal.ofReal (‖gradient (fun z => smoothDyadicTruncation a (u z)) x‖ ^ 2) ∂ν) ^ κ := by
  have h := hweak (fun z => smoothDyadicTruncation a (u z))
    (smoothTruncation_comp_contDiff a hu) (a / 4) (by positivity)
  have hs := smoothTruncation_plateau_subset_centered_level μ hu.continuous.measurable hhalf ha
  have he : ENNReal.ofReal ((4 * a) ^ q) =
      ENNReal.ofReal ((16 : ℝ) ^ q) * ENNReal.ofReal ((a / 4) ^ q) := by
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _),
      ← Real.mul_rpow (by norm_num) (by positivity)]
    congr 2
    ring
  rw [he, mul_assoc]
  calc
    _ ≤ ENNReal.ofReal ((16 : ℝ) ^ q) *
        (ENNReal.ofReal ((a / 4) ^ q) * μ {x | a / 4 <
          ‖smoothDyadicTruncation a (u x) - (⨍ z, smoothDyadicTruncation a (u z) ∂μ)‖}) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (measure_mono hs))
    _ ≤ _ := by simpa only [mul_assoc] using mul_le_mul' (le_refl (ENNReal.ofReal ((16 : ℝ) ^ q))) h

theorem smooth_weak_to_strong_positive (μ ν : Measure ℂ) [IsFiniteMeasure μ] [NeZero μ]
    {u : ℂ → ℝ} (hu : ContDiff ℝ 1 u)
    (hhalf : μ.real {x | 0 < u x} ≤ μ.real univ / 2)
    {q κ K : ℝ} {W : ℝ≥0∞} (hq : 0 < q) (hκ : 1 ≤ κ) (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, ‖deriv Real.smoothTransition t‖ ≤ K)
    (hweak : ∀ v : ℂ → ℝ, ContDiff ℝ 1 v → ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ q) * μ {x | t < ‖v x - (⨍ z, v z ∂μ)‖} ≤
        W * (∫⁻ x, ENNReal.ofReal (‖gradient v x‖ ^ 2) ∂ν) ^ κ) :
    (∫⁻ x, ENNReal.ofReal ((max (u x) 0) ^ q) ∂μ) ≤
      ENNReal.ofReal ((16 : ℝ) ^ q) * W *
        (ENNReal.ofReal (K ^ 2) * ∫⁻ x, ENNReal.ofReal (‖gradient u x‖ ^ 2) ∂ν) ^ κ := by
  apply (positive_moment_le_dyadic_levels μ hu.continuous.measurable hq).trans
  calc
    _ ≤ ∑' j : ℤ, ENNReal.ofReal ((16 : ℝ) ^ q) * W *
        (∫⁻ x, ENNReal.ofReal (‖gradient (fun z => smoothDyadicTruncation ((2 : ℝ) ^ j) (u z)) x‖ ^ 2) ∂ν) ^ κ :=
      ENNReal.tsum_le_tsum (fun j => smooth_truncation_superlevel_bound μ ν hu hhalf hweak (zpow_pos (by norm_num) _))
    _ = (ENNReal.ofReal ((16 : ℝ) ^ q) * W) * ∑' j : ℤ,
        (∫⁻ x, ENNReal.ofReal (‖gradient (fun z => smoothDyadicTruncation ((2 : ℝ) ^ j) (u z)) x‖ ^ 2) ∂ν) ^ κ :=
      ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl (tsum_rpow_le_of_tsum_le hκ (dyadic_truncation_energy_sum hK0 hK hu ν))

end RepulsiveCoulomb
