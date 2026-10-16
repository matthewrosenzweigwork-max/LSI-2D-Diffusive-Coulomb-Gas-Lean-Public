import LeanResearch.RepulsiveCoulomb.DyadicScoreIntegralSums

/-! Actual finite dyadic coverage outside the fixed core. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb
attribute [local instance] Classical.propDecidable

def scoreRadialAnnulus (R : ℝ) : Set ℂ := {x | R ≤ ‖x‖ ∧ ‖x‖ < 2 * R}

theorem scoreRadialAnnulus_measurable (R : ℝ) : MeasurableSet (scoreRadialAnnulus R) :=
  (measurableSet_le measurable_const continuous_norm.measurable).inter
    (isOpen_lt continuous_norm continuous_const).measurableSet

theorem scoreRadialAnnulus_subset_enlarged {R : ℝ} (hR : 0 < R) :
    scoreRadialAnnulus R ⊆ enlargedScoreAnnulus R := by
  intro x hx
  exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem dyadicScoreAnnuli_cover {R : ℝ} (hR : 0 < R) {N : ℕ} {x : ℂ}
    (hx : R ≤ ‖x‖) (hN : ‖x‖ < dyadicScoreRadius R N) :
    ∃ k < N, x ∈ scoreRadialAnnulus (dyadicScoreRadius R k) := by
  obtain ⟨k, hk, hk'⟩ := exists_nat_pow_near ((le_div_iff₀ hR).mpr (by simpa using hx))
    (by norm_num : (1 : ℝ) < 2)
  have hlo : (2 : ℝ) ^ k * R ≤ ‖x‖ := (le_div_iff₀ hR).mp hk
  have hup : ‖x‖ < 2 * ((2 : ℝ) ^ k * R) := by
    have ht := (div_lt_iff₀ hR).mp hk'
    rw [pow_succ] at ht
    nlinarith
  have hkN : k < N := by
    by_contra hn
    have hp : (2 : ℝ) ^ N ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) (by omega)
    have hm := mul_le_mul_of_nonneg_right hp hR.le
    dsimp [dyadicScoreRadius] at hN
    linarith
  exact ⟨k, hkN, hlo, hup⟩

theorem dyadicScoreAnnuli_moment_pointwise {R : ℝ} (hR : 0 < R) (N : ℕ)
    (f : ℂ → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hN : ∀ x, f x ≠ 0 → ‖x‖ < dyadicScoreRadius R N) (x : ℂ) :
    ‖x‖ ^ 2 * f x ≤ R ^ 2 * f x + 4 *
      ∑ k ∈ Finset.range N, (dyadicScoreRadius R k) ^ 2 *
        (scoreRadialAnnulus (dyadicScoreRadius R k)).indicator f x := by
  have hsum : 0 ≤ ∑ k ∈ Finset.range N, (dyadicScoreRadius R k) ^ 2 *
      (scoreRadialAnnulus (dyadicScoreRadius R k)).indicator f x := by
    apply Finset.sum_nonneg
    intro k hk
    exact mul_nonneg (sq_nonneg _) (Set.indicator_nonneg (fun y _ => hf y) _)
  by_cases hf0 : f x = 0
  · simp [hf0, Set.indicator_apply]
  by_cases hx : ‖x‖ < R
  · have hs := mul_self_le_mul_self (norm_nonneg x) hx.le
    have hm := mul_le_mul_of_nonneg_right hs (hf x)
    nlinarith
  · obtain ⟨k, hk, hxk⟩ := dyadicScoreAnnuli_cover hR (le_of_not_gt hx) (hN x hf0)
    have ht := Finset.single_le_sum (f := fun j => (dyadicScoreRadius R j) ^ 2 *
      (scoreRadialAnnulus (dyadicScoreRadius R j)).indicator f x) (fun j (_hj : j ∈ Finset.range N) =>
      mul_nonneg (sq_nonneg (dyadicScoreRadius R j))
        (Set.indicator_nonneg (fun y _ => hf y) x)) (Finset.mem_range.mpr hk)
    rw [Set.indicator_of_mem hxk] at ht
    have hs := mul_self_le_mul_self (norm_nonneg x) hxk.2.le
    have hm := mul_le_mul_of_nonneg_right hs (hf x)
    have hr : 0 ≤ R ^ 2 * f x := mul_nonneg (sq_nonneg R) (hf x)
    nlinarith

set_option backward.isDefEq.respectTransparency false in
theorem dyadicScoreAnnuli_moment_integral {R : ℝ} (hR : 0 < R) (N : ℕ)
    {f : ℂ → ℝ} (hf : Integrable f) (hn : ∀ x, 0 ≤ f x)
    (hw : Integrable (fun x => ‖x‖ ^ 2 * f x))
    (hN : ∀ x, f x ≠ 0 → ‖x‖ < dyadicScoreRadius R N) :
    (∫ x, ‖x‖ ^ 2 * f x) ≤ R ^ 2 * (∫ x, f x) + 4 *
      ∑ k ∈ Finset.range N, (dyadicScoreRadius R k) ^ 2 *
        (∫ x in scoreRadialAnnulus (dyadicScoreRadius R k), f x) := by
  let g : ℕ → ℂ → ℝ := fun k x => (dyadicScoreRadius R k) ^ 2 *
    (scoreRadialAnnulus (dyadicScoreRadius R k)).indicator f x
  have hi (k : ℕ) : Integrable (g k) :=
    (hf.indicator (scoreRadialAnnulus_measurable _)).const_mul _
  have hs := integrable_finsetSum (Finset.range N) (fun k _ => hi k)
  calc
    _ ≤ ∫ x, R ^ 2 * f x + 4 * ∑ k ∈ Finset.range N, g k x := by
      apply integral_mono hw
        (by convert! (hf.const_mul (R ^ 2)).add (hs.const_mul 4) using 1)
      exact dyadicScoreAnnuli_moment_pointwise hR N f hn hN
    _ = _ := by
      rw [integral_add (hf.const_mul (R ^ 2)) (hs.const_mul 4), integral_const_mul,
        integral_const_mul, integral_finsetSum (Finset.range N) (fun k _ => hi k)]
      simp only [g, integral_const_mul, integral_indicator (scoreRadialAnnulus_measurable _)]

end RepulsiveCoulomb
