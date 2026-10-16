module

public import LeanResearch.RepulsiveCoulomb.DyadicScoreAnnuli

@[expose] public section

/-! Finite integral overlap bounds. Integrability is explicit at every
real-valued integral comparison. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb
attribute [local instance] Classical.propDecidable

theorem dyadicScoreAnnuli_indicator_sum_le {R : ℝ} (hR : 0 < R)
    (s : Finset ℕ) (f : ℂ → ℝ) (hf : ∀ x, 0 ≤ f x) (x : ℂ) :
    ∑ k ∈ s, (enlargedScoreAnnulus (dyadicScoreRadius R k)).indicator f x ≤ 3 * f x := by
  simp only [Set.indicator_apply]
  rw [← Finset.sum_filter]
  simp only [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast dyadicScoreAnnuli_card_le_three hR s x) (hf x)

theorem dyadicScoreAnnuli_weighted_indicator_sum_le {R : ℝ} (hR : 0 < R)
    (s : Finset ℕ) (f : ℂ → ℝ) (hf : ∀ x, 0 ≤ f x) (x : ℂ) :
    ∑ k ∈ s, (dyadicScoreRadius R k) ^ 2 *
      (enlargedScoreAnnulus (dyadicScoreRadius R k)).indicator f x ≤ 12 * ‖x‖ ^ 2 * f x := by
  have he : (∑ k ∈ s, (dyadicScoreRadius R k) ^ 2 *
      (enlargedScoreAnnulus (dyadicScoreRadius R k)).indicator f x) =
      (∑ k ∈ s.filter (fun k => x ∈ enlargedScoreAnnulus (dyadicScoreRadius R k)),
        (dyadicScoreRadius R k) ^ 2) * f x := by
    rw [Finset.sum_mul, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hx : x ∈ enlargedScoreAnnulus (dyadicScoreRadius R k) <;> simp [hx]
  rw [he]
  exact mul_le_mul_of_nonneg_right (dyadicScoreAnnuli_radius_sq_sum_le hR s x) (hf x)

theorem dyadicScoreAnnuli_integral_sum_le {R : ℝ} (hR : 0 < R)
    (s : Finset ℕ) {f : ℂ → ℝ} (hf : Integrable f) (hn : ∀ x, 0 ≤ f x) :
    (∑ k ∈ s, ∫ x in enlargedScoreAnnulus (dyadicScoreRadius R k), f x) ≤ 3 * ∫ x, f x := by
  have hi (k : ℕ) : Integrable ((enlargedScoreAnnulus (dyadicScoreRadius R k)).indicator f) :=
    hf.indicator (enlargedScoreAnnulus_measurable _)
  calc
    _ = ∫ x, ∑ k ∈ s, (enlargedScoreAnnulus (dyadicScoreRadius R k)).indicator f x := by
      rw [integral_finsetSum s (fun k _ => hi k)]
      simp only [integral_indicator (enlargedScoreAnnulus_measurable _)]
    _ ≤ ∫ x, 3 * f x := integral_mono (integrable_finsetSum s (fun k _ => hi k))
      (hf.const_mul 3) (dyadicScoreAnnuli_indicator_sum_le hR s f hn)
    _ = _ := integral_const_mul 3 f

theorem dyadicScoreAnnuli_weighted_integral_sum_le {R : ℝ} (hR : 0 < R)
    (s : Finset ℕ) {f : ℂ → ℝ} (hf : Integrable f) (hn : ∀ x, 0 ≤ f x)
    (hw : Integrable (fun x => ‖x‖ ^ 2 * f x)) :
    (∑ k ∈ s, (dyadicScoreRadius R k) ^ 2 *
      ∫ x in enlargedScoreAnnulus (dyadicScoreRadius R k), f x) ≤
        12 * ∫ x, ‖x‖ ^ 2 * f x := by
  have hi (k : ℕ) : Integrable (fun x => (dyadicScoreRadius R k) ^ 2 *
      (enlargedScoreAnnulus (dyadicScoreRadius R k)).indicator f x) :=
    (hf.indicator (enlargedScoreAnnulus_measurable _)).const_mul _
  calc
    _ = ∫ x, ∑ k ∈ s, (dyadicScoreRadius R k) ^ 2 *
        (enlargedScoreAnnulus (dyadicScoreRadius R k)).indicator f x := by
      rw [integral_finsetSum s (fun k _ => hi k)]
      simp only [integral_const_mul, integral_indicator (enlargedScoreAnnulus_measurable _)]
    _ ≤ ∫ x, 12 * (‖x‖ ^ 2 * f x) := integral_mono
      (integrable_finsetSum s (fun k _ => hi k)) (hw.const_mul 12)
      (fun x => by simpa only [mul_assoc] using dyadicScoreAnnuli_weighted_indicator_sum_le hR s f hn x)
    _ = _ := integral_const_mul 12 _

end RepulsiveCoulomb
