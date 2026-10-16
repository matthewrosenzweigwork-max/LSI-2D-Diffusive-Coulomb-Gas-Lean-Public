import LeanResearch.RepulsiveCoulomb.MetricIntervalGeodesicReplacement

/-! Same-side parameter pairs follow from the two radial legs and the triangle
inequality. Only pairs straddling the center require a geometric passage test. -/
noncomputable section
open Set
namespace RepulsiveCoulomb
variable {X : Type*} [PseudoMetricSpace X]

theorem metric_interval_eq_of_center_and_cross_pairs (γ : unitInterval → X) (c : ℝ)
    (t₀ : unitInterval) (U : Set unitInterval)
    (hupper : ∀ s ∈ U, ∀ t ∈ U, dist (γ s) (γ t) ≤ c * |t.1 - s.1|)
    (hcenter : ∀ s ∈ U, dist (γ s) (γ t₀) = c * |t₀.1 - s.1|)
    (hcross : ∀ s ∈ U, ∀ t ∈ U, s ≤ t₀ → t₀ ≤ t →
      dist (γ s) (γ t) = c * (t.1 - s.1)) :
    ∀ s ∈ U, ∀ t ∈ U, dist (γ s) (γ t) = c * |t.1 - s.1| := by
  have hordered : ∀ s ∈ U, ∀ t ∈ U, s ≤ t → dist (γ s) (γ t) = c * (t.1 - s.1) := by
    intro s hs t ht hst
    have hu := hupper s hs t ht
    rw [abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from hst))] at hu
    apply le_antisymm hu
    by_cases ht₀ : t ≤ t₀
    · have htri := dist_triangle (γ s) (γ t) (γ t₀)
      rw [hcenter s hs, hcenter t ht,
        abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t₀.1 from hst.trans ht₀)),
        abs_of_nonneg (sub_nonneg.mpr (show t.1 ≤ t₀.1 from ht₀))] at htri
      linarith
    · by_cases h₀s : t₀ ≤ s
      · have htri := dist_triangle (γ t) (γ s) (γ t₀)
        rw [hcenter t ht, hcenter s hs, dist_comm (γ t) (γ s),
          abs_of_nonpos (sub_nonpos.mpr (show t₀.1 ≤ t.1 from h₀s.trans hst)),
          abs_of_nonpos (sub_nonpos.mpr (show t₀.1 ≤ s.1 from h₀s))] at htri
        linarith
      · exact (hcross s hs t ht (lt_of_not_ge h₀s).le (lt_of_not_ge ht₀).le).ge
  intro s hs t ht
  rcases le_total s t with hst | hts
  · rw [hordered s hs t ht hst,
      abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from hst))]
  · rw [dist_comm, hordered t ht s hs hts,
      abs_of_nonpos (sub_nonpos.mpr (show t.1 ≤ s.1 from hts)), neg_sub]

end RepulsiveCoulomb
