import LeanResearch.RepulsiveCoulomb.PointConformalLipschitzMetric
import Mathlib.Topology.EMetricSpace.VariationOnFromTo
import Mathlib.Topology.Order.IntermediateValue

/-! Actual arclength factorization of every continuous Euclidean-rectifiable
planar curve. The cumulative parameter is its Euclidean partition variation,
not a derivative integral of a possibly singular BV parametrization. -/
noncomputable section
open Set Filter Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def rectifiableCumulativeLength (γ : ℝ → ℂ) (t : ℝ) : ℝ :=
  variationOnFromTo γ (Icc (0 : ℝ) 1) 0 t

@[simp] theorem rectifiableCumulativeLength_zero (γ : ℝ → ℂ) :
    rectifiableCumulativeLength γ 0 = 0 := variationOnFromTo.self _ _ _

@[simp] theorem rectifiableCumulativeLength_one (γ : ℝ → ℂ) :
    rectifiableCumulativeLength γ 1 = (eVariationOn γ (Icc (0 : ℝ) 1)).toReal := by
  rw [rectifiableCumulativeLength, variationOnFromTo.eq_of_le _ _ zero_le_one, inter_self]

theorem rectifiableCumulativeLength_monotone {γ : ℝ → ℂ}
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1)) :
    MonotoneOn (rectifiableCumulativeLength γ) (Icc (0 : ℝ) 1) :=
  variationOnFromTo.monotoneOn hb.locallyBoundedVariationOn (by norm_num)

theorem rectifiableCumulativeLength_continuous {γ : ℝ → ℂ}
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    ContinuousOn (rectifiableCumulativeLength γ) (Icc (0 : ℝ) 1) := by
  intro t ht
  exact (hb.continuousWithinAt_variationOnFromTo_iff (by norm_num) ht).mpr (hc t ht)

theorem rectifiableCumulativeLength_image {γ : ℝ → ℂ}
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    rectifiableCumulativeLength γ '' Icc (0 : ℝ) 1 =
      Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal := by
  simpa only [rectifiableCumulativeLength_zero, rectifiableCumulativeLength_one] using
    (rectifiableCumulativeLength_continuous hb hc).image_Icc_of_monotoneOn zero_le_one
      (rectifiableCumulativeLength_monotone hb)

theorem rectifiable_dist_le_cumulative_sub {γ : ℝ → ℂ}
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1)) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) (hst : s ≤ t) :
    dist (γ s) (γ t) ≤ rectifiableCumulativeLength γ t - rectifiableCumulativeLength γ s := by
  rw [rectifiableCumulativeLength, rectifiableCumulativeLength,
    variationOnFromTo.sub_right hb.locallyBoundedVariationOn (by norm_num) ht hs,
    variationOnFromTo.eq_of_le _ _ hst, dist_edist]
  apply ENNReal.toReal_mono (hb.mono inter_subset_left)
  exact eVariationOn.edist_le γ ⟨hs, le_rfl, hst⟩ ⟨ht, hst, le_rfl⟩

theorem rectifiable_dist_le_cumulative_dist {γ : ℝ → ℂ}
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1)) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    dist (γ s) (γ t) ≤ dist (rectifiableCumulativeLength γ s) (rectifiableCumulativeLength γ t) := by
  rcases le_total s t with hst | hts
  · rw [Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (rectifiableCumulativeLength_monotone hb hs ht hst))]
    exact rectifiable_dist_le_cumulative_sub hb hs ht hst
  · rw [dist_comm (γ s), dist_comm (rectifiableCumulativeLength γ s)]
    rw [Real.dist_eq, abs_sub_comm,
      abs_of_nonneg (sub_nonneg.mpr (rectifiableCumulativeLength_monotone hb ht hs hts))]
    exact rectifiable_dist_le_cumulative_sub hb ht hs hts

theorem rectifiable_eq_of_cumulative_eq {γ : ℝ → ℂ}
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1)) {s t : ℝ}
    (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1)
    (he : rectifiableCumulativeLength γ s = rectifiableCumulativeLength γ t) : γ s = γ t := by
  have h := rectifiable_dist_le_cumulative_dist hb hs ht
  rw [he, dist_self] at h
  exact dist_le_zero.mp h

/-- Canonical arclength factorization, including constant curves and curves with
stopping intervals or singular continuous original parametrizations. -/
theorem exists_rectifiable_arcLength_factor {γ : ℝ → ℂ}
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    ∃ η : ℝ → ℂ,
      LipschitzOnWith 1 η (Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal) ∧
      η 0 = γ 0 ∧ η (eVariationOn γ (Icc (0 : ℝ) 1)).toReal = γ 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, η (rectifiableCumulativeLength γ t) = γ t) ∧
      η '' Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal = γ '' Icc (0 : ℝ) 1 ∧
      eVariationOn η (Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal) =
        eVariationOn γ (Icc (0 : ℝ) 1) := by
  let v := rectifiableCumulativeLength γ
  let ψ := v.invFunOn (Icc (0 : ℝ) 1)
  let η : ℝ → ℂ := γ ∘ ψ
  have himage : v '' Icc (0 : ℝ) 1 = Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal :=
    rectifiableCumulativeLength_image hb hc
  have hmaps : MapsTo ψ (v '' Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
    (surjOn_image v (Icc (0 : ℝ) 1)).mapsTo_invFunOn
  have hinv : EqOn (v ∘ ψ) id (v '' Icc (0 : ℝ) 1) :=
    (surjOn_image v (Icc (0 : ℝ) 1)).rightInvOn_invFunOn
  have hη : ∀ t ∈ Icc (0 : ℝ) 1, η (v t) = γ t := by
    intro t ht
    have hv : v t ∈ v '' Icc (0 : ℝ) 1 := mem_image_of_mem v ht
    exact rectifiable_eq_of_cumulative_eq hb (hmaps hv) ht (hinv hv)
  have hη0 : η 0 = γ 0 := by simpa only [v, rectifiableCumulativeLength_zero] using hη 0 (by norm_num)
  have hη1 : η (eVariationOn γ (Icc (0 : ℝ) 1)).toReal = γ 1 := by
    simpa only [v, rectifiableCumulativeLength_one] using hη 1 (by norm_num)
  have heq : EqOn (η ∘ v) γ (Icc (0 : ℝ) 1) := hη
  refine ⟨η, ?_, hη0, hη1, hη, ?_, ?_⟩
  · apply LipschitzOnWith.of_dist_le_mul
    intro u hu w hw
    have hu' : u ∈ v '' Icc (0 : ℝ) 1 := by rwa [himage]
    have hw' : w ∈ v '' Icc (0 : ℝ) 1 := by rwa [himage]
    have h := rectifiable_dist_le_cumulative_dist hb (hmaps hu') (hmaps hw')
    change dist (η u) (η w) ≤ dist (v (ψ u)) (v (ψ w)) at h
    have hvu : v (ψ u) = u := hinv hu'
    have hvw : v (ψ w) = w := hinv hw'
    rw [hvu, hvw] at h
    simpa only [NNReal.coe_one, one_mul] using h
  · rw [← himage, ← image_comp]
    exact heq.image_eq
  · rw [← himage, ← eVariationOn.comp_eq_of_monotoneOn η v (rectifiableCumulativeLength_monotone hb)]
    exact eVariationOn.eq_of_eqOn heq

end RepulsiveCoulomb
