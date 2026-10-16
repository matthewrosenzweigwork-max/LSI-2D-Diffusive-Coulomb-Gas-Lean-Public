module

public import LeanResearch.RepulsiveCoulomb.RectifiableArcLengthSpeed

@[expose] public section

/-! Literal weighted ds length of a continuous Euclidean-rectifiable curve,
defined by its constructed unit-speed Euclidean arclength parametrization.
The original BV derivative is never substituted for ds. -/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ENNReal
namespace RepulsiveCoulomb

def rectifiableArcLengthParam (γ : ℝ → ℂ)
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) : ℝ → ℂ :=
  Classical.choose (exists_rectifiable_unitSpeed_factor hb hc)

theorem rectifiableArcLengthParam_spec (γ : ℝ → ℂ)
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    let η := rectifiableArcLengthParam γ hb hc
    let L := (eVariationOn γ (Icc (0 : ℝ) 1)).toReal
    LipschitzOnWith 1 η (Icc 0 L) ∧ η 0 = γ 0 ∧ η L = γ 1 ∧
      (∀ t ∈ Icc (0 : ℝ) 1, η (rectifiableCumulativeLength γ t) = γ t) ∧
      η '' Icc 0 L = γ '' Icc (0 : ℝ) 1 ∧
      eVariationOn η (Icc 0 L) = eVariationOn γ (Icc (0 : ℝ) 1) ∧
      ∀ᵐ u ∂volume.restrict (Icc 0 L), ‖deriv η u‖ = 1 :=
  Classical.choose_spec (exists_rectifiable_unitSpeed_factor hb hc)

/-- Euclidean ds integral of the conformal density along the actual curve.
The finite arclength interval and unit-speed representative are proved outputs. -/
def pointRectifiableDSLength {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (γ : ℝ → ℂ) (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) : ℝ≥0∞ :=
  ∫⁻ u in Icc 0 (eVariationOn γ (Icc (0 : ℝ) 1)).toReal,
    ENNReal.ofReal (pointConformalDensity a y (rectifiableArcLengthParam γ hb hc u))

theorem pointRectifiableDSLength_eq_arclength_physical {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (γ : ℝ → ℂ)
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    pointRectifiableDSLength a y γ hb hc =
      pointConformalPathELength a y (rectifiableArcLengthParam γ hb hc) 0
        (eVariationOn γ (Icc (0 : ℝ) 1)).toReal := by
  obtain ⟨hη, h0, h1, hf, hi, hv, hs⟩ := rectifiableArcLengthParam_spec γ hb hc
  unfold pointRectifiableDSLength pointConformalPathELength
  apply lintegral_congr_ae
  filter_upwards [hs] with u hu
  rw [hu, ENNReal.ofReal_one, mul_one]

/-- Metric variation is unchanged by the proved monotone arclength factorization;
this statement uses the actual conformal metric on both sides. -/
theorem pointRectifiable_arclength_metricLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ)
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    pointConformalMetricLength ha y (rectifiableArcLengthParam γ hb hc) 0
        (eVariationOn γ (Icc (0 : ℝ) 1)).toReal =
      pointConformalMetricLength ha y γ 0 1 := by
  let η := rectifiableArcLengthParam γ hb hc
  let L := (eVariationOn γ (Icc (0 : ℝ) 1)).toReal
  let v := rectifiableCumulativeLength γ
  have hm : MonotoneOn v (Icc (0 : ℝ) 1) := rectifiableCumulativeLength_monotone hb
  have himage : v '' Icc (0 : ℝ) 1 = Icc 0 L := rectifiableCumulativeLength_image hb hc
  have heq : EqOn (η ∘ v) γ (Icc (0 : ℝ) 1) := (rectifiableArcLengthParam_spec γ hb hc).2.2.2.1
  letI : TopologicalSpace ℂ := (pointSmoothConformalEMetricSpace ha y).toUniformSpace.toTopologicalSpace
  letI : WeakPseudoEMetricSpace ℂ := @PseudoEMetricSpace.toWeakPseudoEMetricSpace ℂ
    (pointSmoothConformalEMetricSpace ha y).toPseudoEMetricSpace
  change eVariationOn η (Icc 0 L) = eVariationOn γ (Icc (0 : ℝ) 1)
  rw [← himage, ← eVariationOn.comp_eq_of_monotoneOn η v hm]
  exact eVariationOn.eq_of_eqOn heq

/-- No continuous rectifiable competitor can be shorter than the smooth-path
metric when its length is the genuine Euclidean ds integral. -/
theorem pointSmoothConformalEDist_le_rectifiable_ds {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ)
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    pointSmoothConformalEDist a y (γ 0) (γ 1) ≤ pointRectifiableDSLength a y γ hb hc := by
  obtain ⟨hη, h0, h1, hf, hi, hv, hs⟩ := rectifiableArcLengthParam_spec γ hb hc
  rw [pointRectifiableDSLength_eq_arclength_physical]
  have h := pointSmoothConformalEDist_le_lipschitz_path ha y hη
    (show 0 ≤ (eVariationOn γ (Icc (0 : ℝ) 1)).toReal from ENNReal.toReal_nonneg)
  rwa [h0, h1] at h

end RepulsiveCoulomb
