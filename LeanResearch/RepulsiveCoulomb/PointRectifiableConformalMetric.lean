module

public import LeanResearch.RepulsiveCoulomb.PointRectifiableDSLength
public import LeanResearch.RepulsiveCoulomb.PointConformalLipschitzLengthEquality

@[expose] public section

/-! Source-faithful identification of the conformal path metric with the infimum
of ∫sqrt(w) ds over all continuous Euclidean-rectifiable competitors. The ds
integral is computed in the constructed unit-speed Euclidean arclength parameter.
No regularity of the original BV parameter, separation, triangulation, or
uniformizing map is assumed. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

/-- Exact equality of physical ds length and the actual conformal metric
variation for every continuous Euclidean-rectifiable parametrized curve. -/
theorem pointRectifiableDSLength_eq_metricLength {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ)
    (hb : BoundedVariationOn γ (Icc (0 : ℝ) 1))
    (hc : ContinuousOn γ (Icc (0 : ℝ) 1)) :
    pointRectifiableDSLength a y γ hb hc = pointConformalMetricLength ha y γ 0 1 := by
  rw [pointRectifiableDSLength_eq_arclength_physical]
  have hη := (rectifiableArcLengthParam_spec γ hb hc).1
  have heq := le_antisymm
    (pointConformalLipschitz_physical_le_metricLength ha y hη)
    (pointConformalMetricLength_le_lipschitz_physical ha y hη)
  exact heq.trans (pointRectifiable_arclength_metricLength ha y γ hb hc)

/-- The ordinary class of continuous Euclidean-rectifiable competitors on the
unit interval. No derivative-integral condition is part of rectifiability. -/
structure PlanarRectifiablePath (x z : ℂ) where
  curve : ℝ → ℂ
  start : curve 0 = x
  finish : curve 1 = z
  boundedVariation : BoundedVariationOn curve (Icc (0 : ℝ) 1)
  continuous : ContinuousOn curve (Icc (0 : ℝ) 1)

/-- The manuscript's all-rectifiable-curve conformal path distance. -/
def pointRectifiableConformalEDist {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (x z : ℂ) : ℝ≥0∞ :=
  ⨅ γ : PlanarRectifiablePath x z,
    pointRectifiableDSLength a y γ.curve γ.boundedVariation γ.continuous

/-- The constructed smooth-path distance is exactly the manuscript's distance;
all finite nonnegative point configurations and all endpoints are covered. -/
theorem pointRectifiableConformalEDist_eq_smooth {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    pointRectifiableConformalEDist a y x z = pointSmoothConformalEDist a y x z := by
  apply le_antisymm
  · apply le_of_forall_gt
    intro r hr
    obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y hr
    obtain ⟨K, hK⟩ := hγ.contDiffOn.exists_lipschitzOnWith one_ne_zero
      (convex_Icc (0 : ℝ) 1) isCompact_Icc
    have hb : BoundedVariationOn γ (Icc (0 : ℝ) 1) := by
      simpa only [Function.comp_id] using
        hK.comp_boundedVariationOn (mapsTo_id _) (BoundedVariationOn.id_Icc (0 : ℝ) 1)
    let γR : PlanarRectifiablePath x z := ⟨γ, h0, h1, hb, hγ.continuous.continuousOn⟩
    have hle : pointRectifiableConformalEDist a y x z ≤
        pointRectifiableDSLength a y γR.curve γR.boundedVariation γR.continuous :=
      iInf_le _ γR
    have hcompare : pointRectifiableDSLength a y γR.curve γR.boundedVariation γR.continuous ≤
        pointConformalPathELength a y γ 0 1 := by
      rw [pointRectifiableDSLength_eq_metricLength ha]
      exact pointConformalMetricLength_le_physical ha y hγ.contDiffOn
    exact hle.trans_lt (hcompare.trans_lt hlen)
  · unfold pointRectifiableConformalEDist
    apply le_iInf
    intro γ
    simpa only [γ.start, γ.finish] using
      pointSmoothConformalEDist_le_rectifiable_ds ha y γ.curve γ.boundedVariation γ.continuous

theorem pointSmoothConformalEDist_eq_rectifiable_infimum {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    pointSmoothConformalEDist a y x z =
      ⨅ γ : PlanarRectifiablePath x z,
        pointRectifiableDSLength a y γ.curve γ.boundedVariation γ.continuous :=
  (pointRectifiableConformalEDist_eq_smooth ha y x z).symm

end RepulsiveCoulomb
