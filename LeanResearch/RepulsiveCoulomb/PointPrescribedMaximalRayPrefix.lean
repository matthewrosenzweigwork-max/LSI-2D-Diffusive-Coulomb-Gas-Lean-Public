module

public import LeanResearch.RepulsiveCoulomb.MetricOpenRayPrefix
public import LeanResearch.RepulsiveCoulomb.PointFiniteGeodesicTree

@[expose] public section

/-! Every prescribed actual minimizing edge supplies an explicit unit-speed
open ray prefix and hence has a maximal literal extension. At negative cone
points continuations can branch; this construction uses only compatible chains.
Infinite duration still requires the separate global continuation argument. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

def pointGeodesicOpenRaySeed {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) :
    @MetricOpenRayPrefix ℂ (pointSmoothConformalMetricSpace ha y) := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  let L := (pointSmoothConformalEDist a y E.start E.finish).toReal
  have hL : 0 < L := ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y E.distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne
  let D : NNReal := ⟨L, hL.le⟩
  let τ : NNReal → Icc (0 : ℝ) 1 := fun t ↦
    ⟨min ((t : ℝ) / L) 1, le_min (div_nonneg t.2 hL.le) zero_le_one, min_le_right _ _⟩
  have htau (t : NNReal) (ht : (t : ℝ≥0∞) < D) : (τ t).1 = (t : ℝ) / L := by
    apply min_eq_left
    apply (div_le_one hL).mpr
    exact (show (t : ℝ) < L from ENNReal.coe_lt_coe.mp ht).le
  refine ⟨D, E.curve ∘ τ, ?_⟩
  intro s t hs ht
  change (pointSmoothConformalEDist a y (E.curve (τ s)) (E.curve (τ t))).toReal = dist s t
  rw [E.geodesic, htau s hs, htau t ht, ← sub_div, abs_div, abs_of_pos hL,
    div_mul_cancel₀ _ hL.ne']
  exact abs_sub_comm _ _

theorem pointGeodesicOpenRaySeed_duration {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) :
    letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
    (pointGeodesicOpenRaySeed ha y E).duration = pointSmoothConformalEDist a y E.start E.finish := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  change ((pointSmoothConformalEDist a y E.start E.finish).toNNReal : ℝ≥0∞) = _
  exact ENNReal.coe_toNNReal (pointSmoothConformalEDist_lt_top ha y _ _).ne

theorem pointGeodesicOpenRaySeed_parameter {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y)
    (t : Icc (0 : ℝ) 1) :
    letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
    (pointGeodesicOpenRaySeed ha y E).curve
      ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
        mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ = E.curve t := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  have hL : 0 < (pointSmoothConformalEDist a y E.start E.finish).toReal :=
    ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y E.distinct)
      (pointSmoothConformalEDist_lt_top ha y _ _).ne
  change E.curve ⟨min (((pointSmoothConformalEDist a y E.start E.finish).toReal * t.1) /
      (pointSmoothConformalEDist a y E.start E.finish).toReal) 1, _⟩ = E.curve t
  congr 1
  apply Subtype.ext
  change min (((pointSmoothConformalEDist a y E.start E.finish).toReal * t.1) /
    (pointSmoothConformalEDist a y E.start E.finish).toReal) 1 = t.1
  rw [mul_div_cancel_left₀ _ hL.ne', min_eq_left t.2.2]

/-- The constructed maximal prefix preserves the entire prescribed open edge,
and its duration is at least the actual positive edge length. Finite duration
is deliberately not excluded here. -/
theorem exists_pointConformal_prescribed_maximal_ray_prefix {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) :
    letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
    ∃ p : MetricOpenRayPrefix ℂ,
      pointSmoothConformalEDist a y E.start E.finish ≤ p.duration ∧ IsMax p ∧
      ∀ t : Icc (0 : ℝ) 1, t.1 < 1 →
        p.curve ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
          mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ = E.curve t := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  obtain ⟨p, hp, hmax⟩ := @exists_maximal_metricOpenRayPrefix ℂ
    (pointSmoothConformalMetricSpace ha y) (pointGeodesicOpenRaySeed ha y E)
  refine ⟨p, ?_, hmax, ?_⟩
  · simpa only [pointGeodesicOpenRaySeed_duration ha y E] using hp.1
  · intro t ht
    have hL : 0 < (pointSmoothConformalEDist a y E.start E.finish).toReal :=
      ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y E.distinct)
        (pointSmoothConformalEDist_lt_top ha y _ _).ne
    have htime : (⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
        mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ : NNReal) <
        ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal, ENNReal.toReal_nonneg⟩ := by
      change (pointSmoothConformalEDist a y E.start E.finish).toReal * t.1 <
        (pointSmoothConformalEDist a y E.start E.finish).toReal
      nlinarith
    let T : NNReal := ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
      mul_nonneg ENNReal.toReal_nonneg t.2.1⟩
    have htime' : (T : ℝ≥0∞) < (pointGeodesicOpenRaySeed ha y E).duration :=
      ENNReal.coe_lt_coe.mpr htime
    exact (hp.2 _ htime').symm.trans (pointGeodesicOpenRaySeed_parameter ha y E t)

end RepulsiveCoulomb
