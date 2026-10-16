module

public import LeanResearch.RepulsiveCoulomb.PointPrescribedMaximalRayPrefix
public import LeanResearch.RepulsiveCoulomb.PointGeodesicBigonExtraction

@[expose] public section

/-! Exact closed-time metric facts for the prescribed seed, and the actual
reverse edge of a completed metric prefix. These are explicit curve adapters,
with no uniqueness or continuation assumption. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointGeodesicOpenRaySeed_closed_distance {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y)
    (s t : NNReal)
    (hs : (s : ℝ) ≤ (pointSmoothConformalEDist a y E.start E.finish).toReal)
    (ht : (t : ℝ) ≤ (pointSmoothConformalEDist a y E.start E.finish).toReal) :
    letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
    (pointSmoothConformalEDist a y ((pointGeodesicOpenRaySeed ha y E).curve s)
      ((pointGeodesicOpenRaySeed ha y E).curve t)).toReal = dist s t := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  let L := (pointSmoothConformalEDist a y E.start E.finish).toReal
  have hL : 0 < L := ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y E.distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne
  let τ : NNReal → Icc (0 : ℝ) 1 := fun r ↦
    ⟨min ((r : ℝ) / L) 1, le_min (div_nonneg r.2 hL.le) zero_le_one, min_le_right _ _⟩
  have htau (r : NNReal) (hr : (r : ℝ) ≤ L) : (τ r).1 = (r : ℝ) / L :=
    min_eq_left ((div_le_one hL).mpr hr)
  change (pointSmoothConformalEDist a y (E.curve (τ s)) (E.curve (τ t))).toReal = _
  rw [E.geodesic, htau s hs, htau t ht, ← sub_div, abs_div, abs_of_pos hL,
    div_mul_cancel₀ _ hL.ne']
  exact abs_sub_comm _ _

theorem pointGeodesicOpenRaySeed_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) :
    letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
    (pointGeodesicOpenRaySeed ha y E).curve 0 = E.start := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  have h := pointGeodesicOpenRaySeed_parameter ha y E ⟨0, by norm_num⟩
  let T : NNReal := ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * 0,
    mul_nonneg ENNReal.toReal_nonneg (by norm_num)⟩
  have hT : T = 0 := by
    apply Subtype.ext
    change (pointSmoothConformalEDist a y E.start E.finish).toReal * 0 = 0
    exact mul_zero _
  change (pointGeodesicOpenRaySeed ha y E).curve T = E.curve ⟨0, by norm_num⟩ at h
  rw [hT, E.curve_start] at h
  exact h

theorem pointGeodesicOpenRaySeed_end {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) :
    letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
    (pointGeodesicOpenRaySeed ha y E).curve
      ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal, ENNReal.toReal_nonneg⟩ = E.finish := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  have h := pointGeodesicOpenRaySeed_parameter ha y E ⟨1, by norm_num⟩
  simpa only [mul_one, E.curve_finish] using h

/-- Reverse the same completed prefix; its new edge contains every old point. -/
theorem exists_pointClosedMetricPrefix_reverse_edge {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (R : NNReal) (hR : 0 < R)
    (f : NNReal → ℂ)
    (hf : ∀ s ≤ R, ∀ t ≤ R,
      (pointSmoothConformalEDist a y (f s) (f t)).toReal = dist s t) :
    ∃ E : PointGeodesicTreeEdge a y, E.start = f R ∧ E.finish = f 0 := by
  let τ : Icc (0 : ℝ) 1 → NNReal := fun t ↦
    ⟨(R : ℝ) * (1 - t.1), mul_nonneg R.2 (sub_nonneg.mpr t.2.2)⟩
  have hτ (t : Icc (0 : ℝ) 1) : τ t ≤ R := by
    change (R : ℝ) * (1 - t.1) ≤ R
    calc
      (R : ℝ) * (1 - t.1) ≤ (R : ℝ) * 1 :=
        mul_le_mul_of_nonneg_left (by linarith [t.2.1]) (by positivity)
      _ = (R : ℝ) := mul_one _
  have hD : (pointSmoothConformalEDist a y (f R) (f 0)).toReal = (R : ℝ) := by
    simpa only [NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (a := (R : ℝ)) (by positivity)]
      using hf R le_rfl 0 (show (0 : NNReal) ≤ R from zero_le)
  have hneq : f R ≠ f 0 := by
    intro he
    rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at hD
    exact (ne_of_gt (show (0 : ℝ) < R from hR)) hD.symm
  have hgeo : ∀ s t : Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (f (τ s)) (f (τ t))).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y (f R) (f 0)).toReal := by
    intro s t
    rw [hf _ (hτ s) _ (hτ t), NNReal.dist_eq, hD]
    change |(R : ℝ) * (1 - s.1) - (R : ℝ) * (1 - t.1)| = |t.1 - s.1| * R
    rw [show (R : ℝ) * (1 - s.1) - (R : ℝ) * (1 - t.1) = (R : ℝ) * (t.1 - s.1) by ring,
      abs_mul, abs_of_nonneg (a := (R : ℝ)) (by positivity), mul_comm]
  refine ⟨⟨f R, f 0, hneq, f ∘ τ, ?_, ?_,
    pointConformal_geodesic_continuous ha y (f ∘ τ) hgeo, hgeo⟩, rfl, rfl⟩
  · apply congrArg f
    apply Subtype.ext
    change (R : ℝ) * (1 - 0) = (R : ℝ)
    ring
  · apply congrArg f
    apply Subtype.ext
    change (R : ℝ) * (1 - 1) = (0 : ℝ)
    ring

end RepulsiveCoulomb
