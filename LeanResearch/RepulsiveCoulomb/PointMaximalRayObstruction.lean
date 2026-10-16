module

public import LeanResearch.RepulsiveCoulomb.MetricOpenRayEndpoint
public import LeanResearch.RepulsiveCoulomb.MetricAdditiveSegmentJoin
public import LeanResearch.RepulsiveCoulomb.PointRayPrefixSegmentAdapters
public import LeanResearch.RepulsiveCoulomb.PointGeodesicGermExtension
public import LeanResearch.RepulsiveCoulomb.PointGeodesicLocalAdditivity

@[expose] public section

/-! A finite maximal literal ray prefix forces an actual Jordan obstruction.
Its Cauchy endpoint is completed, the reverse prefix is an actual minimizing
edge, and an actual opposite germ is chosen. Endpoint additivity would give a
strict literal isometric extension. Its failure therefore gives the already
constructed minimizing bigon or locally additive minimizing triangle. No
uniqueness of continuation or global turn-exclusion hypothesis is used. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

theorem pointMaximalRayPrefix_finite_obstruction {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (p : @MetricOpenRayPrefix ℂ (pointSmoothConformalMetricSpace ha y))
    (hp : 0 < @MetricOpenRayPrefix.duration ℂ (pointSmoothConformalMetricSpace ha y) p)
    (hfin : @MetricOpenRayPrefix.duration ℂ (pointSmoothConformalMetricSpace ha y) p ≠ ∞)
    (hmax : IsMax p) :
    Nonempty (PointSimpleGeodesicBigon a y) ∨
      ∃ q : ℂ, ∃ r : ℝ, 0 < r ∧ ∃ T : PointSimpleGeodesicTriangle a y q,
        Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr ''
          (range T.left.curve ∪ range T.right.curve ∪ range T.cross.curve)) ∧
        ∀ x ∈ range T.left.curve, ∀ z ∈ range T.right.curve,
          (pointSmoothConformalEDist a y x q).toReal ≤ r →
          (pointSmoothConformalEDist a y z q).toReal ≤ r →
          (pointSmoothConformalEDist a y x z).toReal =
            (pointSmoothConformalEDist a y x q).toReal +
              (pointSmoothConformalEDist a y q z).toReal := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  let M := pointSmoothConformalMetricSpace ha y
  let R := p.duration.toNNReal
  have hR : 0 < R := ENNReal.toNNReal_pos hp.ne' hfin
  obtain ⟨f, hfold, hf⟩ := @exists_metricOpenRayPrefix_closed_extension ℂ M
    (pointSmoothConformalMetricSpace_complete ha y) p hp hfin
  have hfd : ∀ s ≤ R, ∀ t ≤ R,
      (pointSmoothConformalEDist a y (f s) (f t)).toReal = dist s t := hf
  obtain ⟨A, hAstart, hAfinish⟩ := exists_pointClosedMetricPrefix_reverse_edge ha y R hR f hfd
  obtain ⟨B, hBstart, r, hr, _, hcross⟩ := exists_pointGeodesic_opposite_germ ha y A
  by_cases hshort : (pointSmoothConformalEDist a y A.finish B.finish).toReal <
      (pointSmoothConformalEDist a y A.finish A.start).toReal +
        (pointSmoothConformalEDist a y A.start B.finish).toReal
  · rcases pointGeodesic_local_additivity_bigon_or_triangle ha y A B A.start rfl hBstart hr
      hcross hshort with hbigon | ⟨T, hJ, hT⟩
    · exact Or.inl hbigon
    · exact Or.inr ⟨A.start, r, hr, T, hJ, hT⟩
  · let D : NNReal := ⟨(pointSmoothConformalEDist a y B.start B.finish).toReal,
      ENNReal.toReal_nonneg⟩
    have hD : 0 < D := ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y B.distinct)
      (pointSmoothConformalEDist_lt_top ha y _ _).ne
    let g := (pointGeodesicOpenRaySeed ha y B).curve
    have hg : ∀ s ≤ D, ∀ t ≤ D, @dist ℂ M.toDist (g s) (g t) = dist s t :=
      fun s hs t ht ↦ pointGeodesicOpenRaySeed_closed_distance ha y B s t hs ht
    have hg0 : g 0 = B.start := pointGeodesicOpenRaySeed_zero ha y B
    have hgD : g D = B.finish := pointGeodesicOpenRaySeed_end ha y B
    have hjoin : f R = g 0 := by
      rw [hg0]
      exact hAstart.symm.trans hBstart.symm
    have hfirst : (pointSmoothConformalEDist a y A.finish A.start).toReal = (R : ℝ) := by
      rw [hAfinish, hAstart]
      simpa only [NNReal.dist_eq, NNReal.coe_zero, zero_sub, abs_neg, abs_of_nonneg (a := (R : ℝ)) (by positivity)]
        using hfd 0 (show (0 : NNReal) ≤ R from zero_le) R le_rfl
    have hlast : (pointSmoothConformalEDist a y A.start B.finish).toReal = (D : ℝ) := by
      rw [← hBstart]
      rfl
    have htriangle : (pointSmoothConformalEDist a y A.finish B.finish).toReal ≤
        (pointSmoothConformalEDist a y A.finish A.start).toReal +
          (pointSmoothConformalEDist a y A.start B.finish).toReal :=
      @dist_triangle ℂ M.toPseudoMetricSpace A.finish A.start B.finish
    have heq := le_antisymm htriangle (le_of_not_gt hshort)
    have hfull : @dist ℂ M.toDist (f 0) (g D) = (R : ℝ) + D := by
      change (pointSmoothConformalEDist a y (f 0) (g D)).toReal = _
      rw [hgD, ← hAfinish, heq, hfirst, hlast]
    have hRdur : p.duration = (R : ℝ≥0∞) := (ENNReal.coe_toNNReal hfin).symm
    obtain ⟨q, hpq, hpqlt⟩ := @exists_metricOpenRayPrefix_strict_extension ℂ M
      p R D hRdur hD f g hfold hf hg hjoin hfull
    exact False.elim ((not_lt_of_ge (hmax hpq).1) hpqlt)

/-- Every prescribed minimizing edge has an actual infinite isometric extension
or forces an actual forbidden Jordan configuration. Excluding the latter is the
separate global turn/flux theorem, not an input hidden in this construction. -/
theorem pointPrescribedRay_or_jordan_obstruction {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) :
    (∃ γ : NNReal → ℂ, γ 0 = E.start ∧ Continuous γ ∧
      (∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t) ∧
      ∀ t : Icc (0 : ℝ) 1, t.1 < 1 →
        γ ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
          mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ = E.curve t) ∨
    Nonempty (PointSimpleGeodesicBigon a y) ∨
      ∃ q : ℂ, ∃ r : ℝ, 0 < r ∧ ∃ T : PointSimpleGeodesicTriangle a y q,
        Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr ''
          (range T.left.curve ∪ range T.right.curve ∪ range T.cross.curve)) ∧
        ∀ x ∈ range T.left.curve, ∀ z ∈ range T.right.curve,
          (pointSmoothConformalEDist a y x q).toReal ≤ r →
          (pointSmoothConformalEDist a y z q).toReal ≤ r →
          (pointSmoothConformalEDist a y x z).toReal =
            (pointSmoothConformalEDist a y x q).toReal +
              (pointSmoothConformalEDist a y q z).toReal := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  obtain ⟨p, hplen, hmax, hpreserve⟩ := exists_pointConformal_prescribed_maximal_ray_prefix ha y E
  have hp : 0 < p.duration := lt_of_lt_of_le
    (pos_iff_ne_zero.mpr (pointSmoothConformalEDist_ne_zero ha y E.distinct)) hplen
  by_cases htop : p.duration = ∞
  · have hi := @metricOpenRayPrefix_isometry_of_duration_top ℂ
      (pointSmoothConformalMetricSpace ha y) p htop
    have hc := @Isometry.continuous NNReal ℂ _
      (pointSmoothConformalMetricSpace ha y).toPseudoEMetricSpace p.curve hi
    change @Continuous NNReal ℂ _
      (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace p.curve at hc
    rw [pointSmoothConformalMetricSpace_topology ha y] at hc
    have hzero : p.curve 0 = E.start := by
      have h := hpreserve ⟨0, by norm_num⟩ (by norm_num)
      let T : NNReal := ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * 0,
        mul_nonneg ENNReal.toReal_nonneg (by norm_num)⟩
      have hT : T = 0 := by
        apply Subtype.ext
        change (pointSmoothConformalEDist a y E.start E.finish).toReal * 0 = 0
        exact mul_zero _
      change p.curve T = E.curve ⟨0, by norm_num⟩ at h
      rw [hT, E.curve_start] at h
      exact h
    exact Or.inl ⟨p.curve, hzero, hc,
      @Isometry.dist_eq NNReal ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
        p.curve hi, hpreserve⟩
  · exact Or.inr (pointMaximalRayPrefix_finite_obstruction ha y p hp htop hmax)

end RepulsiveCoulomb
