module

public import LeanResearch.RepulsiveCoulomb.PointMaximalRayObstruction
public import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments
public import LeanResearch.RepulsiveCoulomb.MetricOppositeRays

@[expose] public section

/-! An actual prescribed complete line, or an actual Jordan obstruction.
Both infinite rays are constructed by the maximal-prefix alternatives. Their
common locally additive corner is transported from literal seed preservation.
If any cross-distance fails, actual finite restrictions give the same Jordan
obstruction. Otherwise their literal signed concatenation is a proper embedded
minimizing complete line. Global turn/flux exclusion remains separate. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- The concrete obstruction produced by a failed minimizing continuation.
This abbreviation includes actual curves, actual Jordan topology, and actual
local metric additivity; it is not an assumed impossibility certificate. -/
abbrev PointJordanGeodesicObstruction {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) : Prop :=
  Nonempty (PointSimpleGeodesicBigon a y) ∨
    ∃ q : ℂ, ∃ r : ℝ, 0 < r ∧ ∃ T : PointSimpleGeodesicTriangle a y q,
      Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr ''
        (range T.left.curve ∪ range T.right.curve ∪ range T.cross.curve)) ∧
      ∀ x ∈ range T.left.curve, ∀ z ∈ range T.right.curve,
        (pointSmoothConformalEDist a y x q).toReal ≤ r →
        (pointSmoothConformalEDist a y z q).toReal ≤ r →
        (pointSmoothConformalEDist a y x z).toReal =
          (pointSmoothConformalEDist a y x q).toReal +
            (pointSmoothConformalEDist a y q z).toReal

/-- Literal preservation makes a small initial intrinsic ball of a ray belong
to its seed edge. This is used on both sides of the constructed line. -/
theorem pointMetricRay_small_ball_mem_seed {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y)
    (γ : NNReal → ℂ) (hzero : γ 0 = E.start)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t)
    (hpreserve : ∀ t : Icc (0 : ℝ) 1,
      γ ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
        mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ = E.curve t)
    {r : ℝ} (hr : r ≤ (pointSmoothConformalEDist a y E.start E.finish).toReal)
    {x : ℂ} (hx : x ∈ range γ)
    (hxr : (pointSmoothConformalEDist a y x E.start).toReal ≤ r) :
    x ∈ range E.curve := by
  obtain ⟨t, rfl⟩ := hx
  have ht : (t : ℝ) ≤ r := by
    rw [← hzero, hd, NNReal.dist_eq, NNReal.coe_zero, sub_zero,
      abs_of_nonneg (a := (t : ℝ)) (by positivity)] at hxr
    exact hxr
  exact pointMetricRay_mem_preserved_edge ha y E γ hpreserve t (ht.trans hr)

/-- Every prescribed actual minimizing edge extends to an actual proper
minimizing complete line, unless a concrete Jordan obstruction exists.
There is no uniqueness-of-continuation or curvature-balance hypothesis. -/
theorem pointPrescribedLine_or_jordan_obstruction {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) :
    (∃ ℓ : ℝ → ℂ, ℓ 0 = E.start ∧ IsClosedEmbedding ℓ ∧ IsProperMap ℓ ∧
      (∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) ∧
      ∀ t : Icc (0 : ℝ) 1,
        ℓ ((pointSmoothConformalEDist a y E.start E.finish).toReal * t.1) = E.curve t) ∨
    PointJordanGeodesicObstruction a y := by
  classical
  rcases pointPrescribedRay_or_jordan_obstruction ha y E with
    ⟨f, hf0, hfc, hfd, hfseed⟩ | hobs
  · have hfclosed := pointMetricRay_closed_preservation y E f hfc hfseed
    obtain ⟨B, hB0, r, hr, _, hlocal⟩ := exists_pointGeodesic_opposite_germ ha y E
    rcases pointPrescribedRay_or_jordan_obstruction ha y B with
      ⟨g, hg0, hgc, hgd, hgseed⟩ | hobs
    · have hgclosed := pointMetricRay_closed_preservation y B g hgc hgseed
      have hfg0 : f 0 = g 0 := hf0.trans (hg0.trans hB0).symm
      have hfbase (s : NNReal) :
          (pointSmoothConformalEDist a y (f s) E.start).toReal = (s : ℝ) := by
        rw [← hf0, hfd, NNReal.dist_eq, NNReal.coe_zero, sub_zero, abs_of_nonneg (a := (s : ℝ)) (by positivity)]
      have hgbase (t : NNReal) :
          (pointSmoothConformalEDist a y E.start (g t)).toReal = (t : ℝ) := by
        rw [← hB0, ← hg0, hgd, NNReal.dist_eq, NNReal.coe_zero, zero_sub,
          abs_neg, abs_of_nonneg (a := (t : ℝ)) (by positivity)]
      by_cases hcross : ∀ s t : NNReal,
          (pointSmoothConformalEDist a y (f s) (g t)).toReal = (s : ℝ) + t
      · have hfi := @Isometry.of_dist_eq NNReal ℂ _
          (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace f hfd
        have hgi := @Isometry.of_dist_eq NNReal ℂ _
          (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace g hgd
        let ℓ := metricOppositeRaysJoin f g
        have hℓi := @metricOppositeRaysJoin_isometry ℂ
          (pointSmoothConformalMetricSpace ha y) f g hfi hgi hcross
        have hℓd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t :=
          @Isometry.dist_eq ℝ ℂ _ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
            ℓ hℓi
        have hℓc := pointMetricLine_isClosedEmbedding ha y ℓ hℓd
        refine Or.inl ⟨ℓ, ?_, hℓc, hℓc.isProperMap, hℓd, ?_⟩
        · simpa only [ℓ, ← NNReal.coe_zero, metricOppositeRaysJoin_nonneg] using hf0
        · intro t
          have h := metricOppositeRaysJoin_nonneg f g
            ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
              mul_nonneg ENNReal.toReal_nonneg t.2.1⟩
          exact h.trans (hfclosed t)
      · push_neg at hcross
        obtain ⟨s, t, hst⟩ := hcross
        have hshort : (pointSmoothConformalEDist a y (f s) (g t)).toReal < (s : ℝ) + t := by
          have htri := @dist_triangle ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace
            (f s) E.start (g t)
          change (pointSmoothConformalEDist a y (f s) (g t)).toReal ≤
            (pointSmoothConformalEDist a y (f s) E.start).toReal +
              (pointSmoothConformalEDist a y E.start (g t)).toReal at htri
          rw [hfbase, hgbase] at htri
          exact lt_of_le_of_ne htri hst
        have hs : 0 < s := by
          apply pos_iff_ne_zero.mpr
          intro he
          have hh := hshort
          rw [he, hf0, hgbase, NNReal.coe_zero, zero_add] at hh
          exact (lt_irrefl _ hh)
        have ht : 0 < t := by
          apply pos_iff_ne_zero.mpr
          intro he
          have hh := hshort
          rw [he, hg0, hB0, hfbase, NNReal.coe_zero, add_zero] at hh
          exact (lt_irrefl _ hh)
        let A' := pointMetricRaySegment ha y f hfd s hs
        let B' := pointMetricRaySegment ha y g hgd t ht
        let ρ := min r (min (pointSmoothConformalEDist a y E.start E.finish).toReal
          (pointSmoothConformalEDist a y B.start B.finish).toReal)
        have hLE : 0 < (pointSmoothConformalEDist a y E.start E.finish).toReal :=
          ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y E.distinct)
            (pointSmoothConformalEDist_lt_top ha y _ _).ne
        have hLB : 0 < (pointSmoothConformalEDist a y B.start B.finish).toReal :=
          ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y B.distinct)
            (pointSmoothConformalEDist_lt_top ha y _ _).ne
        have hρ : 0 < ρ := lt_min hr (lt_min hLE hLB)
        have hρr : ρ ≤ r := min_le_left _ _
        have hρE : ρ ≤ (pointSmoothConformalEDist a y E.start E.finish).toReal :=
          (min_le_right _ _).trans (min_le_left _ _)
        have hρB : ρ ≤ (pointSmoothConformalEDist a y B.start B.finish).toReal :=
          (min_le_right _ _).trans (min_le_right _ _)
        have hcorner : ∀ x ∈ range A'.curve, ∀ z ∈ range B'.curve,
            (pointSmoothConformalEDist a y x E.start).toReal ≤ ρ →
            (pointSmoothConformalEDist a y z E.start).toReal ≤ ρ →
            (pointSmoothConformalEDist a y x z).toReal =
              (pointSmoothConformalEDist a y x E.start).toReal +
                (pointSmoothConformalEDist a y E.start z).toReal := by
          intro x hx z hz hxr hzr
          have hxray := pointMetricRaySegment_range_subset ha y f hfd s hs hx
          have hzray := pointMetricRaySegment_range_subset ha y g hgd t ht hz
          have hxE := pointMetricRay_small_ball_mem_seed ha y E f hf0 hfd hfclosed hρE hxray hxr
          have hzB := pointMetricRay_small_ball_mem_seed ha y B g hg0 hgd hgclosed hρB hzray
            (by simpa only [hB0] using hzr)
          exact hlocal x hxE z hzB (hxr.trans hρr) (hzr.trans hρr)
        have hshort' : (pointSmoothConformalEDist a y A'.finish B'.finish).toReal <
            (pointSmoothConformalEDist a y A'.finish E.start).toReal +
              (pointSmoothConformalEDist a y E.start B'.finish).toReal := by
          change (pointSmoothConformalEDist a y (f s) (g t)).toReal <
            (pointSmoothConformalEDist a y (f s) E.start).toReal +
              (pointSmoothConformalEDist a y E.start (g t)).toReal
          rwa [hfbase, hgbase]
        rcases pointGeodesic_local_additivity_bigon_or_triangle ha y A' B' E.start
          hf0 (hg0.trans hB0) hρ hcorner hshort' with hbigon | ⟨T, hJ, hT⟩
        · exact Or.inr (Or.inl hbigon)
        · exact Or.inr (Or.inr ⟨E.start, ρ, hρ, T, hJ, hT⟩)
    · exact Or.inr hobs
  · exact Or.inr hobs

end RepulsiveCoulomb
