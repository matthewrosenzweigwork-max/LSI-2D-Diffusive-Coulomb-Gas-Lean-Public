module

public import LeanResearch.RepulsiveCoulomb.PointRayPrefixSegmentAdapters
public import Mathlib.Topology.Order.DenselyOrdered
public import Mathlib.Topology.Maps.Proper.Basic

@[expose] public section

/-! A ray preserving an open prescribed edge preserves its closed endpoint as
well. Actual bounded portions of an isometric ray are constructed as minimizing
edges. Closed embedding and properness refer to the ordinary complex topology. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem pointMetricRay_closed_preservation {m : ℕ} {a : Fin m → ℝ}
    (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y) (γ : NNReal → ℂ)
    (hγ : Continuous γ)
    (hpreserve : ∀ t : Icc (0 : ℝ) 1, t.1 < 1 →
      γ ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
        mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ = E.curve t) :
    ∀ t : Icc (0 : ℝ) 1,
      γ ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
        mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ = E.curve t := by
  let top : Icc (0 : ℝ) 1 := ⟨1, by norm_num⟩
  let τ : Icc (0 : ℝ) 1 → NNReal := fun t ↦
    ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
      mul_nonneg ENNReal.toReal_nonneg t.2.1⟩
  have hτ : Continuous τ := (continuous_const.mul continuous_subtype_val).subtype_mk _
  have heq : EqOn (γ ∘ τ) E.curve (Iio top) := fun t ht ↦ hpreserve t ht
  have hclosure : closure (Iio top) = Iic top :=
    closure_Iio' ⟨⟨0, by norm_num⟩, by change (0 : ℝ) < 1; norm_num⟩
  intro t
  exact heq.closure (hγ.comp hτ) E.continuous (by rw [hclosure]; exact t.2.2)

/-- All ray points at times no larger than the prescribed edge length are
actual points of that edge; no choice of a new minimizing segment is made. -/
theorem pointMetricRay_mem_preserved_edge {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (E : PointGeodesicTreeEdge a y)
    (γ : NNReal → ℂ)
    (hpreserve : ∀ t : Icc (0 : ℝ) 1,
      γ ⟨(pointSmoothConformalEDist a y E.start E.finish).toReal * t.1,
        mul_nonneg ENNReal.toReal_nonneg t.2.1⟩ = E.curve t)
    (s : NNReal) (hs : (s : ℝ) ≤ (pointSmoothConformalEDist a y E.start E.finish).toReal) :
    γ s ∈ range E.curve := by
  let L := (pointSmoothConformalEDist a y E.start E.finish).toReal
  have hL : 0 < L := ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y E.distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne
  let t : Icc (0 : ℝ) 1 := ⟨(s : ℝ) / L, div_nonneg s.2 hL.le,
    (div_le_one hL).mpr hs⟩
  refine ⟨t, ?_⟩
  have htime : (⟨L * t.1, mul_nonneg hL.le t.2.1⟩ : NNReal) = s := by
    apply Subtype.ext
    exact mul_div_cancel₀ _ hL.ne'
  exact (hpreserve t).symm.trans (congrArg γ htime)

/-- The literal time restriction of a supplied metric ray. -/
def pointMetricRaySegment {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : NNReal → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t)
    (R : NNReal) (hR : 0 < R) : PointGeodesicTreeEdge a y := by
  let τ : Icc (0 : ℝ) 1 → NNReal := fun t ↦ ⟨(R : ℝ) * t.1, mul_nonneg R.2 t.2.1⟩
  have hzero : τ ⟨0, by norm_num⟩ = 0 := by ext; exact mul_zero _
  have hone : τ ⟨1, by norm_num⟩ = R := by ext; exact mul_one _
  have hD : (pointSmoothConformalEDist a y (γ 0) (γ R)).toReal = (R : ℝ) := by
    simpa only [NNReal.dist_eq, NNReal.coe_zero, zero_sub, abs_neg, abs_of_nonneg (a := (R : ℝ)) (by positivity)]
      using hd 0 R
  have hneq : γ 0 ≠ γ R := by
    intro he
    rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at hD
    exact (ne_of_gt (show (0 : ℝ) < R from hR)) hD.symm
  have hgeo : ∀ s t : Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (γ (τ s)) (γ (τ t))).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y (γ 0) (γ R)).toReal := by
    intro s t
    rw [hd, NNReal.dist_eq, hD]
    change |(R : ℝ) * s.1 - (R : ℝ) * t.1| = |t.1 - s.1| * R
    rw [← mul_sub, abs_mul, abs_of_nonneg (a := (R : ℝ)) (by positivity), abs_sub_comm, mul_comm]
  exact ⟨γ 0, γ R, hneq, γ ∘ τ, congrArg γ hzero, congrArg γ hone,
    pointConformal_geodesic_continuous ha y (γ ∘ τ) hgeo, hgeo⟩

theorem pointMetricRaySegment_range_subset {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : NNReal → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t)
    (R : NNReal) (hR : 0 < R) :
    range (pointMetricRaySegment ha y γ hd R hR).curve ⊆ range γ := by
  rintro z ⟨t, rfl⟩
  exact ⟨⟨(R : ℝ) * t.1, mul_nonneg R.2 t.2.1⟩, rfl⟩

theorem pointMetricRay_isClosedEmbedding {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : NNReal → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t) :
    IsClosedEmbedding γ := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  have hi := @Isometry.of_dist_eq NNReal ℂ _
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace γ hd
  have hc := hi.isClosedEmbedding
  change @IsClosedEmbedding NNReal ℂ _
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ at hc
  rwa [pointSmoothConformalMetricSpace_topology ha y] at hc

theorem pointMetricLine_isClosedEmbedding {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (γ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = dist s t) :
    IsClosedEmbedding γ := by
  letI : MetricSpace ℂ := pointSmoothConformalMetricSpace ha y
  have hi := @Isometry.of_dist_eq ℝ ℂ _
    (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace γ hd
  have hc := hi.isClosedEmbedding
  change @IsClosedEmbedding ℝ ℂ _
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace γ at hc
  rwa [pointSmoothConformalMetricSpace_topology ha y] at hc

end RepulsiveCoulomb
