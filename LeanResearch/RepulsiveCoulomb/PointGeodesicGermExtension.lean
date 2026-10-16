import LeanResearch.RepulsiveCoulomb.PointConformalLocalAntipode
import LeanResearch.RepulsiveCoulomb.PointFiniteGeodesicTree

/-! Construct an actual opposite minimizing germ at the starting endpoint of
any nondegenerate minimizing edge. Local distance-additivity is proved, not
assumed. This is the input for the separate triangle-based global continuation. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Every actual minimizing germ admits an opposite actual minimizing edge,
with exact cross-distance additivity on one constructed positive metric ball. -/
theorem exists_pointGeodesic_opposite_germ {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (A : PointGeodesicTreeEdge a y) :
    ∃ B : PointGeodesicTreeEdge a y, B.start = A.start ∧ ∃ r : ℝ, 0 < r ∧
      (pointSmoothConformalEDist a y B.finish A.start).toReal = r ∧
      ∀ x ∈ range A.curve, ∀ z ∈ range B.curve,
        (pointSmoothConformalEDist a y x A.start).toReal ≤ r →
        (pointSmoothConformalEDist a y z A.start).toReal ≤ r →
        (pointSmoothConformalEDist a y x z).toReal =
          (pointSmoothConformalEDist a y x A.start).toReal +
            (pointSmoothConformalEDist a y A.start z).toReal := by
  obtain ⟨R, hR, hanti⟩ := exists_pointConformal_local_antipodes ha y A.start
  let L := (pointSmoothConformalEDist a y A.start A.finish).toReal
  have hL : 0 < L := ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y A.distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne
  have hτpos : 0 < min (1 / 2 : ℝ) (R / (2 * L)) :=
    lt_min (by norm_num) (div_pos hR (by positivity))
  have hτ1 : min (1 / 2 : ℝ) (R / (2 * L)) ≤ 1 := (min_le_left _ _).trans (by norm_num)
  let τ : Icc (0 : ℝ) 1 := ⟨min (1 / 2 : ℝ) (R / (2 * L)), hτpos.le, hτ1⟩
  let u := A.curve τ
  let r := τ.1 * L
  have hr : 0 < r := mul_pos hτpos hL
  have hrR : r ≤ R := by
    have hh := (le_div_iff₀ (show 0 < 2 * L by positivity)).mp
      (min_le_right (1 / 2 : ℝ) (R / (2 * L)))
    change min (1 / 2 : ℝ) (R / (2 * L)) * L ≤ R
    nlinarith
  have hrad (s : Icc (0 : ℝ) 1) :
      (pointSmoothConformalEDist a y (A.curve s) A.start).toReal = s.1 * L := by
    have h := A.geodesic s ⟨0, by norm_num⟩
    simpa only [A.curve_start, zero_sub, abs_neg, abs_of_nonneg s.2.1] using h
  have hur : (pointSmoothConformalEDist a y u A.start).toReal = r := hrad τ
  obtain ⟨v, hv, huv⟩ := hanti u (hur.le.trans hrR)
  rw [hur] at hv huv
  have hqv : A.start ≠ v := by
    intro he
    have hzero : (pointSmoothConformalEDist a y v A.start).toReal = 0 := by
      rw [← he, pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    linarith
  obtain ⟨γ, h0, h1, hc, hd⟩ := exists_pointConformal_geodesic ha y A.start v
  let B : PointGeodesicTreeEdge a y := ⟨A.start, v, hqv, γ, h0, h1, hc, hd⟩
  have hBL : (pointSmoothConformalEDist a y B.start B.finish).toReal = r := by
    change (pointSmoothConformalEDist a y A.start v).toReal = r
    rwa [pointSmoothConformalEDist_comm a y A.start v]
  have htri (x z w : ℂ) : (pointSmoothConformalEDist a y x w).toReal ≤
      (pointSmoothConformalEDist a y x z).toReal + (pointSmoothConformalEDist a y z w).toReal :=
    @dist_triangle ℂ (pointSmoothConformalMetricSpace ha y).toPseudoMetricSpace x z w
  refine ⟨B, rfl, r, hr, hv, ?_⟩
  rintro x ⟨s, rfl⟩ z ⟨t, rfl⟩ hx hz
  have hsτ : s.1 ≤ τ.1 := by
    rw [hrad] at hx
    exact (mul_le_mul_iff_left₀ hL).mp hx
  have hux : (pointSmoothConformalEDist a y u (A.curve s)).toReal = (τ.1 - s.1) * L := by
    change (pointSmoothConformalEDist a y (A.curve τ) (A.curve s)).toReal = _
    rw [A.geodesic, abs_of_nonpos (sub_nonpos.mpr hsτ), neg_sub]
  have hzv : (pointSmoothConformalEDist a y (B.curve t) v).toReal = (1 - t.1) * r := by
    have h := B.geodesic t ⟨1, by norm_num⟩
    rw [B.curve_finish, abs_of_nonneg (sub_nonneg.mpr t.2.2), hBL] at h
    exact h
  have hqz : (pointSmoothConformalEDist a y A.start (B.curve t)).toReal = t.1 * r := by
    have h := B.geodesic ⟨0, by norm_num⟩ t
    rw [B.curve_start, sub_zero, abs_of_nonneg t.2.1, hBL] at h
    exact h
  apply le_antisymm (htri _ A.start _)
  have hbound : (pointSmoothConformalEDist a y u v).toReal ≤
      (pointSmoothConformalEDist a y u (A.curve s)).toReal +
        ((pointSmoothConformalEDist a y (A.curve s) (B.curve t)).toReal +
          (pointSmoothConformalEDist a y (B.curve t) v).toReal) :=
    (htri u (A.curve s) v).trans (add_le_add le_rfl (htri (A.curve s) (B.curve t) v))
  rw [huv, hux, hzv] at hbound
  rw [hrad, hqz]
  have hre : r = τ.1 * L := rfl
  nlinarith

end RepulsiveCoulomb
