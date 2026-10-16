module

public import LeanResearch.RepulsiveCoulomb.LocallyConstantSpeedInterval
public import LeanResearch.RepulsiveCoulomb.PointConstantSpeedRestriction
public import LeanResearch.RepulsiveCoulomb.PointGeodesicLocalAdditivity
public import LeanResearch.RepulsiveCoulomb.PointGeodesicStarGerms

@[expose] public section

/-! An actual locally minimizing constant-speed curve that has a shorter
endpoint distance produces an actual simple geodesic bigon or an actual simple
geodesic triangle retaining a locally minimizing corner. The finite subdivision,
first failed minimizing prefix, both edge restrictions, and corner radius are
constructed. No global uniqueness or total-turn exclusion is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointLocalGeodesic_shortcut_obstruction {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (γ : Icc (0 : ℝ) 1 → ℂ) {c : ℝ}
    (hlocal : ∀ t, ∃ U : Set (Icc (0 : ℝ) 1), IsOpen U ∧ t ∈ U ∧
      ∀ s ∈ U, ∀ t ∈ U,
        (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = c * |t.1 - s.1|)
    (hshort : (pointSmoothConformalEDist a y (γ ⟨0, by norm_num⟩)
      (γ ⟨1, by norm_num⟩)).toReal < c) :
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
  have hc : 0 < c := ENNReal.toReal_nonneg.trans_lt hshort
  let M := pointSmoothConformalMetricSpace ha y
  have hloc : @LocallyConstantSpeedInterval ℂ M.toPseudoMetricSpace c γ := hlocal
  obtain ⟨u, v, hu, huv, hpref, hcell, hfail⟩ :=
    @exists_locallyConstantSpeedInterval_shortcut_corner ℂ M.toPseudoMetricSpace c γ hloc hshort
  change ∀ s t, s ≤ u → t ≤ u →
    (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = c * |t.1 - s.1| at hpref
  change ∀ s ∈ Icc u v, ∀ t ∈ Icc u v,
    (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = c * |t.1 - s.1| at hcell
  change (pointSmoothConformalEDist a y (γ ⟨0, by norm_num⟩) (γ v)).toReal < c * v.1 at hfail
  let o : Icc (0 : ℝ) 1 := ⟨0, by norm_num⟩
  have hou : o < u := hu
  have hleft : ∀ s ∈ Icc o u, ∀ t ∈ Icc o u,
      (pointSmoothConformalEDist a y (γ s) (γ t)).toReal = c * |t.1 - s.1| :=
    fun s hs t ht ↦ hpref s t hs.2 ht.2
  let P := pointConstantSpeedRestriction ha y γ hc o u hou hleft
  let A := pointGeodesicReverseEdge P
  let B := pointConstantSpeedRestriction ha y γ hc u v huv hcell
  have hArange : range A.curve = γ '' Icc o u := by
    rw [show A = pointGeodesicReverseEdge P from rfl, pointGeodesicReverseEdge_range]
    exact pointConstantSpeedRestriction_range ha y γ hc o u hou hleft
  have hBrange : range B.curve = γ '' Icc u v :=
    pointConstantSpeedRestriction_range ha y γ hc u v huv hcell
  obtain ⟨U, hU, huU, hUdist⟩ := hlocal u
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds huU)
  let r := c * (ε / 2)
  have hr : 0 < r := mul_pos hc (half_pos hε)
  have hcross : ∀ x ∈ range A.curve, ∀ z ∈ range B.curve,
      (pointSmoothConformalEDist a y x (γ u)).toReal ≤ r →
      (pointSmoothConformalEDist a y z (γ u)).toReal ≤ r →
      (pointSmoothConformalEDist a y x z).toReal =
        (pointSmoothConformalEDist a y x (γ u)).toReal +
          (pointSmoothConformalEDist a y (γ u) z).toReal := by
    intro x hx z hz hxr hzr
    rw [hArange] at hx
    rw [hBrange] at hz
    obtain ⟨s, hs, rfl⟩ := hx
    obtain ⟨t, ht, rfl⟩ := hz
    have hsu := hpref s u hs.2 le_rfl
    have htu := hcell t ht u ⟨le_rfl, huv.le⟩
    have hut := hcell u ⟨le_rfl, huv.le⟩ t ht
    have hsε : |u.1 - s.1| ≤ ε / 2 := by
      rw [hsu] at hxr
      exact (mul_le_mul_iff_right₀ hc).mp hxr
    have htε : |u.1 - t.1| ≤ ε / 2 := by
      rw [htu] at hzr
      exact (mul_le_mul_iff_right₀ hc).mp hzr
    have hsU : s ∈ U := hεU (by
      change |s.1 - u.1| < ε
      rw [abs_sub_comm]
      linarith)
    have htU : t ∈ U := hεU (by
      change |t.1 - u.1| < ε
      rw [abs_sub_comm]
      linarith)
    rw [hUdist s hsU t htU, hsu, hut,
      abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ t.1 from hs.2.trans ht.1)),
      abs_of_nonneg (sub_nonneg.mpr (show s.1 ≤ u.1 from hs.2)), abs_of_nonneg (sub_nonneg.mpr (show u.1 ≤ t.1 from ht.1))]
    ring
  have hshortAB : (pointSmoothConformalEDist a y A.finish B.finish).toReal <
      (pointSmoothConformalEDist a y A.finish (γ u)).toReal +
        (pointSmoothConformalEDist a y (γ u) B.finish).toReal := by
    change (pointSmoothConformalEDist a y (γ o) (γ v)).toReal <
      (pointSmoothConformalEDist a y (γ o) (γ u)).toReal +
        (pointSmoothConformalEDist a y (γ u) (γ v)).toReal
    rw [hpref o u hou.le le_rfl, hcell u ⟨le_rfl, huv.le⟩ v ⟨huv.le, le_rfl⟩,
      abs_of_nonneg (sub_nonneg.mpr (show o.1 ≤ u.1 from hou.le)), abs_of_nonneg (sub_nonneg.mpr (show u.1 ≤ v.1 from huv.le))]
    change (pointSmoothConformalEDist a y (γ o) (γ v)).toReal <
      c * (u.1 - 0) + c * (v.1 - u.1)
    nlinarith
  rcases pointGeodesic_local_additivity_bigon_or_triangle ha y A B (γ u) rfl rfl hr
    hcross hshortAB with hbigon | ⟨T, hJ, hT⟩
  · exact Or.inl hbigon
  · exact Or.inr ⟨γ u, r, hr, T, hJ, hT⟩

end RepulsiveCoulomb
