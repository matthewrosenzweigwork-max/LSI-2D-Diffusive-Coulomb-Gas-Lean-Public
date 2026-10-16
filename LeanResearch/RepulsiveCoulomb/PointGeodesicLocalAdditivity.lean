module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicBigonOrTriangle

@[expose] public section

/-! The shortcut alternative now starts from the actual local minimizing
condition across a corner. The extracted triangle retains that same condition
at the same center and intrinsic radius. Global turn exclusion stays separate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointGeodesic_local_additivity_separates_germs {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (A B : PointGeodesicTreeEdge a y)
    (q : ℂ) (hA : A.start = q) (hB : B.start = q) {r : ℝ} (hr : 0 < r)
    (hlocal : ∀ x ∈ range A.curve, ∀ z ∈ range B.curve,
      (pointSmoothConformalEDist a y x q).toReal ≤ r →
      (pointSmoothConformalEDist a y z q).toReal ≤ r →
      (pointSmoothConformalEDist a y x z).toReal =
        (pointSmoothConformalEDist a y x q).toReal + (pointSmoothConformalEDist a y q z).toReal) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s t : Icc (0 : ℝ) 1,
      0 < s.1 → s.1 ≤ ε → 0 < t.1 → t.1 ≤ ε → A.curve s ≠ B.curve t := by
  let LA := (pointSmoothConformalEDist a y A.start A.finish).toReal
  let LB := (pointSmoothConformalEDist a y B.start B.finish).toReal
  have hLA : 0 < LA := ENNReal.toReal_pos (pointSmoothConformalEDist_ne_zero ha y A.distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne
  have hLB : 0 ≤ LB := ENNReal.toReal_nonneg
  have hC : 0 < LA + LB + 1 := by linarith
  let ε := r / (LA + LB + 1)
  have hε : 0 < ε := div_pos hr hC
  have hεC : ε * (LA + LB + 1) = r := div_mul_cancel₀ _ hC.ne'
  refine ⟨ε, hε, ?_⟩
  intro s t hs0 hsε ht0 htε he
  have hAd : (pointSmoothConformalEDist a y (A.curve s) q).toReal = s.1 * LA := by
    have h := A.geodesic s ⟨0, by norm_num⟩
    have h0 : A.curve ⟨0, by norm_num⟩ = q := A.curve_start.trans hA
    simpa only [h0, zero_sub, abs_neg, abs_of_nonneg s.2.1] using h
  have hBd : (pointSmoothConformalEDist a y (B.curve t) q).toReal = t.1 * LB := by
    have h := B.geodesic t ⟨0, by norm_num⟩
    have h0 : B.curve ⟨0, by norm_num⟩ = q := B.curve_start.trans hB
    simpa only [h0, zero_sub, abs_neg, abs_of_nonneg t.2.1] using h
  have hAr : (pointSmoothConformalEDist a y (A.curve s) q).toReal ≤ r := by
    rw [hAd]
    calc
      s.1 * LA ≤ ε * LA := mul_le_mul_of_nonneg_right hsε hLA.le
      _ ≤ ε * (LA + LB + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = r := hεC
  have hBr : (pointSmoothConformalEDist a y (B.curve t) q).toReal ≤ r := by
    rw [hBd]
    calc
      t.1 * LB ≤ ε * LB := mul_le_mul_of_nonneg_right htε hLB
      _ ≤ ε * (LA + LB + 1) := mul_le_mul_of_nonneg_left (by linarith) hε.le
      _ = r := hεC
  have h := hlocal _ (mem_range_self s) _ (mem_range_self t) hAr hBr
  rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at h
  have hp : 0 < (pointSmoothConformalEDist a y (B.curve t) q).toReal := by
    rw [← he, hAd]
    exact mul_pos hs0 hLA
  have hn : 0 ≤ (pointSmoothConformalEDist a y q (B.curve t)).toReal := ENNReal.toReal_nonneg
  linarith

/-- Before global Gauss--Bonnet is invoked, a failed minimizing continuation
has already been reduced to an actual Jordan bigon or a Jordan triangle with
the original locally minimizing corner retained. -/
theorem pointGeodesic_local_additivity_bigon_or_triangle {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (A B : PointGeodesicTreeEdge a y)
    (q : ℂ) (hA : A.start = q) (hB : B.start = q) {r : ℝ} (hr : 0 < r)
    (hlocal : ∀ x ∈ range A.curve, ∀ z ∈ range B.curve,
      (pointSmoothConformalEDist a y x q).toReal ≤ r →
      (pointSmoothConformalEDist a y z q).toReal ≤ r →
      (pointSmoothConformalEDist a y x z).toReal =
        (pointSmoothConformalEDist a y x q).toReal + (pointSmoothConformalEDist a y q z).toReal)
    (hshort : (pointSmoothConformalEDist a y A.finish B.finish).toReal <
      (pointSmoothConformalEDist a y A.finish q).toReal +
        (pointSmoothConformalEDist a y q B.finish).toReal) :
    Nonempty (PointSimpleGeodesicBigon a y) ∨
      ∃ T : PointSimpleGeodesicTriangle a y q,
        Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr ''
          (range T.left.curve ∪ range T.right.curve ∪ range T.cross.curve)) ∧
        ∀ x ∈ range T.left.curve, ∀ z ∈ range T.right.curve,
          (pointSmoothConformalEDist a y x q).toReal ≤ r →
          (pointSmoothConformalEDist a y z q).toReal ≤ r →
          (pointSmoothConformalEDist a y x z).toReal =
            (pointSmoothConformalEDist a y x q).toReal + (pointSmoothConformalEDist a y q z).toReal := by
  obtain ⟨ε, hε, hsep⟩ := pointGeodesic_local_additivity_separates_germs ha y A B q hA hB hr hlocal
  rcases pointGeodesic_shortcut_bigon_or_triangle ha y A B q hA hB hε hsep hshort with
    hbigon | ⟨T, hTA, hTB, hJ⟩
  · exact Or.inl hbigon
  · exact Or.inr ⟨T, hJ, fun x hx z hz hxr hzr ↦ hlocal x (hTA hx) z (hTB hz) hxr hzr⟩

end RepulsiveCoulomb
