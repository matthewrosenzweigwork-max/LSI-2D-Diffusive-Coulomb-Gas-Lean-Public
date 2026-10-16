module

public import LeanResearch.RepulsiveCoulomb.PointGeodesicStarGerms
public import LeanResearch.RepulsiveCoulomb.PointGeodesicTriangleCorner
public import LeanResearch.RepulsiveCoulomb.PointRadialSectorNormalization

@[expose] public section

/-! Actual full cone disks along a complete minimizing point-metric line.
The entire line in the disk, rather than merely two selected germs, is shown
to be exactly its two radial traces. Both possible side-link angles are at
least pi. This is a local boundary-chart construction; no global side region,
intrinsic halfplane metric, or global uniqueness certificate is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- An actual isometric line has a full cone disk with exactly two radial
boundary traces and nonpositive boundary turn on either side. -/
theorem exists_pointMetricLine_radial_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ R : ℝ, 0 < R ∧ e (ℓ 0) = 0 ∧
      {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R} ⊆ e.source ∧
      Set.BijOn e {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R}
        {w : ℂ | ‖w‖ ≤ R} ∧
      (∀ u, (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v (ℓ 0)).toReal ≤ R →
          (pointSmoothConformalEDist a y u v).toReal =
            pointClassicalConeDist a y (ℓ 0) (e u) (e v)) ∧
      ‖e (ℓ R)‖ = R ∧ ‖e (ℓ (-R))‖ = R ∧ e (ℓ R) ≠ e (ℓ (-R)) ∧
      (∀ t : Icc (0 : ℝ) 1, e (ℓ (R * t.1)) = t.1 • e (ℓ R) ∧
        e (ℓ (-R * t.1)) = t.1 • e (ℓ (-R))) ∧
      e '' (range ℓ ∩ {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R}) =
        range (fun t : Icc (0 : ℝ) 1 ↦ t.1 • e (ℓ R)) ∪
          range (fun t : Icc (0 : ℝ) 1 ↦ t.1 • e (ℓ (-R))) ∧
      Real.pi ≤ coneShortSectorAngle (coalescedPointExponent a y (ℓ 0) / 2)
        (e (ℓ R)) (e (ℓ (-R))) ∧
      Real.pi ≤ coneLongSectorAngle (coalescedPointExponent a y (ℓ 0) / 2)
        (e (ℓ R)) (e (ℓ (-R))) := by
  obtain ⟨e, R, hR, he0, hsource, hbij, hmetric, hradial⟩ :=
    exists_pointConformal_radial_full_disk ha y (ℓ 0)
  have hbase (t : ℝ) : (pointSmoothConformalEDist a y (ℓ t) (ℓ 0)).toReal = |t| := by
    rw [hd, Real.dist_eq, sub_zero]
  have hpos : (pointSmoothConformalEDist a y (ℓ R) (ℓ 0)).toReal = R := by
    rw [hbase, abs_of_pos hR]
  have hneg : (pointSmoothConformalEDist a y (ℓ (-R)) (ℓ 0)).toReal = R := by
    rw [hbase, abs_neg, abs_of_pos hR]
  have hzero : (pointSmoothConformalEDist a y (ℓ 0) (ℓ 0)).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  have hnorm (z : ℂ) (hz : (pointSmoothConformalEDist a y z (ℓ 0)).toReal ≤ R) :
      ‖e z‖ = (pointSmoothConformalEDist a y z (ℓ 0)).toReal := by
    rw [hmetric z hz (ℓ 0) hzero, he0, pointClassicalConeDist_apex]
  have hnpos : ‖e (ℓ R)‖ = R := (hnorm _ hpos.le).trans hpos
  have hnneg : ‖e (ℓ (-R))‖ = R := (hnorm _ hneg.le).trans hneg
  let A : Icc (0 : ℝ) 1 → ℂ := fun t ↦ ℓ (R * t.1)
  let B : Icc (0 : ℝ) 1 → ℂ := fun t ↦ ℓ (-R * t.1)
  have hA0 : A ⟨0, by norm_num⟩ = ℓ 0 := by change ℓ (R * 0) = ℓ 0; rw [mul_zero]
  have hA1 : A ⟨1, by norm_num⟩ = ℓ R := by change ℓ (R * 1) = ℓ R; rw [mul_one]
  have hB0 : B ⟨0, by norm_num⟩ = ℓ 0 := by change ℓ (-R * 0) = ℓ 0; rw [mul_zero]
  have hB1 : B ⟨1, by norm_num⟩ = ℓ (-R) := by change ℓ (-R * 1) = ℓ (-R); rw [mul_one]
  have hA : ∀ s t : Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (A s) (A t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y (ℓ 0) (ℓ R)).toReal := by
    intro s t
    change (pointSmoothConformalEDist a y (ℓ (R * s.1)) (ℓ (R * t.1))).toReal = _
    rw [hd, pointSmoothConformalEDist_comm a y (ℓ 0) (ℓ R), hpos, Real.dist_eq,
      ← mul_sub, abs_mul, abs_of_pos hR, abs_sub_comm, mul_comm]
  have hB : ∀ s t : Icc (0 : ℝ) 1,
      (pointSmoothConformalEDist a y (B s) (B t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y (ℓ 0) (ℓ (-R))).toReal := by
    intro s t
    change (pointSmoothConformalEDist a y (ℓ (-R * s.1)) (ℓ (-R * t.1))).toReal = _
    rw [hd, pointSmoothConformalEDist_comm a y (ℓ 0) (ℓ (-R)), hneg, Real.dist_eq,
      ← mul_sub, abs_mul, abs_neg, abs_of_pos hR, abs_sub_comm, mul_comm]
  have hrA := hradial (ℓ R) hpos.le A hA0 hA1 hA
  have hrB := hradial (ℓ (-R)) hneg.le B hB0 hB1 hB
  have hcarrier : range ℓ ∩
      {u : ℂ | (pointSmoothConformalEDist a y u (ℓ 0)).toReal ≤ R} = range A ∪ range B := by
    ext z
    constructor
    · rintro ⟨⟨t, rfl⟩, ht⟩
      change (pointSmoothConformalEDist a y (ℓ t) (ℓ 0)).toReal ≤ R at ht
      rw [hbase] at ht
      by_cases ht0 : 0 ≤ t
      · left
        let u : Icc (0 : ℝ) 1 := ⟨t / R, div_nonneg ht0 hR.le,
          (div_le_one hR).mpr ((le_abs_self t).trans ht)⟩
        refine ⟨u, ?_⟩
        change ℓ (R * (t / R)) = ℓ t
        rw [mul_div_cancel₀ _ hR.ne']
      · right
        let u : Icc (0 : ℝ) 1 := ⟨(-t) / R, div_nonneg (neg_nonneg.mpr (le_of_not_ge ht0)) hR.le,
          (div_le_one hR).mpr ((neg_le_abs t).trans ht)⟩
        refine ⟨u, ?_⟩
        change ℓ (-R * ((-t) / R)) = ℓ t
        congr 1
        calc
          -R * ((-t) / R) = -(R * ((-t) / R)) := neg_mul _ _
          _ = t := by rw [mul_div_cancel₀ _ hR.ne', neg_neg]
    · rintro (⟨t, rfl⟩ | ⟨t, rfl⟩)
      · refine ⟨⟨R * t.1, rfl⟩, ?_⟩
        change (pointSmoothConformalEDist a y (ℓ (R * t.1)) (ℓ 0)).toReal ≤ R
        rw [hbase, abs_of_nonneg (mul_nonneg hR.le t.2.1)]
        exact (mul_le_mul_of_nonneg_left t.2.2 hR.le).trans_eq (mul_one R)
      · refine ⟨⟨-R * t.1, rfl⟩, ?_⟩
        change (pointSmoothConformalEDist a y (ℓ (-R * t.1)) (ℓ 0)).toReal ≤ R
        rw [hbase, neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hR.le t.2.1)]
        exact (mul_le_mul_of_nonneg_left t.2.2 hR.le).trans_eq (mul_one R)
  have hmin : pointClassicalConeDist a y (ℓ 0) (e (ℓ R)) (e (ℓ (-R))) =
      ‖e (ℓ R)‖ + ‖e (ℓ (-R))‖ := by
    rw [← hmetric _ hpos.le _ hneg.le, hd, Real.dist_eq, hnpos, hnneg,
      abs_of_nonneg (by linarith : 0 ≤ R - -R)]
    ring
  have hne : e (ℓ R) ≠ e (ℓ (-R)) := by
    intro he
    have hℓeq := hbij.injOn hpos.le hneg.le he
    have h := hd R (-R)
    rw [hℓeq, pointSmoothConformalEDist_self, ENNReal.toReal_zero, Real.dist_eq,
      abs_of_nonneg (by linarith : 0 ≤ R - -R)] at h
    linarith
  have hturn := cone_equal_radius_minimizing_turns_nonpos
    (div_nonneg (coalescedPointExponent_nonneg a y (ℓ 0)) (by norm_num))
    (norm_ne_zero_iff.mp (hnpos.trans_ne hR.ne'))
    (norm_ne_zero_iff.mp (hnneg.trans_ne hR.ne')) (hnpos.trans hnneg.symm) hmin
  refine ⟨e, R, hR, he0, hsource, hbij, hmetric, hnpos, hnneg, hne,
    fun t ↦ ⟨hrA t, hrB t⟩, ?_, by linarith [hturn.1], by linarith [hturn.2]⟩
  rw [hcarrier, image_union]
  congr 1
  · rw [← range_comp]
    exact congrArg range (funext hrA)
  · rw [← range_comp]
    exact congrArg range (funext hrB)

end RepulsiveCoulomb
