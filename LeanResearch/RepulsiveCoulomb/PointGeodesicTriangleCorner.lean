import LeanResearch.RepulsiveCoulomb.PointGeodesicLocalAdditivity
import LeanResearch.RepulsiveCoulomb.PointGeodesicStarGerms
import LeanResearch.RepulsiveCoulomb.ConeBoundaryTurn

/-! Both possible cone-sector turns at the retained locally minimizing triangle
corner are nonpositive, including the regular zero-exponent case. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem cone_equal_radius_minimizing_turns_nonpos {α : ℝ} (hα : 0 ≤ α)
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) (hn : ‖u‖ = ‖v‖)
    (hmin : @dist ℂ (classicalConeMetricSpace α hα).toDist u v = ‖u‖ + ‖v‖) :
    Real.pi - coneShortSectorAngle α u v ≤ 0 ∧
      Real.pi - coneLongSectorAngle α u v ≤ 0 := by
  rcases hα.eq_or_lt with hzero | hpos
  · subst α
    rw [classicalCone_zero_dist] at hmin
    have hp := parallelogram_law_with_norm ℝ u v
    rw [norm_sub_rev u v, hmin, ← hn] at hp
    have hsum : u + v = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg (u + v)])
    have hvu : v = -u := by
      calc
        v = (u + v) - u := by ring
        _ = -u := by rw [hsum, zero_sub]
    have harg : Complex.arg (v / u) = Real.pi := by
      rw [hvu, neg_div, div_self hu, Complex.arg_neg_one]
    simp only [coneShortSectorAngle, coneLongSectorAngle, harg,
      abs_of_pos Real.pi_pos, zero_add, one_mul, mul_one]
    constructor <;> linarith
  · exact cone_minimizing_sector_turns_nonpos hpos hu hv hmin

/-- An actual cone chart and synchronized radial germs are constructed at q;
local metric additivity proves both candidate inside turns are nonpositive. -/
theorem exists_pointSimpleGeodesicTriangle_nonpositive_corner {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {q : ℂ}
    (T : PointSimpleGeodesicTriangle a y q) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hlocal : ∀ x ∈ range T.left.curve, ∀ z ∈ range T.right.curve,
      (pointSmoothConformalEDist a y x q).toReal ≤ r₀ →
      (pointSmoothConformalEDist a y z q).toReal ≤ r₀ →
      (pointSmoothConformalEDist a y x z).toReal =
        (pointSmoothConformalEDist a y x q).toReal + (pointSmoothConformalEDist a y q z).toReal) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ R r : ℝ, 0 < r ∧ r < R ∧ r < r₀ ∧ e q = 0 ∧
      {u : ℂ | (pointSmoothConformalEDist a y u q).toReal ≤ R} ⊆ e.source ∧
      Set.BijOn e {u : ℂ | (pointSmoothConformalEDist a y u q).toReal ≤ R} {w : ℂ | ‖w‖ ≤ R} ∧
      (∀ u, (pointSmoothConformalEDist a y u q).toReal ≤ R →
        ∀ v, (pointSmoothConformalEDist a y v q).toReal ≤ R →
          (pointSmoothConformalEDist a y u v).toReal = pointClassicalConeDist a y q (e u) (e v)) ∧
      ∃ s t : Icc (0 : ℝ) 1, 0 < s.1 ∧ s.1 < 1 ∧ 0 < t.1 ∧ t.1 < 1 ∧
        ‖e (T.left.curve s)‖ = r ∧ ‖e (T.right.curve t)‖ = r ∧
        (∀ v : Icc (0 : ℝ) 1,
          e (T.left.curve (pointEdgeSubparam ⟨0, by norm_num⟩ s v)) = v.1 • e (T.left.curve s) ∧
          e (T.right.curve (pointEdgeSubparam ⟨0, by norm_num⟩ t v)) = v.1 • e (T.right.curve t)) ∧
        Real.pi - coneShortSectorAngle (coalescedPointExponent a y q / 2)
          (e (T.left.curve s)) (e (T.right.curve t)) ≤ 0 ∧
        Real.pi - coneLongSectorAngle (coalescedPointExponent a y q / 2)
          (e (T.left.curve s)) (e (T.right.curve t)) ≤ 0 := by
  let E : Bool → PointGeodesicTreeEdge a y := fun b ↦ if b then T.right else T.left
  have hstart : ∀ b, (E b).start = q := by
    intro b
    cases b
    · exact T.left_start
    · exact T.right_start
  have hpair : ∀ i j, i ≠ j → ∀ z ∈ range (E i).curve, z ∈ range (E j).curve →
      z = (E i).start ∨ z = (E i).finish := by
    intro i j hij z hzi hzj
    cases i <;> cases j
    · exact False.elim (hij rfl)
    · left
      change z = T.left.start
      rw [T.left_start]
      exact mem_singleton_iff.mp (T.legs_meet ▸ And.intro hzi hzj)
    · left
      change z = T.right.start
      rw [T.right_start]
      exact mem_singleton_iff.mp (T.legs_meet ▸ And.intro hzj hzi)
    · exact False.elim (hij rfl)
  obtain ⟨e, R, r, hr, hrR, hrr₀, heq, hsource, hbij, hmetric,
    τ, hτ, hdist, hnorm, hinj, hradial⟩ :=
    exists_pointConformal_finite_star_germs ha y E q hstart hpair hr₀
  have hb (b : Bool) : (pointSmoothConformalEDist a y ((E b).curve (τ b)) q).toReal ≤ R :=
    (hdist b).le.trans hrR.le
  have hb₀ (b : Bool) : (pointSmoothConformalEDist a y ((E b).curve (τ b)) q).toReal ≤ r₀ :=
    (hdist b).le.trans hrr₀.le
  have hmin : pointClassicalConeDist a y q (e ((E false).curve (τ false)))
      (e ((E true).curve (τ true))) =
        ‖e ((E false).curve (τ false))‖ + ‖e ((E true).curve (τ true))‖ := by
    rw [← hmetric _ (hb false) _ (hb true)]
    have h := hlocal _ (mem_range_self (τ false)) _ (mem_range_self (τ true)) (hb₀ false) (hb₀ true)
    change (pointSmoothConformalEDist a y ((E false).curve (τ false))
        ((E true).curve (τ true))).toReal =
      (pointSmoothConformalEDist a y ((E false).curve (τ false)) q).toReal +
        (pointSmoothConformalEDist a y q ((E true).curve (τ true))).toReal at h
    rw [pointSmoothConformalEDist_comm a y q ((E true).curve (τ true))] at h
    rw [hnorm false, hnorm true]
    simpa only [hdist false, hdist true] using h
  have hu : e ((E false).curve (τ false)) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hnorm false]; exact hr.ne')
  have hv : e ((E true).curve (τ true)) ≠ 0 :=
    norm_ne_zero_iff.mp (by rw [hnorm true]; exact hr.ne')
  have hturn := cone_equal_radius_minimizing_turns_nonpos
    (div_nonneg (coalescedPointExponent_nonneg a y q) (by norm_num)) hu hv
    ((hnorm false).trans (hnorm true).symm) hmin
  exact ⟨e, R, r, hr, hrR, hrr₀, heq, hsource, hbij, hmetric, τ false, τ true,
    (hτ false).1, (hτ false).2, (hτ true).1, (hτ true).2, hnorm false, hnorm true,
    fun v ↦ ⟨hradial false v, hradial true v⟩, hturn⟩

end RepulsiveCoulomb
