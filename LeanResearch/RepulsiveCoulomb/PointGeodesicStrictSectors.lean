import LeanResearch.RepulsiveCoulomb.ConeBoundaryTurn

/-! Distinct synchronized rays at an endpoint give strictly positive values
for both complementary cone-sector angles. The chart and positive metric
radius are constructed. This does not silently identify one sector with the
inside of a Jordan curve; that global side-selection remains separate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Distinct equal-radius points have distinct arguments, including the case
where zero was not initially excluded. -/
theorem complex_arg_div_ne_zero_of_norm_eq {u v : ℂ}
    (hnorm : ‖u‖ = ‖v‖) (hne : u ≠ v) : Complex.arg (v / u) ≠ 0 := by
  have hu : u ≠ 0 := by
    intro hu
    have hv : v = 0 := norm_eq_zero.mp (by rw [← hnorm, hu, norm_zero])
    exact hne (hu.trans hv.symm)
  intro harg
  have hratio : ‖v / u‖ = 1 := by
    rw [norm_div, ← hnorm, div_self (norm_ne_zero_iff.mpr hu)]
  have hpolar := Complex.norm_mul_exp_arg_mul_I (v / u)
  rw [harg, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one,
    hratio, Complex.ofReal_one] at hpolar
  have hvu : v = u := by
    have h := (div_eq_iff hu).mp hpolar.symm
    simpa only [one_mul] using h
  exact hne hvu.symm

/-- Both sectors have strictly positive angle at distinct equal-radius rays;
therefore each endpoint turn is strictly below pi. -/
theorem cone_equal_radius_sector_turns_lt_pi {α : ℝ} (hα : 0 ≤ α)
    {u v : ℂ} (hnorm : ‖u‖ = ‖v‖) (hne : u ≠ v) :
    0 < coneShortSectorAngle α u v ∧ 0 < coneLongSectorAngle α u v ∧
      Real.pi - coneShortSectorAngle α u v < Real.pi ∧
      Real.pi - coneLongSectorAngle α u v < Real.pi := by
  have hshort : 0 < coneShortSectorAngle α u v :=
    mul_pos (by linarith) (abs_pos.mpr (complex_arg_div_ne_zero_of_norm_eq hnorm hne))
  have hlong := hshort.trans_le (coneShortSectorAngle_le_long hα u v)
  exact ⟨hshort, hlong, by linarith, by linarith⟩

/-- For the literal metric, close distinct points at the same intrinsic radius
have positive complementary angles in a constructed cone chart. -/
theorem exists_pointConformal_equal_radius_strict_sector_chart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (p : ℂ) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, ∃ R : ℝ, 0 < R ∧ e p = 0 ∧
      ∀ u v : ℂ,
        (pointSmoothConformalEDist a y u p).toReal ≤ R →
        (pointSmoothConformalEDist a y v p).toReal ≤ R →
        (pointSmoothConformalEDist a y u p).toReal =
          (pointSmoothConformalEDist a y v p).toReal →
        u ≠ v →
        0 < coneShortSectorAngle (coalescedPointExponent a y p / 2) (e u) (e v) ∧
        0 < coneLongSectorAngle (coalescedPointExponent a y p / 2) (e u) (e v) ∧
        Real.pi - coneShortSectorAngle (coalescedPointExponent a y p / 2) (e u) (e v) < Real.pi ∧
        Real.pi - coneLongSectorAngle (coalescedPointExponent a y p / 2) (e u) (e v) < Real.pi := by
  obtain ⟨e, R, hR, hep, hsource, _, hmetric⟩ :=
    exists_pointConformal_classical_cone_disk ha y p
  have hpp : (pointSmoothConformalEDist a y p p).toReal ≤ R := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact hR.le
  refine ⟨e, R, hR, hep, ?_⟩
  intro u v hu hv hrad hne
  have hnorm : ‖e u‖ = ‖e v‖ := by
    rw [hmetric u hu p hpp, hmetric v hv p hpp, hep,
      pointClassicalConeDist_apex, pointClassicalConeDist_apex] at hrad
    exact hrad
  have hene : e u ≠ e v := fun h => hne (e.injOn (hsource hu) (hsource hv) h)
  exact cone_equal_radius_sector_turns_lt_pi
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)) hnorm hene

end RepulsiveCoulomb
