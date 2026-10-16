import LeanResearch.RepulsiveCoulomb.ConeBoundaryTurn

/-! Equality in the radial lower bound forces points onto the same cone ray.
This is an actual metric statement, useful for describing a shortest arc ending
at a puncture; it does not assume a polygonal realization of the full surface. -/
noncomputable section
namespace RepulsiveCoulomb

theorem classicalCone_distance_sq {α : ℝ} (hα : 0 < α) (u v : ℂ) :
    (@dist ℂ (classicalConeMetricSpace α hα.le).toDist u v) ^ 2 =
      ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * ‖u‖ * ‖v‖ *
        Real.cos (min Real.pi ((α + 1) * |Complex.arg (v / u)|)) := by
  rw [classicalCone_distance_formula hα]
  apply Real.sq_sqrt
  have hp : 0 ≤ 2 * ‖u‖ * ‖v‖ *
      (1 - Real.cos (min Real.pi ((α + 1) * |Complex.arg (v / u)|))) :=
    mul_nonneg (by positivity) (sub_nonneg.mpr (Real.cos_le_one _))
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

theorem classicalCone_radial_distance_eq_iff {α : ℝ} (hα : 0 < α)
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0) :
    @dist ℂ (classicalConeMetricSpace α hα.le).toDist u v = |‖v‖ - ‖u‖| ↔
      Complex.arg (v / u) = 0 := by
  constructor
  · intro he
    have hs := classicalCone_distance_sq hα u v
    rw [he, sq_abs] at hs
    have hprod : 0 < 2 * ‖u‖ * ‖v‖ := by
      have := norm_pos_iff.mpr hu
      have := norm_pos_iff.mpr hv
      positivity
    have hcos : Real.cos (min Real.pi ((α + 1) * |Complex.arg (v / u)|)) = 1 := by
      have heq : (2 * ‖u‖ * ‖v‖) *
          (Real.cos (min Real.pi ((α + 1) * |Complex.arg (v / u)|)) - 1) = 0 := by nlinarith
      exact sub_eq_zero.mp ((mul_eq_zero.mp heq).resolve_left hprod.ne')
    have hmin : min Real.pi ((α + 1) * |Complex.arg (v / u)|) = 0 :=
      Real.strictAntiOn_cos.injOn
        ⟨le_min Real.pi_pos.le (by positivity), min_le_left _ _⟩
        ⟨le_rfl, Real.pi_pos.le⟩ (by simpa using hcos)
    have hang : (α + 1) * |Complex.arg (v / u)| = 0 := by
      by_contra hn
      have hpos : 0 < (α + 1) * |Complex.arg (v / u)| :=
        lt_of_le_of_ne (by positivity) (Ne.symm hn)
      have := lt_min Real.pi_pos hpos
      rw [hmin] at this
      exact (lt_irrefl 0) this
    exact abs_eq_zero.mp ((mul_eq_zero.mp hang).resolve_left (by linarith))
  · intro hang
    rw [classicalCone_distance_formula hα, hang, abs_zero, mul_zero,
      min_eq_right Real.pi_pos.le, Real.cos_zero]
    have heq : ‖u‖ ^ 2 + ‖v‖ ^ 2 - 2 * ‖u‖ * ‖v‖ * 1 = (‖v‖ - ‖u‖) ^ 2 := by ring
    rw [heq, Real.sqrt_sq_eq_abs]

theorem classicalCone_radial_equality_same_ray {α : ℝ} (hα : 0 < α)
    {u v : ℂ} (hu : u ≠ 0) (hv : v ≠ 0)
    (he : @dist ℂ (classicalConeMetricSpace α hα.le).toDist u v = |‖v‖ - ‖u‖|) :
    v = (‖v‖ / ‖u‖) • u := by
  have ha := (classicalCone_radial_distance_eq_iff hα hu hv).mp he
  have hq : (‖v / u‖ : ℂ) = v / u := by
    simpa only [ha, Complex.ofReal_zero, zero_mul, Complex.exp_zero, mul_one] using
      Complex.norm_mul_exp_arg_mul_I (v / u)
  rw [norm_div] at hq
  rw [Complex.real_smul, ← div_eq_iff hu]
  exact hq.symm

/-- Every constant-speed cone geodesic issuing from the apex has the exact
radial parameterization in intrinsic-radius coordinates. -/
theorem classicalCone_geodesic_from_apex {α : ℝ} (hα : 0 < α)
    (γ : Set.Icc (0 : ℝ) 1 → ℂ) (w : ℂ)
    (h0 : γ ⟨0, by norm_num⟩ = 0) (h1 : γ ⟨1, by norm_num⟩ = w)
    (hd : ∀ s t, @dist ℂ (classicalConeMetricSpace α hα.le).toDist (γ s) (γ t) =
      |t.1 - s.1| * ‖w‖) (t : Set.Icc (0 : ℝ) 1) :
    γ t = t.1 • w := by
  have hr : ‖γ t‖ = t.1 * ‖w‖ := by
    have h := hd t ⟨0, by norm_num⟩
    rw [h0, classicalCone_dist_apex, zero_sub, abs_neg, abs_of_nonneg t.2.1] at h
    exact h
  by_cases hw : w = 0
  · rw [hw, norm_zero, mul_zero] at hr
    rw [norm_eq_zero.mp hr, hw, smul_zero]
  by_cases ht : t.1 = 0
  · have he : t = ⟨0, by norm_num⟩ := Subtype.ext ht
    rw [he, h0]
    simp
  have hγ : γ t ≠ 0 := by
    apply norm_pos_iff.mp
    rw [hr]
    exact mul_pos (lt_of_le_of_ne t.2.1 (Ne.symm ht)) (norm_pos_iff.mpr hw)
  have he : @dist ℂ (classicalConeMetricSpace α hα.le).toDist w (γ t) =
      |‖γ t‖ - ‖w‖| := by
    have h := hd ⟨1, by norm_num⟩ t
    rw [h1, abs_of_nonpos (sub_nonpos.mpr t.2.2)] at h
    rw [h, hr, abs_of_nonpos (by nlinarith [norm_nonneg w, t.2.2])]
    ring
  rw [classicalCone_radial_equality_same_ray hα hw hγ he, hr,
    mul_div_cancel_right₀ _ (norm_ne_zero_iff.mpr hw)]

end RepulsiveCoulomb
