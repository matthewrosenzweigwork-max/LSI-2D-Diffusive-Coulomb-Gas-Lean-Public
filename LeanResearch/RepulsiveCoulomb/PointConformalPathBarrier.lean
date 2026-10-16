import LeanResearch.RepulsiveCoulomb.PointSmoothConformalDistance
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

/-! Smooth test functions whose physical derivatives are dominated by the conformal
density control endpoint oscillation along genuine smooth paths. This is a step
towards nondegeneracy of the path distance, not an assumed analytic inequality. -/
noncomputable section
open MeasureTheory Set Metric
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem pointConformalPath_barrier {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    {φ : ℂ → ℝ} (hφ : ContDiff ℝ 1 φ) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ z, ‖fderiv ℝ φ z‖ ≤ C * pointConformalDensity a y z)
    {γ : ℝ → ℂ} {s t : ℝ} (hγ : ContDiffOn ℝ 1 γ (Icc s t)) (hst : s ≤ t) :
    ‖φ (γ t) - φ (γ s)‖ₑ ≤ ENNReal.ofReal C * pointConformalPathELength a y γ s t := by
  have hc : ContDiffOn ℝ 1 (φ ∘ γ) (Icc s t) := hφ.comp_contDiffOn hγ
  apply (enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hc hst).trans
  have hm : (∫⁻ u in Icc s t, ‖deriv (φ ∘ γ) u‖ₑ) ≤
      ∫⁻ u in Icc s t, ENNReal.ofReal C *
        (ENNReal.ofReal (pointConformalDensity a y (γ u)) * ENNReal.ofReal ‖deriv γ u‖) := by
    apply lintegral_mono_ae
    rw [← restrict_Ioo_eq_restrict_Icc]
    filter_upwards [self_mem_ae_restrict measurableSet_Ioo] with u hu
    have hg : DifferentiableAt ℝ γ u :=
      ((hγ u ⟨hu.1.le, hu.2.le⟩).contDiffAt (Icc_mem_nhds hu.1 hu.2)).differentiableAt one_ne_zero
    rw [fderiv_comp_deriv u (hφ.differentiable one_ne_zero).differentiableAt hg]
    have hn : ‖(fderiv ℝ φ (γ u)) (deriv γ u)‖ ≤
        C * pointConformalDensity a y (γ u) * ‖deriv γ u‖ :=
      (ContinuousLinearMap.le_opNorm _ _).trans
        (mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _))
    rw [← ofReal_norm]
    calc
      _ ≤ ENNReal.ofReal (C * pointConformalDensity a y (γ u) * ‖deriv γ u‖) :=
        ENNReal.ofReal_le_ofReal hn
      _ = _ := by
        rw [ENNReal.ofReal_mul (mul_nonneg hC (pointConformalDensity_nonneg a y _)),
          ENNReal.ofReal_mul hC, mul_assoc]
  apply hm.trans_eq
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  rfl

/-- For distinct points a compactly supported smooth barrier separates them, with
its physical derivative dominated by a configuration-dependent multiple of rho. -/
theorem exists_pointConformal_barrier {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z) :
    ∃ φ : ℂ → ℝ, ∃ C : ℝ, 0 < C ∧ ContDiff ℝ 1 φ ∧ φ x = 1 ∧ φ z = 0 ∧
      ∀ p, ‖fderiv ℝ φ p‖ ≤ C * pointConformalDensity a y p := by
  classical
  let F : Set ℂ := (pointPunctures a y \ {x}) ∪ {z}
  have hF : F.Finite := ((pointPunctures_finite a y).sdiff).union (finite_singleton z)
  have hx : x ∈ Fᶜ := by simp [F, hxz]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hF.isClosed.isOpen_compl.mem_nhds hx)
  let ε := r / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsub : Metric.closedBall x (2 * ε) ⊆ Fᶜ :=
    (Metric.closedBall_subset_ball (by dsimp [ε]; linarith)).trans hball
  have hz : z ∉ Metric.closedBall x (2 * ε) := fun hz ↦ hsub hz (Or.inr (mem_singleton z))
  let A := Metric.closedBall x (2 * ε) \ Metric.ball x ε
  have hA : IsCompact A := (isCompact_closedBall x (2 * ε)).diff isOpen_ball
  have hpos : ∀ p ∈ A, 0 < pointConformalDensity a y p := by
    intro p hp
    apply pointConformalDensity_pos_off_punctures ha y
    intro hpunct
    apply hsub hp.1
    left
    refine ⟨hpunct, ?_⟩
    intro hpx
    have he : p = x := mem_singleton_iff.mp hpx
    subst p
    exact hp.2 (Metric.mem_ball_self hε)
  obtain ⟨c, hc, hmin⟩ := hA.exists_forall_le'
    (pointConformalDensity_continuous ha y).continuousOn hpos
  obtain ⟨B, hB, hbound⟩ := exists_pointCutoffBump_gradient_bound
  let φ : ℂ → ℝ := pointCutoffBump x ε hε
  refine ⟨φ, (B / ε) / c, div_pos (div_pos hB hε) hc,
    (pointCutoffBump_contDiff x ε hε).of_le (by simp), ?_, ?_, ?_⟩
  · exact pointCutoffBump_one x ε hε (Metric.mem_closedBall_self hε.le)
  · apply (pointCutoffBump x ε hε).zero_of_le_dist
    exact (not_le.mp hz).le
  · intro p
    by_cases hp : p ∈ Metric.closedBall x (2 * ε)
    · by_cases hin : p ∈ Metric.ball x ε
      · have he := (pointCutoffBump x ε hε).eventuallyEq_one_of_mem_ball hin
        have hd : fderiv ℝ φ p = 0 := by
          rw [he.fderiv_eq]
          exact fderiv_const_apply 1
        rw [hd, norm_zero]
        exact mul_nonneg (div_pos (div_pos hB hε) hc).le (pointConformalDensity_nonneg a y p)
      · rw [← TauCeti.norm_gradient_eq_norm_fderiv]
        apply (hbound x ε hε p).trans
        have hm := hmin p ⟨hp, hin⟩
        calc
          B / ε = ((B / ε) / c) * c := by field_simp
          _ ≤ ((B / ε) / c) * pointConformalDensity a y p :=
            mul_le_mul_of_nonneg_left hm (div_pos (div_pos hB hε) hc).le
    · have hd : fderiv ℝ φ p = 0 :=
        fderiv_of_notMem_tsupport ℝ (by simpa [φ, pointCutoffBump_support] using hp)
      rw [hd, norm_zero]
      exact mul_nonneg (div_pos (div_pos hB hε) hc).le (pointConformalDensity_nonneg a y p)

/-- Even a puncture is at positive smooth conformal distance from every other point. -/
theorem pointSmoothConformalEDist_ne_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {x z : ℂ} (hxz : x ≠ z) :
    pointSmoothConformalEDist a y x z ≠ 0 := by
  obtain ⟨φ, C, hC, hφ, hx, hz, hb⟩ := exists_pointConformal_barrier ha y hxz
  intro hd
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hr : pointSmoothConformalEDist a y x z < (ENNReal.ofReal C)⁻¹ := by
    rw [hd]
    simp
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y hr
  have hbar := pointConformalPath_barrier a y hφ hC.le hb hγ.contDiffOn zero_le_one
  rw [h0, h1, hx, hz] at hbar
  have hmul := ENNReal.mul_lt_mul_right hC0 ENNReal.ofReal_ne_top hlen
  rw [ENNReal.mul_inv_cancel hC0 ENNReal.ofReal_ne_top] at hmul
  have hbad : (1 : ℝ≥0∞) < 1 := by simpa using hbar.trans_lt hmul
  exact (lt_irrefl _ hbad)

@[simp] theorem pointSmoothConformalEDist_eq_zero_iff {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x z : ℂ) :
    pointSmoothConformalEDist a y x z = 0 ↔ x = z := by
  constructor
  · intro h
    by_contra hne
    exact pointSmoothConformalEDist_ne_zero ha y hne h
  · rintro rfl
    exact pointSmoothConformalEDist_self a y x

end RepulsiveCoulomb
