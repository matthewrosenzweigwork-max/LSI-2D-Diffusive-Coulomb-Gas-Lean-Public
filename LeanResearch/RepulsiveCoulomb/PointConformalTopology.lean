module

public import LeanResearch.RepulsiveCoulomb.PointConformalMetricSpace

@[expose] public section

/-! Local cutoff barriers for comparison of the smooth conformal metric topology
with the original Euclidean topology. Constants here may depend on configuration. -/
noncomputable section
open MeasureTheory Set Metric Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem exists_pointConformal_neighborhood_barrier {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {U : Set ℂ}
    (hU : IsOpen U) {x : ℂ} (hxU : x ∈ U) :
    ∃ φ : ℂ → ℝ, ∃ C : ℝ, 0 < C ∧ ContDiff ℝ 1 φ ∧ φ x = 1 ∧ (∀ z ∉ U, φ z = 0) ∧
      ∀ p, ‖fderiv ℝ φ p‖ ≤ C * pointConformalDensity a y p := by
  classical
  let F : Set ℂ := (pointPunctures a y \ {x}) ∪ Uᶜ
  have hF : IsClosed F := ((pointPunctures_finite a y).sdiff.isClosed).union hU.isClosed_compl
  have hx : x ∈ Fᶜ := by simp [F, hxU]
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hF.isOpen_compl.mem_nhds hx)
  let ε := r / 4
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hsub : Metric.closedBall x (2 * ε) ⊆ Fᶜ :=
    (Metric.closedBall_subset_ball (by dsimp [ε]; linarith)).trans hball
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
  · intro z hzU
    have hz : z ∉ Metric.closedBall x (2 * ε) := fun hz ↦ hsub hz (Or.inr hzU)
    apply (pointCutoffBump x ε hε).zero_of_le_dist
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


theorem pointConformal_ball_subset_open {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {U : Set ℂ}
    (hU : IsOpen U) {x : ℂ} (hx : x ∈ U) :
    ∃ r : ℝ≥0∞, 0 < r ∧ ∀ z, pointSmoothConformalEDist a y x z < r → z ∈ U := by
  obtain ⟨φ, C, hC, hφ, hxφ, hzero, hb⟩ := exists_pointConformal_neighborhood_barrier ha y hU hx
  refine ⟨(ENNReal.ofReal C)⁻¹, by simp, ?_⟩
  intro z hdist
  by_contra hz
  obtain ⟨γ, h0, h1, hγ, hlen⟩ := exists_smooth_path_lt_pointConformalEDist a y hdist
  have hbar := pointConformalPath_barrier a y hφ hC.le hb hγ.contDiffOn zero_le_one
  rw [h0, h1, hxφ, hzero z hz] at hbar
  have hC0 : ENNReal.ofReal C ≠ 0 := (ENNReal.ofReal_pos.mpr hC).ne'
  have hmul := ENNReal.mul_lt_mul_right hC0 ENNReal.ofReal_ne_top hlen
  rw [ENNReal.mul_inv_cancel hC0 ENNReal.ofReal_ne_top] at hmul
  have hbad : (1 : ℝ≥0∞) < 1 := by simpa using hbar.trans_lt hmul
  exact lt_irrefl _ hbad

theorem rawPointBallFactor_mono_radius {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ) {r R : ℝ}
    (hr : 0 ≤ r) (hR : r ≤ R) : rawPointBallFactor a y x r ≤ rawPointBallFactor a y x R := by
  apply Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg (by positivity) _)
  intro j _
  exact Real.rpow_le_rpow (by positivity) (by linarith) (ha j)

theorem pointSmoothConformalEDist_tendsto_zero {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (x : ℂ) :
    Tendsto (fun z ↦ pointSmoothConformalEDist a y x z) (𝓝 x) (𝓝 0) := by
  let C := ENNReal.ofReal (Real.sqrt (rawPointBallFactor a y x 1))
  have hl : Tendsto (fun z : ℂ ↦ ENNReal.ofReal ‖z - x‖) (𝓝 x) (𝓝 0) := by
    have hn : Continuous (fun z : ℂ ↦ ‖z - x‖) := by fun_prop
    simpa [Function.comp_def] using (ENNReal.continuous_ofReal.comp hn).tendsto x
  have hu : Tendsto (fun z : ℂ ↦ C * ENNReal.ofReal ‖z - x‖) (𝓝 x) (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_mul hl (Or.inr (by simp [C]))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Eventually.of_forall fun _ ↦ bot_le)

  filter_upwards [Metric.ball_mem_nhds x zero_lt_one] with z hz
  have hnorm : ‖z - x‖ ≤ 1 := (by simpa [mem_ball, dist_eq_norm] using hz : ‖z - x‖ < 1).le
  apply (pointSmoothConformalEDist_segment_upper ha y x z).trans
  apply mul_le_mul' _ le_rfl
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt
    (rawPointBallFactor_mono_radius ha y x (norm_nonneg _) hnorm))

theorem isOpen_iff_pointConformal_balls {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (U : Set ℂ) :
    IsOpen U ↔ ∀ x ∈ U, ∃ r : ℝ≥0∞, 0 < r ∧
      ∀ z, pointSmoothConformalEDist a y x z < r → z ∈ U := by
  constructor
  · intro hU x hx
    exact pointConformal_ball_subset_open ha y hU hx
  · intro h
    apply isOpen_iff_mem_nhds.mpr
    intro x hx
    obtain ⟨r, hr, hsub⟩ := h x hx
    have he : ∀ᶠ z in 𝓝 x, pointSmoothConformalEDist a y x z < r :=
      (pointSmoothConformalEDist_tendsto_zero ha y x).eventually (eventually_lt_nhds hr)
    exact mem_of_superset he hsub

/-- The auxiliary smooth conformal metric has exactly the Euclidean open sets. -/
theorem pointSmoothConformalMetricSpace_topology {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    (pointSmoothConformalMetricSpace ha y).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace ℂ) := by
  ext U
  have he := @EMetric.isOpen_iff ℂ U
    (pointSmoothConformalEMetricSpace ha y).toPseudoEMetricSpace
  rw [he]
  rw [isOpen_iff_pointConformal_balls ha y U]
  change (∀ x ∈ U, ∃ r : ℝ≥0∞, 0 < r ∧
    ∀ z, pointSmoothConformalEDist a y z x < r → z ∈ U) ↔ _
  simp_rw [pointSmoothConformalEDist_comm a y]

end RepulsiveCoulomb
