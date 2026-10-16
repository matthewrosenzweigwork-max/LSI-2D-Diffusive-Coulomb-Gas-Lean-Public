import LeanResearch.RepulsiveCoulomb.CoulombOuterBump

/-! Outer approximants: genuine probability normalization controls tails,
and the physical gradient energy is O(radius^-2). -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem coulombOuterTestFunction_tendsto_one (N : ℕ) (z : CoulombConfig (N + 2)) :
    Tendsto (fun n ↦ coulombOuterTestFunction N n z) atTop (𝓝 1) := by
  have ht : Tendsto pointOuterRadius atTop atTop := by
    have hh : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
    change Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have he : ∀ᶠ n in atTop, coulombOuterTestFunction N n z = 1 := by
    filter_upwards [ht.eventually_ge_atTop ‖z‖] with n hn
    apply (coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n)).one_of_mem_closedBall
    simpa [mem_closedBall, dist_eq_norm, coulombOuterBump] using hn
  exact tendsto_const_nhds.congr' (he.mono fun n hn ↦ hn.symm)

theorem coulombOuterTestFunction_L2_error (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n ↦ ∫ z, (coulombOuterTestFunction N n z - 1) ^ 2 ∂coulombMeasure (N + 2) β)
      atTop (𝓝 0) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  have h := tendsto_integral_of_dominated_convergence (μ := coulombMeasure (N + 2) β)
    (F := fun n z ↦ (coulombOuterTestFunction N n z - 1) ^ 2) (f := fun _ ↦ (0 : ℝ))
    (fun _ ↦ (1 : ℝ))
    (fun n ↦ ((coulombOuterTestFunction N n).continuous.sub continuous_const).pow 2 |>.aestronglyMeasurable)
    (integrable_const 1) ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    exact Eventually.of_forall fun z ↦ by
      have h0 := (coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n)).nonneg (x := z)
      have h1 := (coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n)).le_one (x := z)
      change ‖(coulombOuterBump N (pointOuterRadius n) (pointOuterRadius_pos n) z - 1) ^ 2‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith
  · exact Eventually.of_forall fun z ↦ by
      simpa using ((coulombOuterTestFunction_tendsto_one N z).sub_const 1).pow 2

theorem coulombOuterTestFunction_energy_tendsto_zero (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n ↦ ∫ z, ‖gradient (coulombOuterTestFunction N n : CoulombConfig (N + 2) → ℝ) z‖ ^ 2
      ∂coulombMeasure (N + 2) β) atTop (𝓝 0) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  obtain ⟨B, hB, hb⟩ := coulombOuterBump_gradient_bound N
  apply squeeze_zero (g := fun n ↦ (B / pointOuterRadius n) ^ 2)
    (fun n ↦ integral_nonneg fun z ↦ sq_nonneg _)
  · intro n
    have hi : Integrable (fun z => ‖gradient (coulombOuterTestFunction N n : CoulombConfig (N + 2) → ℝ) z‖ ^ 2)
        (coulombMeasure (N + 2) β) := by
      have hm : MemLp (gradient (coulombOuterTestFunction N n : CoulombConfig (N + 2) → ℝ)) 2
          (coulombMeasure (N + 2) β) :=
        (TauCeti.continuous_gradient_testFunction (coulombOuterTestFunction N n)).memLp_of_hasCompactSupport
          (TauCeti.hasCompactSupport_gradient_testFunction (coulombOuterTestFunction N n))
      exact hm.norm.integrable_sq
    have h := integral_mono hi (integrable_const ((B / pointOuterRadius n) ^ 2))
      (fun z ↦ pow_le_pow_left₀ (norm_nonneg _) (hb (pointOuterRadius n) (pointOuterRadius_pos n) z) 2)
    simpa [coulombOuterTestFunction] using h
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul B
    simpa [pointOuterRadius, div_eq_mul_inv] using h.pow 2

end RepulsiveCoulomb
