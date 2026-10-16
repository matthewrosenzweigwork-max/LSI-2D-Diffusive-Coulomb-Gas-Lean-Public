import LeanResearch.RepulsiveCoulomb.PointAmbientCore

/-! Smooth outer cutoffs for the normalized Gaussian point measure. Its proved
finite normalization permits dominated convergence for radial tails and the
inverse-radius gradient estimate. No change to the Dirichlet form is made. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def pointOuterRadius (n : ℕ) : ℝ := (n : ℝ) + 1

theorem pointOuterRadius_pos (n : ℕ) : 0 < pointOuterRadius n := by
  unfold pointOuterRadius
  positivity

def pointOuterTestFunction (n : ℕ) : TestFunction (⊤ : Opens ℂ) ℝ ⊤ :=
  pointCutoffTestFunction 0 (pointOuterRadius n) (pointOuterRadius_pos n)

theorem pointOuterTestFunction_tendsto_one (z : ℂ) :
    Tendsto (fun n ↦ pointOuterTestFunction n z) atTop (𝓝 1) := by
  have ht : Tendsto pointOuterRadius atTop atTop := by
    have hh : Tendsto (fun n : ℕ ↦ ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      (tendsto_add_atTop_iff_nat 1).2 tendsto_natCast_atTop_atTop
    change Tendsto (fun n : ℕ ↦ (n : ℝ) + 1) atTop atTop
    simpa only [Nat.cast_add, Nat.cast_one] using hh
  have he : ∀ᶠ n in atTop, pointOuterTestFunction n z = 1 := by
    filter_upwards [ht.eventually_ge_atTop ‖z‖] with n hn
    apply pointCutoffBump_one
    simpa [mem_closedBall, dist_eq_norm] using hn
  exact tendsto_const_nhds.congr' (he.mono fun n hn ↦ hn.symm)

theorem pointOuterTestFunction_L2_error {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    Tendsto (fun n ↦ ∫ z, (pointOuterTestFunction n z - 1) ^ 2 ∂pointMeasure γ a y)
      atTop (𝓝 0) := by
  let _ := pointMeasure_isProbability hγ ha y
  have h := tendsto_integral_of_dominated_convergence (μ := pointMeasure γ a y)
    (F := fun n z ↦ (pointOuterTestFunction n z - 1) ^ 2) (f := fun _ ↦ (0 : ℝ))
    (fun _ ↦ (1 : ℝ))
    (fun n ↦ ((pointOuterTestFunction n).continuous.sub continuous_const).pow 2 |>.aestronglyMeasurable)
    (integrable_const 1) ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    exact Eventually.of_forall fun z ↦ by
      have h0 := (pointCutoffBump 0 (pointOuterRadius n) (pointOuterRadius_pos n)).nonneg (x := z)
      have h1 := (pointCutoffBump 0 (pointOuterRadius n) (pointOuterRadius_pos n)).le_one (x := z)
      change ‖(pointCutoffBump 0 (pointOuterRadius n) (pointOuterRadius_pos n) z - 1) ^ 2‖ ≤ 1
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith
  · exact Eventually.of_forall fun z ↦ by
      simpa using ((pointOuterTestFunction_tendsto_one z).sub_const 1).pow 2

theorem pointOuterTestFunction_energy_tendsto_zero {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    Tendsto (fun n ↦ ∫ z, ‖gradient (pointOuterTestFunction n : ℂ → ℝ) z‖ ^ 2
      ∂pointMeasure γ a y) atTop (𝓝 0) := by
  let _ := pointMeasure_isProbability hγ ha y
  obtain ⟨B, hB, hb⟩ := exists_pointCutoffBump_gradient_bound
  apply squeeze_zero (g := fun n ↦ (B / pointOuterRadius n) ^ 2)
    (fun n ↦ integral_nonneg fun z ↦ sq_nonneg _)
  · intro n
    have hi := pointCutoff_energy_integrable hγ ha y 0 (pointOuterRadius n) (pointOuterRadius_pos n)
    have h := integral_mono hi (integrable_const ((B / pointOuterRadius n) ^ 2))
      (fun z ↦ pow_le_pow_left₀ (norm_nonneg _) (hb 0 (pointOuterRadius n) (pointOuterRadius_pos n) z) 2)
    simpa [pointOuterTestFunction, pointCutoffTestFunction] using h
  · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul B
    simpa [pointOuterRadius, div_eq_mul_inv] using h.pow 2

end RepulsiveCoulomb
