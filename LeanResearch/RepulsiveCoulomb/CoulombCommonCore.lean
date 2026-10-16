import LeanResearch.RepulsiveCoulomb.CoulombFiniteCutoffEnergy

/-! Common-core approximation, retaining the actual weighted Euclidean gradient. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

/-- Dominated convergence for the bounded finite-puncture avoidance factors. -/
theorem coulombAvoidance_weighted_error_tendsto_zero (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (w : CoulombConfig (N + 2) → ℝ) (hw : Integrable w (coulombMeasure (N + 2) β)) (hw0 : ∀ z, 0 ≤ w z)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, (1 - coulombAvoidanceCutoff (N + 2) (ε n) (hε n) z) ^ 2 * w z
      ∂coulombMeasure (N + 2) β) atTop (𝓝 0) := by
  have havoid : ∀ᵐ z ∂coulombMeasure (N + 2) β, z ∈ coulombDomain (N + 2) :=
    (coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae (N + 2))
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z ↦ (1 - coulombAvoidanceCutoff (N + 2) (ε n) (hε n) z) ^ 2 * w z)
      (coulombMeasure (N + 2) β) := by
    have hc : Continuous (fun z ↦ (1 - coulombAvoidanceCutoff (N + 2) (ε n) (hε n) z) ^ 2) :=
      (continuous_const.sub (coulombAvoidanceCutoff_contDiff (N + 2) (ε n) (hε n)).continuous).pow 2
    exact hc.aestronglyMeasurable.mul hw.aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ z ∂coulombMeasure (N + 2) β,
      ‖(1 - coulombAvoidanceCutoff (N + 2) (ε n) (hε n) z) ^ 2 * w z‖ ≤ w z := by
    exact Eventually.of_forall fun z ↦ by
      have h0 := coulombAvoidanceCutoff_nonneg (N + 2) (ε n) (hε n) z
      have h1 := coulombAvoidanceCutoff_le_one (N + 2) (ε n) (hε n) z
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hw0 z))]
      have hs : (1 - coulombAvoidanceCutoff (N + 2) (ε n) (hε n) z) ^ 2 ≤ 1 := by nlinarith
      exact mul_le_of_le_one_left (hw0 z) hs
  have hl : ∀ᵐ z ∂coulombMeasure (N + 2) β,
      Tendsto (fun n ↦ (1 - coulombAvoidanceCutoff (N + 2) (ε n) (hε n) z) ^ 2 * w z)
        atTop (𝓝 0) := by
    filter_upwards [havoid] with z hz
    have ht : Tendsto (fun n ↦ 1 - coulombAvoidanceCutoff (N + 2) (ε n) (hε n) z)
        atTop (𝓝 (1 - 1)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
        (coulombAvoidanceCutoff_tendsto_one z hz ε hε hlim)
    simpa using (ht.pow 2).mul_const (w z)
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence (f := fun _ ↦ (0 : ℝ)) w hm hw hb hl)

theorem coulombAvoidanceTestFunction_L2_error (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, (coulombAvoidanceTestFunction (N + 2) (ε n) (hε n) φ z - φ z) ^ 2
      ∂coulombMeasure (N + 2) β) atTop (𝓝 0) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  have hs : HasCompactSupport (fun z : CoulombConfig (N + 2) ↦ (φ z) ^ 2) := by
    convert (φ.hasCompactSupport.mul_right (f' := (φ : CoulombConfig (N + 2) → ℝ))) using 1
    ext z
    simp [pow_two]
  have hi : Integrable (fun z ↦ (φ z) ^ 2) (coulombMeasure (N + 2) β) :=
    (φ.continuous.pow 2).integrable_of_hasCompactSupport hs
  have h := coulombAvoidance_weighted_error_tendsto_zero N hβ
    (fun z ↦ (φ z) ^ 2) hi (fun z ↦ sq_nonneg _) ε hε hlim
  convert h using 1
  ext n
  congr 1
  funext z
  dsimp [coulombAvoidanceTestFunction]
  ring

theorem coulombAvoidanceTestFunction_gradient (N : ℕ)
    (ε : ℝ) (hε : 0 < ε) (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) (z : CoulombConfig (N + 2)) :
    gradient (coulombAvoidanceTestFunction (N + 2) ε hε φ : CoulombConfig (N + 2) → ℝ) z =
      φ z • gradient (coulombAvoidanceCutoff (N + 2) ε hε) z +
      coulombAvoidanceCutoff (N + 2) ε hε z • gradient (φ : CoulombConfig (N + 2) → ℝ) z := by
  apply (InnerProductSpace.toDual ℝ (CoulombConfig (N + 2))).injective
  simp only [toDual_gradient, map_add, map_smul]
  exact fderiv_fun_mul (φ.contDiff.differentiable (by simp) z)
    ((coulombAvoidanceCutoff_contDiff (N + 2) ε hε).differentiable (by simp) z)

theorem coulombAvoidanceTestFunction_gradient_error_bound (N : ℕ) (ε : ℝ) (hε : 0 < ε)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) (z : CoulombConfig (N + 2)) :
    ‖gradient (coulombAvoidanceTestFunction (N + 2) ε hε φ : CoulombConfig (N + 2) → ℝ) z - gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2 ≤
      2 * (φ z) ^ 2 * ‖gradient (coulombAvoidanceCutoff (N + 2) ε hε) z‖ ^ 2 +
      2 * (1 - coulombAvoidanceCutoff (N + 2) ε hε z) ^ 2 * ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2 := by
  rw [coulombAvoidanceTestFunction_gradient]
  have heq : φ z • gradient (coulombAvoidanceCutoff (N + 2) ε hε) z +
      coulombAvoidanceCutoff (N + 2) ε hε z • gradient (φ : CoulombConfig (N + 2) → ℝ) z - gradient (φ : CoulombConfig (N + 2) → ℝ) z =
      φ z • gradient (coulombAvoidanceCutoff (N + 2) ε hε) z +
      (coulombAvoidanceCutoff (N + 2) ε hε z - 1) • gradient (φ : CoulombConfig (N + 2) → ℝ) z := by
    rw [sub_smul, one_smul, add_sub_assoc]
  rw [heq]
  have h := norm_add_le (φ z • gradient (coulombAvoidanceCutoff (N + 2) ε hε) z)
    ((coulombAvoidanceCutoff (N + 2) ε hε z - 1) • gradient (φ : CoulombConfig (N + 2) → ℝ) z)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hsq : ∀ v : ℝ, ‖v‖ ^ 2 = v ^ 2 := fun v ↦ by simp [Real.norm_eq_abs, sq_abs]
  have h1 := sq_nonneg (‖φ z • gradient (coulombAvoidanceCutoff (N + 2) ε hε) z‖ -
    ‖(coulombAvoidanceCutoff (N + 2) ε hε z - 1) • gradient (φ : CoulombConfig (N + 2) → ℝ) z‖)
  simp only [norm_smul] at hs h1
  have hφ := hsq (φ z)
  have hq := hsq (coulombAvoidanceCutoff (N + 2) ε hε z - 1)
  nlinarith

theorem coulombAvoidanceTestFunction_gradient_L2_error (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z,
      ‖gradient (coulombAvoidanceTestFunction (N + 2) (ε n) (hε n) φ : CoulombConfig (N + 2) → ℝ) z -
        gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 2) β) atTop (𝓝 0) := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  have hgc := TauCeti.continuous_gradient_testFunction φ
  have hgs := TauCeti.hasCompactSupport_gradient_testFunction φ
  have hwc : Continuous (fun z ↦ ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2) := hgc.norm.pow 2
  have hws : HasCompactSupport (fun z ↦ ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2) :=
    hgs.comp_left (g := fun v : CoulombConfig (N + 2) ↦ ‖v‖ ^ 2) (by simp)
  have hwi := hwc.integrable_of_hasCompactSupport (μ := coulombMeasure (N + 2) β) hws
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.exists_bound_of_continuousOn φ.continuous.continuousOn
  let C : ℝ := |M| + 1
  have hC : ∀ z, ‖φ z‖ ≤ C := by
    intro z
    by_cases hz : z ∈ tsupport (φ : CoulombConfig (N + 2) → ℝ)
    · exact (hM z hz).trans (by dsimp [C]; linarith [le_abs_self M])
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      dsimp [C]
      positivity
  have hlim1 := (coulombAvoidanceCutoff_energy_tendsto_zero N hβ ε hε hlim).const_mul (2 * C ^ 2)
  have hlim2 := (coulombAvoidance_weighted_error_tendsto_zero N hβ
    (fun z ↦ ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2) hwi (fun z ↦ sq_nonneg _) ε hε hlim).const_mul 2
  apply squeeze_zero (g := fun n ↦
    2 * C ^ 2 * (∫ z, ‖gradient (coulombAvoidanceCutoff (N + 2) (ε n) (hε n)) z‖ ^ 2 ∂coulombMeasure (N + 2) β) +
    2 * (∫ z, (1 - coulombAvoidanceCutoff (N + 2) (ε n) (hε n) z) ^ 2 * ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2 ∂coulombMeasure (N + 2) β))
    (fun n ↦ integral_nonneg fun z ↦ sq_nonneg _)
  · intro n
    let q := coulombAvoidanceCutoff (N + 2) (ε n) (hε n)
    let ψ := coulombAvoidanceTestFunction (N + 2) (ε n) (hε n) φ
    have herrc : Continuous (fun z ↦ ‖gradient (ψ : CoulombConfig (N + 2) → ℝ) z - gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2) :=
      ((TauCeti.continuous_gradient_testFunction ψ).sub hgc).norm.pow 2
    have herrs : HasCompactSupport (fun z ↦ ‖gradient (ψ : CoulombConfig (N + 2) → ℝ) z - gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2) :=
      ((TauCeti.hasCompactSupport_gradient_testFunction ψ).sub hgs).comp_left
        (g := fun v : CoulombConfig (N + 2) ↦ ‖v‖ ^ 2) (by simp)
    have herri := herrc.integrable_of_hasCompactSupport (μ := coulombMeasure (N + 2) β) herrs
    have hqc : Continuous (fun z ↦ (1 - q z) ^ 2) :=
      (continuous_const.sub (coulombAvoidanceCutoff_contDiff (N + 2) (ε n) (hε n)).continuous).pow 2
    have hterm : Integrable (fun z ↦ (1 - q z) ^ 2 * ‖gradient (φ : CoulombConfig (N + 2) → ℝ) z‖ ^ 2)
        (coulombMeasure (N + 2) β) := by
      apply (hqc.mul hwc).integrable_of_hasCompactSupport
      exact hws.mul_left
    have hright := ((coulombAvoidanceCutoff_energy_integrable N hβ (ε n) (hε n)).const_mul (2 * C ^ 2)).add
      (hterm.const_mul 2)
    have hb := integral_mono herri hright (fun z ↦ ?_)
    · simpa only [Pi.add_apply, integral_add ((coulombAvoidanceCutoff_energy_integrable N hβ (ε n) (hε n)).const_mul (2 * C ^ 2)) (hterm.const_mul 2),
        integral_const_mul] using hb
    · apply (coulombAvoidanceTestFunction_gradient_error_bound N (ε n) (hε n) φ z).trans
      have hh : (φ z) ^ 2 ≤ C ^ 2 := by
        have h := pow_le_pow_left₀ (norm_nonneg _) (hC z) 2
        simpa [Real.norm_eq_abs, sq_abs] using h
      dsimp only [q, ψ, Pi.add_apply]
      simp only [← mul_assoc]
      gcongr
  · simpa only [mul_zero, add_zero] using hlim1.add hlim2

end RepulsiveCoulomb
