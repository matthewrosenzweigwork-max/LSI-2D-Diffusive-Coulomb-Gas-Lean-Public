import LeanResearch.RepulsiveCoulomb.PointFiniteCutoff

/-! Common-core approximation, retaining the actual weighted Euclidean gradient. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

/-- Dominated convergence for the bounded finite-puncture avoidance factors. -/
theorem pointAvoidance_weighted_error_tendsto_zero {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (w : ℂ → ℝ) (hw : Integrable w (pointMeasure γ a y)) (hw0 : ∀ z, 0 ≤ w z)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, (1 - pointAvoidanceCutoff a y (ε n) (hε n) z) ^ 2 * w z
      ∂pointMeasure γ a y) atTop (𝓝 0) := by
  have havoid : ∀ᵐ z ∂pointMeasure γ a y, z ∉ pointPunctures a y := by
    apply (pointMeasure_ae_iff hγ ha y).mpr
    filter_upwards [ae_all_iff.mpr (fun j : Fin m ↦ volume.ae_ne (y j))] with z hz
    rintro ⟨j, _, he⟩
    exact hz j he
  have hm (n : ℕ) : AEStronglyMeasurable
      (fun z ↦ (1 - pointAvoidanceCutoff a y (ε n) (hε n) z) ^ 2 * w z)
      (pointMeasure γ a y) := by
    have hc : Continuous (fun z ↦ (1 - pointAvoidanceCutoff a y (ε n) (hε n) z) ^ 2) :=
      (continuous_const.sub (pointAvoidanceCutoff_contDiff a y (ε n) (hε n)).continuous).pow 2
    exact hc.aestronglyMeasurable.mul hw.aestronglyMeasurable
  have hb (n : ℕ) : ∀ᵐ z ∂pointMeasure γ a y,
      ‖(1 - pointAvoidanceCutoff a y (ε n) (hε n) z) ^ 2 * w z‖ ≤ w z := by
    exact Eventually.of_forall fun z ↦ by
      have h0 := pointAvoidanceCutoff_nonneg a y (ε n) (hε n) z
      have h1 := pointAvoidanceCutoff_le_one a y (ε n) (hε n) z
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hw0 z))]
      have hs : (1 - pointAvoidanceCutoff a y (ε n) (hε n) z) ^ 2 ≤ 1 := by nlinarith
      exact mul_le_of_le_one_left (hw0 z) hs
  have hl : ∀ᵐ z ∂pointMeasure γ a y,
      Tendsto (fun n ↦ (1 - pointAvoidanceCutoff a y (ε n) (hε n) z) ^ 2 * w z)
        atTop (𝓝 0) := by
    filter_upwards [havoid] with z hz
    have ht : Tendsto (fun n ↦ 1 - pointAvoidanceCutoff a y (ε n) (hε n) z)
        atTop (𝓝 (1 - 1)) :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1)).sub
        (pointAvoidanceCutoff_tendsto_one a y ε hε hlim hz)
    simpa using (ht.pow 2).mul_const (w z)
  simpa only [integral_zero] using
    (tendsto_integral_of_dominated_convergence (f := fun _ ↦ (0 : ℝ)) w hm hw hb hl)

theorem pointAvoidanceTestFunction_L2_error {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, (pointAvoidanceTestFunction a y (ε n) (hε n) φ z - φ z) ^ 2
      ∂pointMeasure γ a y) atTop (𝓝 0) := by
  let _ := pointMeasure_isProbability hγ ha y
  have hs : HasCompactSupport (fun z : ℂ ↦ (φ z) ^ 2) := by
    convert (φ.hasCompactSupport.mul_right (f' := (φ : ℂ → ℝ))) using 1
    ext z
    simp [pow_two]
  have hi : Integrable (fun z ↦ (φ z) ^ 2) (pointMeasure γ a y) :=
    (φ.continuous.pow 2).integrable_of_hasCompactSupport hs
  have h := pointAvoidance_weighted_error_tendsto_zero hγ ha y
    (fun z ↦ (φ z) ^ 2) hi (fun z ↦ sq_nonneg _) ε hε hlim
  convert h using 1
  ext n
  congr 1
  funext z
  dsimp [pointAvoidanceTestFunction]
  ring

theorem pointAvoidanceTestFunction_gradient {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ)
    (ε : ℝ) (hε : 0 < ε) (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) (z : ℂ) :
    gradient (pointAvoidanceTestFunction a y ε hε φ : ℂ → ℝ) z =
      φ z • gradient (pointAvoidanceCutoff a y ε hε) z +
      pointAvoidanceCutoff a y ε hε z • gradient (φ : ℂ → ℝ) z := by
  apply (InnerProductSpace.toDual ℝ ℂ).injective
  simp only [toDual_gradient, map_add, map_smul]
  exact fderiv_fun_mul (φ.contDiff.differentiable (by simp) z)
    ((pointAvoidanceCutoff_contDiff a y ε hε).differentiable (by simp) z)

theorem pointAvoidanceTestFunction_gradient_error_bound {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (ε : ℝ) (hε : 0 < ε)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) (z : ℂ) :
    ‖gradient (pointAvoidanceTestFunction a y ε hε φ : ℂ → ℝ) z - gradient (φ : ℂ → ℝ) z‖ ^ 2 ≤
      2 * (φ z) ^ 2 * ‖gradient (pointAvoidanceCutoff a y ε hε) z‖ ^ 2 +
      2 * (1 - pointAvoidanceCutoff a y ε hε z) ^ 2 * ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 := by
  rw [pointAvoidanceTestFunction_gradient]
  have heq : φ z • gradient (pointAvoidanceCutoff a y ε hε) z +
      pointAvoidanceCutoff a y ε hε z • gradient (φ : ℂ → ℝ) z - gradient (φ : ℂ → ℝ) z =
      φ z • gradient (pointAvoidanceCutoff a y ε hε) z +
      (pointAvoidanceCutoff a y ε hε z - 1) • gradient (φ : ℂ → ℝ) z := by
    rw [sub_smul, one_smul, add_sub_assoc]
  rw [heq]
  have h := norm_add_le (φ z • gradient (pointAvoidanceCutoff a y ε hε) z)
    ((pointAvoidanceCutoff a y ε hε z - 1) • gradient (φ : ℂ → ℝ) z)
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  have hsq : ∀ v : ℝ, ‖v‖ ^ 2 = v ^ 2 := fun v ↦ by simp [Real.norm_eq_abs, sq_abs]
  have h1 := sq_nonneg (‖φ z • gradient (pointAvoidanceCutoff a y ε hε) z‖ -
    ‖(pointAvoidanceCutoff a y ε hε z - 1) • gradient (φ : ℂ → ℝ) z‖)
  simp only [norm_smul] at hs h1
  have hφ := hsq (φ z)
  have hq := hsq (pointAvoidanceCutoff a y ε hε z - 1)
  nlinarith

theorem pointAvoidanceTestFunction_gradient_L2_error {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z,
      ‖gradient (pointAvoidanceTestFunction a y (ε n) (hε n) φ : ℂ → ℝ) z -
        gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂pointMeasure γ a y) atTop (𝓝 0) := by
  let _ := pointMeasure_isProbability hγ ha y
  have hgc := TauCeti.continuous_gradient_testFunction φ
  have hgs := TauCeti.hasCompactSupport_gradient_testFunction φ
  have hwc : Continuous (fun z ↦ ‖gradient (φ : ℂ → ℝ) z‖ ^ 2) := hgc.norm.pow 2
  have hws : HasCompactSupport (fun z ↦ ‖gradient (φ : ℂ → ℝ) z‖ ^ 2) :=
    hgs.comp_left (g := fun v : ℂ ↦ ‖v‖ ^ 2) (by simp)
  have hwi := hwc.integrable_of_hasCompactSupport (μ := pointMeasure γ a y) hws
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.exists_bound_of_continuousOn φ.continuous.continuousOn
  let C : ℝ := |M| + 1
  have hC : ∀ z, ‖φ z‖ ≤ C := by
    intro z
    by_cases hz : z ∈ tsupport (φ : ℂ → ℝ)
    · exact (hM z hz).trans (by dsimp [C]; linarith [le_abs_self M])
    · rw [image_eq_zero_of_notMem_tsupport hz, norm_zero]
      dsimp [C]
      positivity
  have hlim1 := (pointAvoidanceCutoff_energy_tendsto_zero hγ ha y ε hε hlim).const_mul (2 * C ^ 2)
  have hlim2 := (pointAvoidance_weighted_error_tendsto_zero hγ ha y
    (fun z ↦ ‖gradient (φ : ℂ → ℝ) z‖ ^ 2) hwi (fun z ↦ sq_nonneg _) ε hε hlim).const_mul 2
  apply squeeze_zero (g := fun n ↦
    2 * C ^ 2 * (∫ z, ‖gradient (pointAvoidanceCutoff a y (ε n) (hε n)) z‖ ^ 2 ∂pointMeasure γ a y) +
    2 * (∫ z, (1 - pointAvoidanceCutoff a y (ε n) (hε n) z) ^ 2 * ‖gradient (φ : ℂ → ℝ) z‖ ^ 2 ∂pointMeasure γ a y))
    (fun n ↦ integral_nonneg fun z ↦ sq_nonneg _)
  · intro n
    let q := pointAvoidanceCutoff a y (ε n) (hε n)
    let ψ := pointAvoidanceTestFunction a y (ε n) (hε n) φ
    have herrc : Continuous (fun z ↦ ‖gradient (ψ : ℂ → ℝ) z - gradient (φ : ℂ → ℝ) z‖ ^ 2) :=
      ((TauCeti.continuous_gradient_testFunction ψ).sub hgc).norm.pow 2
    have herrs : HasCompactSupport (fun z ↦ ‖gradient (ψ : ℂ → ℝ) z - gradient (φ : ℂ → ℝ) z‖ ^ 2) :=
      ((TauCeti.hasCompactSupport_gradient_testFunction ψ).sub hgs).comp_left
        (g := fun v : ℂ ↦ ‖v‖ ^ 2) (by simp)
    have herri := herrc.integrable_of_hasCompactSupport (μ := pointMeasure γ a y) herrs
    have hqc : Continuous (fun z ↦ (1 - q z) ^ 2) :=
      (continuous_const.sub (pointAvoidanceCutoff_contDiff a y (ε n) (hε n)).continuous).pow 2
    have hterm : Integrable (fun z ↦ (1 - q z) ^ 2 * ‖gradient (φ : ℂ → ℝ) z‖ ^ 2)
        (pointMeasure γ a y) := by
      apply (hqc.mul hwc).integrable_of_hasCompactSupport
      exact hws.mul_left
    have hright := ((pointAvoidanceCutoff_energy_integrable hγ ha y (ε n) (hε n)).const_mul (2 * C ^ 2)).add
      (hterm.const_mul 2)
    have hb := integral_mono herri hright (fun z ↦ ?_)
    · simpa only [Pi.add_apply, integral_add ((pointAvoidanceCutoff_energy_integrable hγ ha y (ε n) (hε n)).const_mul (2 * C ^ 2)) (hterm.const_mul 2),
        integral_const_mul] using hb
    · apply (pointAvoidanceTestFunction_gradient_error_bound a y (ε n) (hε n) φ z).trans
      have hh : (φ z) ^ 2 ≤ C ^ 2 := by
        have h := pow_le_pow_left₀ (norm_nonneg _) (hC z) 2
        simpa [Real.norm_eq_abs, sq_abs] using h
      dsimp only [q, ψ, Pi.add_apply]
      simp only [← mul_assoc]
      gcongr
  · simpa only [mul_zero, add_zero] using hlim1.add hlim2

end RepulsiveCoulomb
