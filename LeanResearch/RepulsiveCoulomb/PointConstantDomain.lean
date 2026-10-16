import LeanResearch.RepulsiveCoulomb.PointOuterCutoff

/-! The constant function belongs to the full closed weighted form domain. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem pointJet_tendsto_of_components {m : ℕ} {γ : ℝ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (J : ℕ → PointJetL2 γ a y) (V : PointJetL2 γ a y)
    (hv : Tendsto (fun n ↦ pointJetValueL γ a y (J n)) atTop (𝓝 (pointJetValueL γ a y V)))
    (hg : Tendsto (fun n ↦ pointJetGradientL γ a y (J n)) atTop (𝓝 (pointJetGradientL γ a y V))) :
    Tendsto J atTop (𝓝 V) := by
  have hvs := (tendsto_iff_norm_sub_tendsto_zero.mp hv).pow 2
  have hgs := (tendsto_iff_norm_sub_tendsto_zero.mp hg).pow 2
  have he (n : ℕ) : ‖J n - V‖ ^ 2 =
      ‖pointJetValueL γ a y (J n) - pointJetValueL γ a y V‖ ^ 2 +
      ‖pointJetGradientL γ a y (J n) - pointJetGradientL γ a y V‖ ^ 2 := by
    rw [pointJet_norm_sq, map_sub, map_sub]
  have hs : Tendsto (fun n ↦ ‖J n - V‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using hvs.add hgs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto 0).comp hs
  change Tendsto (fun n ↦ Real.sqrt (‖J n - V‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at ht
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

def pointConstantJet {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : PointJetL2 γ a y := by
  let _ := pointMeasure_isProbability hγ ha y
  exact (memLp_const (WithLp.toLp 2 ((1 : ℝ), (0 : ℂ)))).toLp _

theorem pointConstantJet_coe {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointConstantJet hγ ha y =ᵐ[pointMeasure γ a y]
      (fun _ ↦ WithLp.toLp 2 ((1 : ℝ), (0 : ℂ))) := by
  unfold pointConstantJet
  exact MemLp.coeFn_toLp _

theorem pointConstantJet_value {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointJetValueL γ a y (pointConstantJet hγ ha y) =ᵐ[pointMeasure γ a y] (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [pointJetValueL_coe γ a y (pointConstantJet hγ ha y),
    pointConstantJet_coe hγ ha y] with z hv hj
  simpa only [hj, WithLp.toLp_fst] using hv

theorem pointConstantJet_gradient {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointJetGradientL γ a y (pointConstantJet hγ ha y) =ᵐ[pointMeasure γ a y] (fun _ ↦ (0 : ℂ)) := by
  filter_upwards [pointJetGradientL_coe γ a y (pointConstantJet hγ ha y),
    pointConstantJet_coe hγ ha y] with z hg hj
  simpa only [hj, WithLp.toLp_snd] using hg

theorem pointOuterJet_tendsto_constant {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    Tendsto (fun n ↦ pointAmbientJet hγ ha y (pointOuterTestFunction n))
      atTop (𝓝 (pointConstantJet hγ ha y)) := by
  apply pointJet_tendsto_of_components
  · apply point_L2_tendsto_of_sq_integral
    convert pointOuterTestFunction_L2_error hγ ha y using 1
    ext n
    apply integral_congr_ae
    filter_upwards [pointAmbientJet_value hγ ha y (pointOuterTestFunction n),
      pointConstantJet_value hγ ha y] with z hz hvz
    simp only [hz, hvz, Real.norm_eq_abs, sq_abs]
  · apply point_L2_tendsto_of_sq_integral
    convert pointOuterTestFunction_energy_tendsto_zero hγ ha y using 1
    ext n
    apply integral_congr_ae
    filter_upwards [pointAmbientJet_gradient hγ ha y (pointOuterTestFunction n),
      pointConstantJet_gradient hγ ha y] with z hz hvz
    simp only [hz, hvz, sub_zero]

theorem pointConstantJet_mem_closedCore {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointConstantJet hγ ha y ∈ pointCoreGraph hγ ha y :=
  isClosed_closure.mem_of_tendsto (pointOuterJet_tendsto_constant hγ ha y)
    (Eventually.of_forall fun n ↦ pointAmbientJet_mem_closedCore hγ ha y (pointOuterTestFunction n))

def pointConstantForm {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) : PointFormDomain hγ ha y :=
  ⟨pointConstantJet hγ ha y, by
    change pointConstantJet hγ ha y ∈ (pointFormSubmodule hγ ha y : Set _)
    rw [coe_pointFormSubmodule]
    exact pointConstantJet_mem_closedCore hγ ha y⟩

theorem pointConstantForm_value {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointFormValueL hγ ha y (pointConstantForm hγ ha y) =ᵐ[pointMeasure γ a y] (fun _ ↦ (1 : ℝ)) :=
  pointConstantJet_value hγ ha y

theorem pointConstantForm_gradient {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointFormGradientL hγ ha y (pointConstantForm hγ ha y) = 0 := by
  apply Lp.ext
  filter_upwards [pointConstantJet_gradient hγ ha y, Lp.coeFn_zero ℂ 2 (pointMeasure γ a y)] with z hz hzero
  change pointJetGradientL γ a y (pointConstantJet hγ ha y) z = (0 : Lp ℂ 2 (pointMeasure γ a y)) z
  rw [hz, hzero]
  rfl

theorem pointConstantForm_energy {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    pointFormEnergy hγ ha y (pointConstantForm hγ ha y) = 0 := by
  rw [pointFormEnergy, pointConstantForm_gradient, norm_zero, zero_pow (by norm_num)]

end RepulsiveCoulomb
