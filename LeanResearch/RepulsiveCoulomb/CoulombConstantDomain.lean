import LeanResearch.RepulsiveCoulomb.CoulombOuterCutoff

/-! The constant function belongs to the full closed weighted form domain. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem coulombJet_tendsto_of_components (N : ℕ) {β : ℝ}
    (J : ℕ → CoulombJetL2 (N + 2) β) (V : CoulombJetL2 (N + 2) β)
    (hv : Tendsto (fun n ↦ coulombJetValueL (N + 2) β (J n)) atTop (𝓝 (coulombJetValueL (N + 2) β V)))
    (hg : Tendsto (fun n ↦ coulombJetGradientL (N + 2) β (J n)) atTop (𝓝 (coulombJetGradientL (N + 2) β V))) :
    Tendsto J atTop (𝓝 V) := by
  have hvs := (tendsto_iff_norm_sub_tendsto_zero.mp hv).pow 2
  have hgs := (tendsto_iff_norm_sub_tendsto_zero.mp hg).pow 2
  have he (n : ℕ) : ‖J n - V‖ ^ 2 =
      ‖coulombJetValueL (N + 2) β (J n) - coulombJetValueL (N + 2) β V‖ ^ 2 +
      ‖coulombJetGradientL (N + 2) β (J n) - coulombJetGradientL (N + 2) β V‖ ^ 2 := by
    rw [coulombJet_norm_sq, map_sub, map_sub]
  have hs : Tendsto (fun n ↦ ‖J n - V‖ ^ 2) atTop (𝓝 0) := by
    simpa only [he, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add] using hvs.add hgs
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto 0).comp hs
  change Tendsto (fun n ↦ Real.sqrt (‖J n - V‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at ht
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

def coulombConstantJet (N : ℕ) {β : ℝ} (hβ : 0 < β) : CoulombJetL2 (N + 2) β := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  exact (memLp_const (WithLp.toLp 2 ((1 : ℝ), (0 : CoulombConfig (N + 2))))).toLp _

theorem coulombConstantJet_coe (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombConstantJet N hβ =ᵐ[coulombMeasure (N + 2) β]
      (fun _ ↦ WithLp.toLp 2 ((1 : ℝ), (0 : CoulombConfig (N + 2)))) := by
  unfold coulombConstantJet
  exact MemLp.coeFn_toLp _

theorem coulombConstantJet_value (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombJetValueL (N + 2) β (coulombConstantJet N hβ) =ᵐ[coulombMeasure (N + 2) β] (fun _ ↦ (1 : ℝ)) := by
  filter_upwards [coulombJetValueL_coe (N + 2) β (coulombConstantJet N hβ),
    coulombConstantJet_coe N hβ] with z hv hj
  simpa only [hj, WithLp.toLp_fst] using hv

theorem coulombConstantJet_gradient (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombJetGradientL (N + 2) β (coulombConstantJet N hβ) =ᵐ[coulombMeasure (N + 2) β] (fun _ ↦ (0 : CoulombConfig (N + 2))) := by
  filter_upwards [coulombJetGradientL_coe (N + 2) β (coulombConstantJet N hβ),
    coulombConstantJet_coe N hβ] with z hg hj
  simpa only [hj, WithLp.toLp_snd] using hg

theorem coulombOuterJet_tendsto_constant (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    Tendsto (fun n ↦ coulombAmbientJet N hβ (coulombOuterTestFunction N n))
      atTop (𝓝 (coulombConstantJet N hβ)) := by
  apply coulombJet_tendsto_of_components N
  · apply coulomb_L2_tendsto_of_sq_integral N
    convert coulombOuterTestFunction_L2_error N hβ using 1
    ext n
    apply integral_congr_ae
    filter_upwards [coulombAmbientJet_value N hβ (coulombOuterTestFunction N n),
      coulombConstantJet_value N hβ] with z hz hvz
    simp only [hz, hvz, Real.norm_eq_abs, sq_abs]
  · apply coulomb_L2_tendsto_of_sq_integral N
    convert coulombOuterTestFunction_energy_tendsto_zero N hβ using 1
    ext n
    apply integral_congr_ae
    filter_upwards [coulombAmbientJet_gradient N hβ (coulombOuterTestFunction N n),
      coulombConstantJet_gradient N hβ] with z hz hvz
    simp only [hz, hvz, sub_zero]

theorem coulombConstantJet_mem_closedCore (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombConstantJet N hβ ∈ coulombCoreGraph (N + 2) hβ :=
  isClosed_closure.mem_of_tendsto (coulombOuterJet_tendsto_constant N hβ)
    (Eventually.of_forall fun n ↦ coulombAmbientJet_mem_closedCore N hβ (coulombOuterTestFunction N n))

def coulombConstantForm (N : ℕ) {β : ℝ} (hβ : 0 < β) : CoulombFormDomain (N + 2) hβ :=
  ⟨coulombConstantJet N hβ, by
    change coulombConstantJet N hβ ∈ (coulombFormSubmodule (N + 2) hβ : Set _)
    rw [coe_coulombFormSubmodule]
    exact coulombConstantJet_mem_closedCore N hβ⟩

theorem coulombConstantForm_value (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombFormValueL (N + 2) hβ (coulombConstantForm N hβ) =ᵐ[coulombMeasure (N + 2) β] (fun _ ↦ (1 : ℝ)) :=
  coulombConstantJet_value N hβ

theorem coulombConstantForm_gradient (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombFormGradientL (N + 2) hβ (coulombConstantForm N hβ) = 0 := by
  apply Lp.ext
  filter_upwards [coulombConstantJet_gradient N hβ, Lp.coeFn_zero (CoulombConfig (N + 2)) 2 (coulombMeasure (N + 2) β)] with z hz hzero
  change coulombJetGradientL (N + 2) β (coulombConstantJet N hβ) z = (0 : Lp (CoulombConfig (N + 2)) 2 (coulombMeasure (N + 2) β)) z
  rw [hz, hzero]
  rfl

theorem coulombConstantForm_energy (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    coulombFormEnergy (N + 2) hβ (coulombConstantForm N hβ) = 0 := by
  rw [coulombFormEnergy, coulombConstantForm_gradient, norm_zero, zero_pow (by norm_num)]

end RepulsiveCoulomb
