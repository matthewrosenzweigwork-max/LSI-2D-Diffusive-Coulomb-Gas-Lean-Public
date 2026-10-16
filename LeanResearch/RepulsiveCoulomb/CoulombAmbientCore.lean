module

public import LeanResearch.RepulsiveCoulomb.CoulombCommonCore

@[expose] public section

/-! Ambient smooth functions are represented in the closure of the prescribed
puncture-avoiding core, with both value and physical gradient identified. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem coulomb_L2_norm_sq (N : ℕ) {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {μ : Measure (CoulombConfig (N + 2))} (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq u, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun z ↦ real_inner_self_eq_norm_sq (u z))

theorem coulomb_L2_tendsto_of_sq_integral (N : ℕ) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure (CoulombConfig (N + 2))}
    (u : ℕ → Lp E 2 μ) (v : Lp E 2 μ)
    (h : Tendsto (fun n ↦ ∫ z, ‖u n z - v z‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 v) := by
  have he (n : ℕ) : ‖u n - v‖ ^ 2 = ∫ z, ‖u n z - v z‖ ^ 2 ∂μ := by
    rw [coulomb_L2_norm_sq N]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) v] with z hz
    rw [hz]
    rfl
  have hsq : Tendsto (fun n ↦ ‖u n - v‖ ^ 2) atTop (𝓝 0) := by simpa only [he] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto 0).comp hsq
  change Tendsto (fun n ↦ Real.sqrt (‖u n - v‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at ht
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

def coulombAmbientJet (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) : CoulombJetL2 (N + 2) β := by
  let _ := coulombMeasure_isProbability (N := N + 2) hβ
  have hv : MemLp (φ : CoulombConfig (N + 2) → ℝ) 2 (coulombMeasure (N + 2) β) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hg : MemLp (fun z ↦ gradient (φ : CoulombConfig (N + 2) → ℝ) z) 2 (coulombMeasure (N + 2) β) :=
    (TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
      (TauCeti.hasCompactSupport_gradient_testFunction φ)
  have hj : MemLp (fun z ↦ WithLp.toLp 2 (φ z, gradient (φ : CoulombConfig (N + 2) → ℝ) z)) 2 (coulombMeasure (N + 2) β) := by
    apply MemLp.of_fst_of_snd_prodLp
    exact ⟨by simpa only [WithLp.toLp_fst] using hv, by simpa only [WithLp.toLp_snd] using hg⟩
  exact hj.toLp _

theorem coulombAmbientJet_coe (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) :
    coulombAmbientJet N hβ φ =ᵐ[coulombMeasure (N + 2) β]
      (fun z ↦ WithLp.toLp 2 (φ z, gradient (φ : CoulombConfig (N + 2) → ℝ) z)) := by
  unfold coulombAmbientJet
  exact MemLp.coeFn_toLp _

theorem coulombAmbientJet_value (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) :
    coulombJetValueL (N + 2) β (coulombAmbientJet N hβ φ) =ᵐ[coulombMeasure (N + 2) β] φ := by
  filter_upwards [coulombJetValueL_coe (N + 2) β (coulombAmbientJet N hβ φ),
    coulombAmbientJet_coe N hβ φ] with z hv hj
  simpa only [hj, WithLp.toLp_fst] using hv

theorem coulombAmbientJet_gradient (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) :
    coulombJetGradientL (N + 2) β (coulombAmbientJet N hβ φ) =ᵐ[coulombMeasure (N + 2) β]
      (fun z ↦ gradient (φ : CoulombConfig (N + 2) → ℝ) z) := by
  filter_upwards [coulombJetGradientL_coe (N + 2) β (coulombAmbientJet N hβ φ),
    coulombAmbientJet_coe N hβ φ] with z hg hj
  simpa only [hj, WithLp.toLp_snd] using hg

theorem coulombAvoidanceJet_tendsto (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ coulombCoreJet hβ (coulombAvoidanceTestFunction (N + 2) (ε n) (hε n) φ))
      atTop (𝓝 (coulombAmbientJet N hβ φ)) := by
  let J := fun n ↦ coulombCoreJet hβ (coulombAvoidanceTestFunction (N + 2) (ε n) (hε n) φ)
  let V := coulombAmbientJet N hβ φ
  have hv : Tendsto (fun n ↦ coulombJetValueL (N + 2) β (J n)) atTop (𝓝 (coulombJetValueL (N + 2) β V)) := by
    apply coulomb_L2_tendsto_of_sq_integral N
    convert coulombAvoidanceTestFunction_L2_error N hβ φ ε hε hlim using 1
    ext n
    apply integral_congr_ae
    filter_upwards [coulombCoreJet_value hβ (coulombAvoidanceTestFunction (N + 2) (ε n) (hε n) φ),
      coulombAmbientJet_value N hβ φ] with z hz hvz
    simp only [J, V, hz, hvz, Real.norm_eq_abs, sq_abs]
  have hg : Tendsto (fun n ↦ coulombJetGradientL (N + 2) β (J n)) atTop (𝓝 (coulombJetGradientL (N + 2) β V)) := by
    apply coulomb_L2_tendsto_of_sq_integral N
    convert coulombAvoidanceTestFunction_gradient_L2_error N hβ φ ε hε hlim using 1
    ext n
    apply integral_congr_ae
    filter_upwards [coulombCoreJet_gradient hβ (coulombAvoidanceTestFunction (N + 2) (ε n) (hε n) φ),
      coulombAmbientJet_gradient N hβ φ] with z hz hvz
    simp only [J, V, hz, hvz]
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

/-- Every ambient compactly supported smooth function belongs to the closure
of the original puncture-avoiding value/gradient graph. -/
theorem coulombAmbientJet_mem_closedCore (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) :
    coulombAmbientJet N hβ φ ∈ coulombCoreGraph (N + 2) hβ := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hp : ∀ n, 0 < ε n := fun n ↦ by dsimp [ε]; positivity
  have hl : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact isClosed_closure.mem_of_tendsto (coulombAvoidanceJet_tendsto N hβ φ ε hp hl)
    (Eventually.of_forall fun n ↦ subset_closure (mem_range_self _))

def coulombAmbientForm (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) : CoulombFormDomain (N + 2) hβ :=
  ⟨coulombAmbientJet N hβ φ, by
    change coulombAmbientJet N hβ φ ∈ (coulombFormSubmodule (N + 2) hβ : Set _)
    rw [coe_coulombFormSubmodule]
    exact coulombAmbientJet_mem_closedCore N hβ φ⟩

/-- The ambient and puncture-avoiding smooth cores have exactly the same closed
value/physical-gradient graph. -/
theorem coulomb_common_core (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    closure (range (coulombAmbientJet N hβ)) = coulombCoreGraph (N + 2) hβ := by
  apply Subset.antisymm
  · apply closure_minimal
    · rintro u ⟨φ, rfl⟩
      exact coulombAmbientJet_mem_closedCore N hβ φ
    · exact isClosed_closure
  · apply closure_mono
    rintro u ⟨φ, rfl⟩
    let ψ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤ :=
      ⟨φ, φ.contDiff, φ.hasCompactSupport, by simp⟩
    refine ⟨ψ, ?_⟩
    apply Lp.ext
    filter_upwards [coulombAmbientJet_coe N hβ ψ, coulombCoreJet_coe hβ φ]
      with z hψ hφ
    rw [hψ, hφ]
    rfl

theorem coulombAmbientForm_value (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) :
    coulombFormValueL (N + 2) hβ (coulombAmbientForm N hβ φ) =ᵐ[coulombMeasure (N + 2) β] φ :=
  coulombAmbientJet_value N hβ φ

theorem coulombAmbientForm_gradient (N : ℕ) {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (⊤ : Opens (CoulombConfig (N + 2))) ℝ ⊤) :
    coulombFormGradientL (N + 2) hβ (coulombAmbientForm N hβ φ) =ᵐ[coulombMeasure (N + 2) β]
      (fun z ↦ gradient (φ : CoulombConfig (N + 2) → ℝ) z) :=
  coulombAmbientJet_gradient N hβ φ

end RepulsiveCoulomb
