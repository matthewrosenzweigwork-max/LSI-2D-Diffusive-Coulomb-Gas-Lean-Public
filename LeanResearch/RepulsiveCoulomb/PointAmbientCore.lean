import LeanResearch.RepulsiveCoulomb.PointCommonCore

/-! Ambient smooth functions are represented in the closure of the prescribed
puncture-avoiding core, with both value and physical gradient identified. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem point_L2_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {μ : Measure ℂ} (u : Lp E 2 μ) :
    ‖u‖ ^ 2 = ∫ z, ‖u z‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq u, L2.inner_def]
  exact integral_congr_ae (Eventually.of_forall fun z ↦ real_inner_self_eq_norm_sq (u z))

theorem point_L2_tendsto_of_sq_integral {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] {μ : Measure ℂ}
    (u : ℕ → Lp E 2 μ) (v : Lp E 2 μ)
    (h : Tendsto (fun n ↦ ∫ z, ‖u n z - v z‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 v) := by
  have he (n : ℕ) : ‖u n - v‖ ^ 2 = ∫ z, ‖u n z - v z‖ ^ 2 ∂μ := by
    rw [point_L2_norm_sq]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (u n) v] with z hz
    rw [hz]
    rfl
  have hsq : Tendsto (fun n ↦ ‖u n - v‖ ^ 2) atTop (𝓝 0) := by simpa only [he] using h
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have ht := (Real.continuous_sqrt.tendsto 0).comp hsq
  change Tendsto (fun n ↦ Real.sqrt (‖u n - v‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) at ht
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using ht

def pointAmbientJet {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) : PointJetL2 γ a y := by
  let _ := pointMeasure_isProbability hγ ha y
  have hv : MemLp (φ : ℂ → ℝ) 2 (pointMeasure γ a y) :=
    φ.continuous.memLp_of_hasCompactSupport φ.hasCompactSupport
  have hg : MemLp (fun z ↦ gradient (φ : ℂ → ℝ) z) 2 (pointMeasure γ a y) :=
    (TauCeti.continuous_gradient_testFunction φ).memLp_of_hasCompactSupport
      (TauCeti.hasCompactSupport_gradient_testFunction φ)
  have hj : MemLp (fun z ↦ WithLp.toLp 2 (φ z, gradient (φ : ℂ → ℝ) z)) 2 (pointMeasure γ a y) := by
    apply MemLp.of_fst_of_snd_prodLp
    exact ⟨by simpa only [WithLp.toLp_fst] using hv, by simpa only [WithLp.toLp_snd] using hg⟩
  exact hj.toLp _

theorem pointAmbientJet_coe {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    pointAmbientJet hγ ha y φ =ᵐ[pointMeasure γ a y]
      (fun z ↦ WithLp.toLp 2 (φ z, gradient (φ : ℂ → ℝ) z)) := by
  unfold pointAmbientJet
  exact MemLp.coeFn_toLp _

theorem pointAmbientJet_value {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    pointJetValueL γ a y (pointAmbientJet hγ ha y φ) =ᵐ[pointMeasure γ a y] φ := by
  filter_upwards [pointJetValueL_coe γ a y (pointAmbientJet hγ ha y φ),
    pointAmbientJet_coe hγ ha y φ] with z hv hj
  simpa only [hj, WithLp.toLp_fst] using hv

theorem pointAmbientJet_gradient {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    pointJetGradientL γ a y (pointAmbientJet hγ ha y φ) =ᵐ[pointMeasure γ a y]
      (fun z ↦ gradient (φ : ℂ → ℝ) z) := by
  filter_upwards [pointJetGradientL_coe γ a y (pointAmbientJet hγ ha y φ),
    pointAmbientJet_coe hγ ha y φ] with z hg hj
  simpa only [hj, WithLp.toLp_snd] using hg

theorem pointAvoidanceJet_tendsto {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ pointCoreJet hγ ha y (pointAvoidanceTestFunction a y (ε n) (hε n) φ))
      atTop (𝓝 (pointAmbientJet hγ ha y φ)) := by
  let J := fun n ↦ pointCoreJet hγ ha y (pointAvoidanceTestFunction a y (ε n) (hε n) φ)
  let V := pointAmbientJet hγ ha y φ
  have hv : Tendsto (fun n ↦ pointJetValueL γ a y (J n)) atTop (𝓝 (pointJetValueL γ a y V)) := by
    apply point_L2_tendsto_of_sq_integral
    convert pointAvoidanceTestFunction_L2_error hγ ha y φ ε hε hlim using 1
    ext n
    apply integral_congr_ae
    filter_upwards [pointCoreJet_value hγ ha y (pointAvoidanceTestFunction a y (ε n) (hε n) φ),
      pointAmbientJet_value hγ ha y φ] with z hz hvz
    simp only [J, V, hz, hvz, Real.norm_eq_abs, sq_abs]
  have hg : Tendsto (fun n ↦ pointJetGradientL γ a y (J n)) atTop (𝓝 (pointJetGradientL γ a y V)) := by
    apply point_L2_tendsto_of_sq_integral
    convert pointAvoidanceTestFunction_gradient_L2_error hγ ha y φ ε hε hlim using 1
    ext n
    apply integral_congr_ae
    filter_upwards [pointCoreJet_gradient hγ ha y (pointAvoidanceTestFunction a y (ε n) (hε n) φ),
      pointAmbientJet_gradient hγ ha y φ] with z hz hvz
    simp only [J, V, hz, hvz]
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

/-- Every ambient compactly supported smooth function belongs to the closure
of the original puncture-avoiding value/gradient graph. -/
theorem pointAmbientJet_mem_closedCore {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    pointAmbientJet hγ ha y φ ∈ pointCoreGraph hγ ha y := by
  let ε : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  have hp : ∀ n, 0 < ε n := fun n ↦ by dsimp [ε]; positivity
  have hl : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  exact isClosed_closure.mem_of_tendsto (pointAvoidanceJet_tendsto hγ ha y φ ε hp hl)
    (Eventually.of_forall fun n ↦ subset_closure (mem_range_self _))

def pointAmbientForm {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) : PointFormDomain hγ ha y :=
  ⟨pointAmbientJet hγ ha y φ, by
    change pointAmbientJet hγ ha y φ ∈ (pointFormSubmodule hγ ha y : Set _)
    rw [coe_pointFormSubmodule]
    exact pointAmbientJet_mem_closedCore hγ ha y φ⟩

/-- The ambient and puncture-avoiding smooth cores have exactly the same closed
value/physical-gradient graph. -/
theorem point_common_core {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) :
    closure (range (pointAmbientJet hγ ha y)) = pointCoreGraph hγ ha y := by
  apply Subset.antisymm
  · apply closure_minimal
    · rintro u ⟨φ, rfl⟩
      exact pointAmbientJet_mem_closedCore hγ ha y φ
    · exact isClosed_closure
  · apply closure_mono
    rintro u ⟨φ, rfl⟩
    let ψ : TestFunction (⊤ : Opens ℂ) ℝ ⊤ :=
      ⟨φ, φ.contDiff, φ.hasCompactSupport, by simp⟩
    refine ⟨ψ, ?_⟩
    apply Lp.ext
    filter_upwards [pointAmbientJet_coe hγ ha y ψ, pointCoreJet_coe hγ ha y φ]
      with z hψ hφ
    rw [hψ, hφ]
    rfl

theorem pointAmbientForm_value {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    pointFormValueL hγ ha y (pointAmbientForm hγ ha y φ) =ᵐ[pointMeasure γ a y] φ :=
  pointAmbientJet_value hγ ha y φ

theorem pointAmbientForm_gradient {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (φ : TestFunction (⊤ : Opens ℂ) ℝ ⊤) :
    pointFormGradientL hγ ha y (pointAmbientForm hγ ha y φ) =ᵐ[pointMeasure γ a y]
      (fun z ↦ gradient (φ : ℂ → ℝ) z) :=
  pointAmbientJet_gradient hγ ha y φ

end RepulsiveCoulomb
