import LeanResearch.RepulsiveCoulomb.CoulombLocalL2
import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.MeasureTheory.Function.Lp.ExtendByZero
import LeanResearch.RepulsiveCoulomb.Imported.TauCeti.MeasureTheory.Function.Lp.CastMeasure

/-! An actual bounded map sends global Lebesgue L2 to Gibbs L2 by restriction
to a fixed compact collision-free set and zero extension. It transfers a
common compactly supported approximation without changing representatives. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

theorem dbarCoulomb_restrict_le_volume_smul {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ (coulombMeasure N β).restrict K ≤ C • volume := by
  obtain ⟨c, C, hc, hC, hlo, hhi⟩ := coulombMeasure_restrict_comparison hβ hK hKΩ
  exact ⟨ENNReal.ofReal C, ENNReal.ofReal_ne_top,
    hhi.trans (smul_le_smul_left _ Measure.restrict_le_self)⟩

theorem dbarMeasureCompactTransfer_coe {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ ν : Measure X} {K : Set X}
    (hK : MeasurableSet K)
    (R : Lp F 2 ν →L[ℝ] Lp F 2 (μ.restrict K))
    (hR : ∀ f : Lp F 2 ν, R f =ᵐ[μ.restrict K] f) (f : Lp F 2 ν) :
    (TauCeti.castLpₗᵢ (𝕜 := ℝ) (E := F) (p := 2)
      (show μ.restrict univ = μ from Measure.restrict_univ)
      (TauCeti.extendByZeroLpₗᵢ ℝ μ hK (subset_univ K) (R f)) : X → F)
      =ᵐ[μ] K.indicator (f : X → F) := by
  have hRi := (ae_eq_restrict_iff_indicator_ae_eq hK).mp (hR f)
  have hE := TauCeti.coeFn_extendByZeroLpₗᵢ ℝ hK (subset_univ K) (R f)
  have hfilter : ae μ ≤ ae (μ.restrict univ) :=
    le_of_eq (congrArg (fun m : Measure X => ae m)
      (show μ.restrict univ = μ from Measure.restrict_univ)).symm
  have hE' := hE.filter_mono hfilter
  have hcast :
      (TauCeti.castLpₗᵢ (𝕜 := ℝ) (E := F) (p := 2)
        (show μ.restrict univ = μ from Measure.restrict_univ)
        (TauCeti.extendByZeroLpₗᵢ ℝ μ hK (subset_univ K) (R f)) : X → F)
        =ᵐ[μ] (TauCeti.extendByZeroLpₗᵢ ℝ μ hK (subset_univ K) (R f) : X → F) :=
    Eventually.of_forall fun x => TauCeti.coeFn_castLpₗᵢ _ _ x
  exact hcast.trans (hE'.trans hRi)

def dbarMeasureCompactTransferL {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ ν : Measure X} {K : Set X}
    {C : ℝ≥0∞} (hK : MeasurableSet K) (hc : C ≠ ⊤) (hle : μ.restrict K ≤ C • ν) :
    Lp F 2 ν →L[ℝ] Lp F 2 μ :=
  (Lp.LpToLpOfMeasureLeSMul ENNReal.one_ne_top
    (show μ ≤ (1 : ℝ≥0∞) • μ.restrict univ from by simp)).comp
      ((TauCeti.extendByZeroLpₗᵢ ℝ μ hK (subset_univ K)).toContinuousLinearMap.comp
        (Lp.LpToLpOfMeasureLeSMul hc hle))

theorem dbarMeasureCompactTransferL_coe {X F : Type*} [MeasurableSpace X]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {μ ν : Measure X} {K : Set X}
    {C : ℝ≥0∞} (hK : MeasurableSet K) (hc : C ≠ ⊤) (hle : μ.restrict K ≤ C • ν)
    (f : Lp F 2 ν) :
    dbarMeasureCompactTransferL hK hc hle f =ᵐ[μ] K.indicator (f : X → F) := by
  let R : Lp F 2 ν →L[ℝ] Lp F 2 (μ.restrict K) := Lp.LpToLpOfMeasureLeSMul hc hle
  have hR : R f =ᵐ[μ.restrict K] f := Lp.coeFn_LpToLpOfMeasureLeSMul hc hle f
  have hRi := (ae_eq_restrict_iff_indicator_ae_eq hK).mp hR
  have hE := TauCeti.coeFn_extendByZeroLpₗᵢ (μ := μ) ℝ hK (subset_univ K) (R f)
  have hE' : (TauCeti.extendByZeroLpₗᵢ ℝ μ hK (subset_univ K) (R f) : X → F)
      =ᵐ[μ] K.indicator (R f : X → F) := by
    filter_upwards [(ae_restrict_iff' MeasurableSet.univ).mp hE] with x hx
    exact hx (mem_univ x)
  have hμ : μ ≤ (1 : ℝ≥0∞) • μ.restrict univ := by simp
  exact (Lp.coeFn_LpToLpOfMeasureLeSMul ENNReal.one_ne_top hμ _).trans (hE'.trans hRi)

theorem dbarIsometryTransfer_comp_apply {E₁ E₂ E₃ E₄ : Type*}
    [NormedAddCommGroup E₁] [NormedSpace ℝ E₁]
    [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [NormedAddCommGroup E₃] [NormedSpace ℝ E₃]
    [NormedAddCommGroup E₄] [NormedSpace ℝ E₄]
    (e : E₃ ≃ₗᵢ[ℝ] E₄) (i : E₂ →ₗᵢ[ℝ] E₃) (R : E₁ →L[ℝ] E₂) (f : E₁) :
    (e.toLinearIsometry.toContinuousLinearMap.comp (i.toContinuousLinearMap.comp R)) f =
      e (i (R f)) := by
  rfl

def dbarVolumeToCoulombCompactL {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (F : Type*) [NormedAddCommGroup F] [NormedSpace ℝ F] :
    Lp F 2 (volume : Measure (CoulombConfig N)) →L[ℝ] Lp F 2 (coulombMeasure N β) :=
  dbarMeasureCompactTransferL (F := F) (μ := coulombMeasure N β) (ν := volume)
    hK.measurableSet (dbarCoulomb_restrict_le_volume_smul hβ hK hKΩ).choose_spec.1
      (dbarCoulomb_restrict_le_volume_smul hβ hK hKΩ).choose_spec.2

theorem dbarVolumeToCoulombCompactL_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (volume : Measure (CoulombConfig N))) :
    dbarVolumeToCoulombCompactL hβ hK hKΩ F f =ᵐ[coulombMeasure N β]
      K.indicator (f : CoulombConfig N → F) := by
  exact dbarMeasureCompactTransferL_coe (F := F) (μ := coulombMeasure N β) (ν := volume)
    hK.measurableSet (dbarCoulomb_restrict_le_volume_smul hβ hK hKΩ).choose_spec.1
      (dbarCoulomb_restrict_le_volume_smul hβ hK hKΩ).choose_spec.2 f

theorem dbarVolumeToCoulombCompactL_eq_of_supported {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (volume : Measure (CoulombConfig N))) (g : Lp F 2 (coulombMeasure N β))
    (hfg : (f : CoulombConfig N → F) =ᵐ[volume] g)
    (hsupp : ∀ᵐ z ∂volume, z ∉ K → f z = 0) :
    dbarVolumeToCoulombCompactL hβ hK hKΩ F f = g := by
  apply Lp.ext
  filter_upwards [dbarVolumeToCoulombCompactL_coe hβ hK hKΩ f,
    (coulombMeasure_ae_iff hβ).mpr hfg, (coulombMeasure_ae_iff hβ).mpr hsupp] with z hz he hs
  rw [hz]
  by_cases h : z ∈ K
  · rw [indicator_of_mem h, he]
  · rw [indicator_of_notMem h, ← he, hs h]

theorem dbarVolumeToCoulombCompactL_tendsto {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι : Type*} {l : Filter ι}
    {f : ι → Lp F 2 (volume : Measure (CoulombConfig N))}
    {f₀ : Lp F 2 (volume : Measure (CoulombConfig N))} (hf : Tendsto f l (𝓝 f₀)) :
    Tendsto (fun i => dbarVolumeToCoulombCompactL hβ hK hKΩ F (f i)) l
      (𝓝 (dbarVolumeToCoulombCompactL hβ hK hKΩ F f₀)) :=
  (dbarVolumeToCoulombCompactL hβ hK hKΩ F).continuous.tendsto f₀ |>.comp hf

end RepulsiveCoulomb
