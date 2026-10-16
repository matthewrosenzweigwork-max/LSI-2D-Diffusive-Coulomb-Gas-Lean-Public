import LeanResearch.RepulsiveCoulomb.DbarBranchLocalDistribution

/-! Actual compactly supported Gibbs-L2 representatives are global Lebesgue
L2 and L1 functions. This supplies, rather than assumes, the integrability
conditions needed by the local simultaneous mollification theorem. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem coulombCompactL2_indicator_memLp_volume {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (coulombMeasure N β)) :
    MemLp (K.indicator (f : CoulombConfig N → F)) 2 volume := by
  apply (memLp_indicator_iff_restrict hK.measurableSet).mpr
  exact (Lp.memLp (coulombL2RestrictToVolume hβ hK hKΩ Subset.rfl F f)).ae_eq
    (coulombL2RestrictToVolume_coe hβ hK hKΩ Subset.rfl f)

theorem coulombCompactL2_indicator_integrable_volume {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (coulombMeasure N β)) :
    Integrable (K.indicator (f : CoulombConfig N → F)) volume := by
  apply (integrable_indicator_iff hK.measurableSet).mpr
  exact (coulombL2_locallyIntegrableOn hβ f).integrableOn_compact_subset hKΩ hK

theorem coulombCompactL2_indicator_eq_ae {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (coulombMeasure N β))
    (hsupp : ∀ᵐ z ∂coulombMeasure N β, z ∉ K → f z = 0) :
    K.indicator (f : CoulombConfig N → F) =ᵐ[volume] f := by
  filter_upwards [(coulombMeasure_ae_iff hβ).mp hsupp] with z hz
  by_cases h : z ∈ K
  · exact indicator_of_mem h _
  · rw [indicator_of_notMem h, hz h]

theorem coulombCompactL2_memLp_volume {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (coulombMeasure N β))
    (hsupp : ∀ᵐ z ∂coulombMeasure N β, z ∉ K → f z = 0) :
    MemLp (f : CoulombConfig N → F) 2 volume :=
  (coulombCompactL2_indicator_memLp_volume hβ hK hKΩ f).ae_eq
    (coulombCompactL2_indicator_eq_ae hβ f hsupp)

theorem coulombCompactL2_integrable_volume {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : Lp F 2 (coulombMeasure N β))
    (hsupp : ∀ᵐ z ∂coulombMeasure N β, z ∉ K → f z = 0) :
    Integrable (f : CoulombConfig N → F) volume :=
  (coulombCompactL2_indicator_integrable_volume hβ hK hKΩ f).congr
    (coulombCompactL2_indicator_eq_ae hβ f hsupp)

end RepulsiveCoulomb
