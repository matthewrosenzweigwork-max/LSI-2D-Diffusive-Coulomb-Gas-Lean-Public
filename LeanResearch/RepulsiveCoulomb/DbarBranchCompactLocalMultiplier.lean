import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCoefficientExtension
import LeanResearch.RepulsiveCoulomb.DbarBranchTranslationMultiplier

/-! Locally smooth coefficients act by actual bounded L2 multipliers after
one common compact localization. This is the precise local mechanism for the
changes w=rho*u and u=rho^{-1}w, with no global density isomorphism asserted. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombLocalCoefficientVolumeL {N : ℕ} (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {R : ℝ} (hR : 0 < R) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) →L[ℝ]
      Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  dbarVolumeMulL ((coulombCoefficientExtensionGlobal a ha hR).memLp_top (μ := volume))

theorem coulombLocalCoefficientVolumeL_coe_of_supported {N : ℕ}
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {R : ℝ} (hR : 0 < R) {K : Set (CoulombConfig N)}
    (hKR : K ⊆ coulombGraphRadiusSublevel N R)
    (f : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hf : ∀ᵐ z ∂volume, z ∉ K → f z = 0) :
    coulombLocalCoefficientVolumeL a ha hR f =ᵐ[volume] fun z => a z * f z := by
  filter_upwards [dbarVolumeMulL_coe
    ((coulombCoefficientExtensionGlobal a ha hR).memLp_top (μ := volume)) f, hf] with z hm hz
  rw [coulombLocalCoefficientVolumeL, hm]
  by_cases hK : z ∈ K
  · change coulombCoefficientExtension a ha hR z * f z = _
    rw [coulombCoefficientExtension_eq a ha hR (hKR hK)]
  · rw [hz hK, mul_zero, mul_zero]

theorem coulombCompactLocalCoefficient_memLp_volume {N : ℕ}
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {f : CoulombConfig N → ℂ} (hf : MemLp f 2 volume)
    (hsupp : ∀ᵐ z ∂volume, z ∉ K → f z = 0) :
    MemLp (fun z => a z * f z) 2 volume := by
  obtain ⟨R, hR, hKR⟩ := coulombCompact_in_radius_sublevel hK hKΩ
  have hext : MemLp (fun z => coulombCoefficientExtensionGlobal a ha hR z * f z) 2 volume :=
    ((coulombCoefficientExtensionGlobal a ha hR).memLp_top (μ := volume)).fun_mul hf
  apply hext.ae_eq
  filter_upwards [hsupp] with z hz
  by_cases h : z ∈ K
  · change coulombCoefficientExtension a ha hR z * f z = _
    rw [coulombCoefficientExtension_eq a ha hR (hKR h)]
  · rw [hz h, mul_zero, mul_zero]

theorem coulombCompactLocalCoefficient_integrable_volume {N : ℕ}
    {K : Set (CoulombConfig N)} (hK : IsCompact K) (hKΩ : K ⊆ coulombDomain N)
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {f : CoulombConfig N → ℂ} (hf : MemLp f 2 volume)
    (hsupp : ∀ᵐ z ∂volume, z ∉ K → f z = 0) :
    Integrable (fun z => a z * f z) volume := by
  obtain ⟨R, hR, hKR⟩ := coulombCompact_in_radius_sublevel hK hKΩ
  have hi := (coulombCoefficientExtensionGlobal a ha hR).integrable_bilin
    (ContinuousLinearMap.mul ℝ ℂ)
    ((hf.locallyIntegrable (by norm_num)).locallyIntegrableOn _)
  apply hi.congr
  filter_upwards [hsupp] with z hz
  by_cases h : z ∈ K
  · change coulombCoefficientExtension a ha hR z * f z = _
    rw [coulombCoefficientExtension_eq a ha hR (hKR h)]
  · simp only [hz h, map_zero, mul_zero]

theorem coulombLocalCoefficientVolumeL_tendsto {N : ℕ}
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    {R : ℝ} (hR : 0 < R)
    {f : ℕ → Lp ℂ 2 (volume : Measure (CoulombConfig N))}
    {g : Lp ℂ 2 (volume : Measure (CoulombConfig N))}
    (hf : Tendsto f atTop (𝓝 g)) :
    Tendsto (fun n => coulombLocalCoefficientVolumeL a ha hR (f n)) atTop
      (𝓝 (coulombLocalCoefficientVolumeL a ha hR g)) :=
  (coulombLocalCoefficientVolumeL a ha hR).continuous.continuousAt.tendsto.comp hf

end RepulsiveCoulomb
