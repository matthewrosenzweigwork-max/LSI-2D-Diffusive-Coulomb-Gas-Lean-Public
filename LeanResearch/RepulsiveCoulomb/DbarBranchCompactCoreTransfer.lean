module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactWeightedTransfer
public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactLocalMultiplier
public import LeanResearch.RepulsiveCoulomb.DbarBranchJointApproximationSupport

@[expose] public section

/-! The fixed-compact measure-transfer map preserves actual core values and
locally smooth coefficient products. These representative identities let
one transfer the common-support local approximants to the Gibbs norm. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem dbarVolumeCoreValue_supported {N : ℕ}
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    {L : Set (CoulombConfig N)} (hφ : tsupport (φ : CoulombConfig N → ℂ) ⊆ L) :
    ∀ᵐ z ∂volume, z ∉ L → dbarVolumeCoreValue φ z = 0 := by
  filter_upwards [dbarVolumeCoreValue_coe φ] with z hz
  intro hL
  rw [hz]
  exact image_eq_zero_of_notMem_tsupport (fun h => hL (hφ h))

theorem coulombCompactCore_volume_transfer {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {L : Set (CoulombConfig N)} (hL : IsCompact L) (hLΩ : L ⊆ coulombDomain N)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (hφ : tsupport (φ : CoulombConfig N → ℂ) ⊆ L) :
    dbarVolumeToCoulombCompactL hβ hL hLΩ ℂ (dbarVolumeCoreValue φ) =
      coulombComplexCoreValue hβ (coulombRestrictGlobalCore φ (hφ.trans hLΩ)) := by
  apply dbarVolumeToCoulombCompactL_eq_of_supported hβ hL hLΩ
  · have hg : (coulombComplexCoreValue hβ (coulombRestrictGlobalCore φ (hφ.trans hLΩ)) :
        CoulombConfig N → ℂ) =ᵐ[volume] (φ : CoulombConfig N → ℂ) :=
      (coulombMeasure_ae_iff hβ).mp
        (coulombComplexCoreValue_coe hβ (coulombRestrictGlobalCore φ (hφ.trans hLΩ)))
    exact (dbarVolumeCoreValue_coe φ).trans (Filter.EventuallyEq.symm hg)
  · exact dbarVolumeCoreValue_supported φ hφ

theorem coulombCompactCore_coefficient_volume_transfer {N : ℕ} {β S : ℝ}
    (hβ : 0 < β) (hS : 0 < S)
    {L : Set (CoulombConfig N)} (hL : IsCompact L) (hLS : L ⊆ coulombGraphRadiusSublevel N S)
    (a : CoulombConfig N → ℂ)
    (ha : ∀ z ∈ coulombDomain N, ContDiffAt ℝ (⊤ : ℕ∞) a z)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (hφ : tsupport (φ : CoulombConfig N → ℂ) ⊆ L) :
    dbarVolumeToCoulombCompactL hβ hL (fun z hz => (hLS hz).1) ℂ
      (coulombLocalCoefficientVolumeL a ha hS (dbarVolumeCoreValue φ)) =
        coulombComplexCoreValue hβ (coulombComplexCoreMulLocal a ha
          (coulombRestrictGlobalCore φ (fun z hz => (hLS (hφ hz)).1))) := by
  have hcoe := coulombLocalCoefficientVolumeL_coe_of_supported a ha hS hLS
    (dbarVolumeCoreValue φ) (dbarVolumeCoreValue_supported φ hφ)
  apply dbarVolumeToCoulombCompactL_eq_of_supported hβ hL (fun z hz => (hLS hz).1)
  · filter_upwards [hcoe, dbarVolumeCoreValue_coe φ,
      (coulombMeasure_ae_iff hβ).mp (coulombComplexCoreValue_coe hβ
        (coulombComplexCoreMulLocal a ha
          (coulombRestrictGlobalCore φ (fun z hz => (hLS (hφ hz)).1))))] with z hc hv hg
    rw [hc, hv, hg]
    rfl
  · filter_upwards [hcoe, dbarVolumeCoreValue_supported φ hφ] with z hc hv
    intro hz
    rw [hc, hv hz, mul_zero]

end RepulsiveCoulomb
