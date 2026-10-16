module

public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactCoreTransfer
public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCompactData

@[expose] public section

/-! An actual bounded map returns the density-scaled local approximants to
the original Gibbs L2 space on one fixed compact margin. Its action on the
core approximants and the genuine cutoff input is identified exactly. -/
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem coulombComplexDensityInverse_contDiffAt {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun x => (coulombDensity N β x : ℂ)⁻¹) z := by
  apply (coulombComplexDensity_contDiffAt β hz).inv
  exact_mod_cast (ne_of_gt (coulombDensity_pos_off_collisions hβ hz))

def coulombDensityInverseVolumeL (N : ℕ) {β S : ℝ} (hβ : 0 < β) (hS : 0 < S) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) →L[ℝ] Lp ℂ 2 (volume : Measure (CoulombConfig N)) :=
  coulombLocalCoefficientVolumeL (fun z => (coulombDensity N β z : ℂ)⁻¹)
    (fun z hz => coulombComplexDensityInverse_contDiffAt hβ hz) hS

def coulombDensityReturnL {N : ℕ} {β S : ℝ} (hβ : 0 < β) (hS : 0 < S)
    {L : Set (CoulombConfig N)} (hL : IsCompact L) (hLΩ : L ⊆ coulombDomain N) :
    Lp ℂ 2 (volume : Measure (CoulombConfig N)) →L[ℝ] Lp ℂ 2 (coulombMeasure N β) :=
  (dbarVolumeToCoulombCompactL hβ hL hLΩ ℂ).comp (coulombDensityInverseVolumeL N hβ hS)

theorem coulombDensityReturnL_core {N : ℕ} {β S : ℝ} (hβ : 0 < β) (hS : 0 < S)
    {L : Set (CoulombConfig N)} (hL : IsCompact L) (hLS : L ⊆ coulombGraphRadiusSublevel N S)
    (φ : TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (hφ : tsupport (φ : CoulombConfig N → ℂ) ⊆ L) :
    coulombDensityReturnL hβ hS hL (fun z hz => (hLS hz).1) (dbarVolumeCoreValue φ) =
      coulombComplexCoreValue hβ (coulombComplexCoreDensityDiv hβ
        (coulombRestrictGlobalCore φ (fun z hz => (hLS (hφ hz)).1))) := by
  exact coulombCompactCore_coefficient_volume_transfer hβ hS hL hLS
    (fun z => (coulombDensity N β z : ℂ)⁻¹)
    (fun z hz => coulombComplexDensityInverse_contDiffAt hβ hz) φ hφ

theorem coulombDensityReturnL_cutoff_input {N : ℕ} {β R S : ℝ}
    (hβ : 0 < β) (hR : 0 < R) (hS : 0 < S)
    {L : Set (CoulombConfig N)} (hL : IsCompact L) (hLS : L ⊆ coulombGraphRadiusSublevel N S)
    (hKL : coulombMetricCutoffSupport N R ⊆ L)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β)) (b : Fin N) :
    coulombDensityReturnL hβ hS hL (fun z hz => (hLS hz).1)
      (coulombAuxiliaryCompactInputVolume hβ hR u b) =
        (EuclideanSpace.proj (𝕜 := ℂ) b).compLpL 2 (coulombMeasure N β)
          (coulombMetricCutoffL2L hR (CoulombConfig N) u) := by
  have hsup : ∀ᵐ z ∂volume, z ∉ L → coulombAuxiliaryCompactInputVolume hβ hR u b z = 0 := by
    filter_upwards [coulombAuxiliaryCompactInputVolume_supported hβ hR u b] with z hz
    exact fun hzL => hz (fun hzK => hzL (hKL hzK))
  have hcoef : coulombDensityInverseVolumeL N hβ hS (coulombAuxiliaryCompactInputVolume hβ hR u b)
      =ᵐ[volume] fun z => (coulombDensity N β z : ℂ)⁻¹ *
        coulombAuxiliaryCompactInputVolume hβ hR u b z :=
    coulombLocalCoefficientVolumeL_coe_of_supported _ _ hS hLS _ hsup
  have hin : (coulombAuxiliaryCompactInputVolume hβ hR u b : CoulombConfig N → ℂ) =ᵐ[volume]
      coulombDensityInputComponent β (coulombMetricCutoffL2L hR (CoulombConfig N) u) b :=
    (coulombAuxiliaryCompactInputVolume_coe hβ hR u b).trans
      (dbarIndicator_eq_of_ae_supported (coulombCutoffDensityInput_supported hβ hR u b))
  change dbarVolumeToCoulombCompactL hβ hL (fun z hz => (hLS hz).1) ℂ
    (coulombDensityInverseVolumeL N hβ hS (coulombAuxiliaryCompactInputVolume hβ hR u b)) = _
  apply dbarVolumeToCoulombCompactL_eq_of_supported hβ hL (fun z hz => (hLS hz).1)
  · filter_upwards [hcoef, hin, coulombDomain_ae N,
      (coulombMeasure_ae_iff hβ).mp ((EuclideanSpace.proj (𝕜 := ℂ) b).coeFn_compLpL
        (p := 2) (μ := coulombMeasure N β) (coulombMetricCutoffL2L hR (CoulombConfig N) u))]
      with z hc hi hz hp
    rw [hc, hi, hp]
    change (coulombDensity N β z : ℂ)⁻¹ * ((coulombDensity N β z : ℂ) *
      (coulombMetricCutoffL2L hR (CoulombConfig N) u z) b) = _
    have hd : (coulombDensity N β z : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (coulombDensity_pos_off_collisions hβ hz))
    rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
    rfl
  · filter_upwards [hcoef, hsup] with z hc hs
    intro hz
    rw [hc, hs hz, mul_zero]

end RepulsiveCoulomb
