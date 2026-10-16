import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreRawSystem
import LeanResearch.RepulsiveCoulomb.DbarBranchClassicalLocalSystem
import LeanResearch.RepulsiveCoulomb.DbarBranchOutputWeakSystem

/-! Exact identification of the local classical system with the genuine
compact auxiliary adjoint and curl after division by the density. Equality
of actual weighted-L2 outputs follows from their injective distributions. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombAuxiliaryCore_joint_weakSystem {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    DbarLocalWeakSystem (coulombAuxiliaryJointPrincipal β) (coulombAuxiliaryJointLower β)
      (dbarSystemDirection N) (coulombDensityInputComponent β (coulombComplexVectorCoreValue hβ ψ))
      (fun q => (coulombAuxiliaryCoreJointOutput hβ ψ q : CoulombConfig N → ℂ)) := by
  have hs := dbarLocalWeakDivergenceSystem_output_weakSystem
    (coulombAuxiliaryRawSystemPrincipal β) (coulombAuxiliaryOutputMultiplier β)
    (fun a b d z hz => coulombAuxiliaryRawSystemPrincipal_contDiffAt hβ a b d hz)
    (fun q a z hz => coulombAuxiliaryOutputMultiplier_contDiffAt hβ q a hz)
    (dbarSystemDirection N) (coulombDensityInputComponent β (coulombComplexVectorCoreValue hβ ψ))
    (coulombAuxiliaryCoreRawSource hβ ψ)
    (coulombDensityInputComponent_locallyIntegrable hβ _)
    (coulombAuxiliaryCoreRawSource_locallyIntegrable hβ ψ)
    (coulombAuxiliaryCore_raw_weakSystem hβ ψ)
  exact dbarLocalWeakSystem_congr_ae hs (fun _ => ae_eq_rfl)
    (fun q => (coulombAuxiliaryOutputMultiplier_core_source hβ ψ q).symm)

theorem coulombAuxiliaryCoreDensityInput_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (b : Fin N) :
    (coulombComplexCoreDensityMul β (ψ b) : CoulombConfig N → ℂ) =ᵐ[volume]
      coulombDensityInputComponent β (coulombComplexVectorCoreValue hβ ψ) b := by
  filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombComplexVectorCoreValue_coe hβ ψ)] with z hz
  change (coulombDensity N β z : ℂ) * ψ b z =
    (coulombDensity N β z : ℂ) * (coulombComplexVectorCoreValue hβ ψ z) b
  rw [hz]
  rfl

theorem coulombComplexCoreDensityMul_div {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombComplexCoreDensityMul β (coulombComplexCoreDensityDiv hβ φ) = φ := by
  ext z
  change (coulombDensity N β z : ℂ) * coulombComplexCoreDensityDiv hβ φ z = φ z
  rw [coulombComplexCoreDensityDiv_apply]
  by_cases hz : z ∈ coulombDomain N
  · have hd : (coulombDensity N β z : ℂ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (coulombDensity_pos_off_collisions hβ hz))
    field_simp [hd]
  · have hφ : φ z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (φ.tsupport_subset h))
    rw [hφ, zero_div, mul_zero]

theorem coulombAuxiliaryCoreJointOutput_div_eq_classical {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    coulombAuxiliaryCoreJointOutput hβ (fun b => coulombComplexCoreDensityDiv hβ (φ b)) =
      fun q => coulombComplexCoreValue hβ
        (coulombLocalSystemCoreOutput (coulombAuxiliaryJointPrincipal β) (coulombAuxiliaryJointLower β)
          (fun q b d z hz => coulombAuxiliaryJointPrincipal_contDiffAt hβ q b d hz)
          (fun q b z hz => coulombAuxiliaryJointLower_contDiffAt hβ q b hz)
          (dbarSystemDirection N) φ q) := by
  let ψ := fun b => coulombComplexCoreDensityDiv hβ (φ b)
  have hinput (b : Fin N) : (φ b : CoulombConfig N → ℂ) =ᵐ[volume]
      coulombDensityInputComponent β (coulombComplexVectorCoreValue hβ ψ) b := by
    have h := coulombAuxiliaryCoreDensityInput_coe hβ ψ b
    simpa only [ψ, coulombComplexCoreDensityMul_div] using h
  have hactual := dbarLocalWeakSystem_congr_ae (coulombAuxiliaryCore_joint_weakSystem hβ ψ)
    hinput (fun _ => ae_eq_rfl)
  have hclassic := coulombLocalSystemCoreOutput_weakSystem
    (coulombAuxiliaryJointPrincipal β) (coulombAuxiliaryJointLower β)
    (fun q b d z hz => coulombAuxiliaryJointPrincipal_contDiffAt hβ q b d hz)
    (fun q b z hz => coulombAuxiliaryJointLower_contDiffAt hβ q b hz)
    (dbarSystemDirection N) φ
  have hclassicLp := dbarLocalWeakSystem_congr_ae hclassic (fun _ => ae_eq_rfl)
    (fun q => (coulombMeasure_ae_iff hβ).mp (coulombComplexCoreValue_coe hβ
      (coulombLocalSystemCoreOutput (coulombAuxiliaryJointPrincipal β) (coulombAuxiliaryJointLower β)
        (fun q b d z hz => coulombAuxiliaryJointPrincipal_contDiffAt hβ q b d hz)
        (fun q b z hz => coulombAuxiliaryJointLower_contDiffAt hβ q b hz)
        (dbarSystemDirection N) φ q)))
  exact dbarLocalWeakSystem_output_unique_L2 hβ hactual hclassicLp

end RepulsiveCoulomb
