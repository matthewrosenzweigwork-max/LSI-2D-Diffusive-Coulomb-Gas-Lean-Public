import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreWeakEquations
import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryJointData

/-! Both literal raw weak rows for arbitrary compact vector cores. This
does not require those cores to lie in the compatibility subspace: their
actual raw curl is retained as the second output. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombAuxiliaryCoreRawSource {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    CoulombAuxiliaryRawIndex N → CoulombConfig N → ℂ
  | none => fun z => (coulombDensity N β z : ℂ) *
      coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ ψ) z
  | some p => coulombAuxiliaryRawCurlCore ψ p

theorem coulombAuxiliaryCoreRawSource_locallyIntegrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (a : CoulombAuxiliaryRawIndex N) :
    LocallyIntegrableOn (coulombAuxiliaryCoreRawSource hβ ψ a) (coulombDomain N) volume := by
  cases a with
  | none =>
      exact (coulombL2_locallyIntegrableOn hβ
        (coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ ψ))).continuousOn_mul
          (fun z hz => (coulombComplexDensity_contDiffAt β hz).continuousAt.continuousWithinAt)
          (coulombDomain N).isOpen.isLocallyClosed
  | some p => exact ((coulombAuxiliaryRawCurlCore ψ p).continuous.locallyIntegrable).locallyIntegrableOn _

theorem coulombAuxiliaryCore_raw_weakSystem {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    DbarLocalWeakDivergenceSystem (coulombAuxiliaryRawSystemPrincipal β)
      (fun (_ : CoulombAuxiliaryRawIndex N) (_ : Fin N) (_ : CoulombConfig N) => 0)
      (dbarSystemDirection N) (coulombDensityInputComponent β (coulombComplexVectorCoreValue hβ ψ))
      (coulombAuxiliaryCoreRawSource hβ ψ) := by
  have hs := coulombAuxiliaryDbarAdjoint_scalar_weakSystem hβ (coulombAuxiliaryCore_adjoint_graph hβ ψ)
  intro a φ
  cases a with
  | none => exact hs () φ
  | some p =>
      simp only [zero_mul, smul_zero, integral_zero, Finset.sum_const_zero, add_zero,
        coulombAuxiliaryRawSystemPrincipal]
      rw [coulombAuxiliaryRawCurlDensityPrincipal_integral hβ _
        (coulombDensityInputComponent_locallyIntegrable hβ _) p.1 p.2 φ]
      have he : (∫ z, coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.1 *
          (∑ b, coulombDensityRootMatrix β z p.2 b *
            coulombDensityInputComponent β (coulombComplexVectorCoreValue hβ ψ) b z) -
          coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.2 *
            (∑ b, coulombDensityRootMatrix β z p.1 b *
              coulombDensityInputComponent β (coulombComplexVectorCoreValue hβ ψ) b z)) =
          coulombAuxiliaryCurlConstraintL hβ p.1 p.2 φ (coulombComplexVectorCoreValue hβ ψ) := by
        rw [coulombAuxiliaryCurlConstraint_integral]
        apply integral_congr_ae
        filter_upwards [coulombDomain_ae N] with z hz
        change coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.1 *
          (∑ b, coulombDensityRootMatrix β z p.2 b * ((coulombDensity N β z : ℂ) *
            (coulombComplexVectorCoreValue hβ ψ z) b)) -
          coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.2 *
            (∑ b, coulombDensityRootMatrix β z p.1 b * ((coulombDensity N β z : ℂ) *
              (coulombComplexVectorCoreValue hβ ψ z) b)) = _
        rw [coulombDensityRootMatrix_density_action hβ hz,
          coulombDensityRootMatrix_density_action hβ hz]
      rw [he, coulombAuxiliaryCore_raw_curl_constraint hβ ψ p φ, neg_neg]
      rfl

def coulombAuxiliaryCoreJointOutput {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    CoulombAuxiliaryJointIndex N → Lp ℂ 2 (coulombMeasure N β)
  | none => coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ ψ)
  | some p => (EuclideanSpace.proj (𝕜 := ℂ) p).compLpL 2 (coulombMeasure N β)
      (coulombAuxiliaryCoreCurlValue hβ ψ)

theorem coulombAuxiliaryOutputMultiplier_core_source {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (q : CoulombAuxiliaryJointIndex N) :
    (fun z => ∑ a, coulombAuxiliaryOutputMultiplier β q a z * coulombAuxiliaryCoreRawSource hβ ψ a z)
      =ᵐ[volume] (coulombAuxiliaryCoreJointOutput hβ ψ q : CoulombConfig N → ℂ) := by
  cases q with
  | none =>
      filter_upwards [coulombDomain_ae N] with z hz
      have hd : (coulombDensity N β z : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (coulombDensity_pos_off_collisions hβ hz))
      simp only [Fintype.sum_option, coulombAuxiliaryOutputMultiplier,
        coulombAuxiliaryCoreRawSource, coulombAuxiliaryCoreJointOutput,
        zero_mul, Finset.sum_const_zero, add_zero, zero_add]
      rw [← mul_assoc, inv_mul_cancel₀ hd, one_mul]
  | some p =>
      filter_upwards [(coulombMeasure_ae_iff hβ).mp
        ((EuclideanSpace.proj (𝕜 := ℂ) p).coeFn_compLpL (p := 2) (μ := coulombMeasure N β)
          (coulombAuxiliaryCoreCurlValue hβ ψ)),
        (coulombMeasure_ae_iff hβ).mp (coulombAuxiliaryCoreCurlValue_coe hβ ψ)] with z hp hψ
      change (∑ a, coulombAuxiliaryOutputMultiplier β (some p) a z *
        coulombAuxiliaryCoreRawSource hβ ψ a z) =
          ((EuclideanSpace.proj (𝕜 := ℂ) p).compLpL 2 (coulombMeasure N β)
            (coulombAuxiliaryCoreCurlValue hβ ψ)) z
      rw [hp, hψ]
      change _ = coulombAuxiliaryCoreCurl ψ z p.1.1 p.1.2
      simp only [Fintype.sum_option, coulombAuxiliaryOutputMultiplier,
        coulombAuxiliaryCoreRawSource, zero_mul, add_zero, zero_add, Fintype.sum_prod_type,
        coulombAuxiliaryCoreCurl, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l _
      apply Finset.sum_congr rfl
      intro k _
      simp only [coulombAuxiliaryRawCurlCore, _root_.sub_apply, coulombDbarCoreCoordinateL_apply]
      ring

end RepulsiveCoulomb
