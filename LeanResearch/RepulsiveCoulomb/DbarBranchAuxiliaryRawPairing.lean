import LeanResearch.RepulsiveCoulomb.DbarBranchComplexLebesguePairing
import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryMinimalOperator

/-! Compact weak pairings for the raw auxiliary coefficient Sg. They are
continuous on auxiliary vector L2 because every S entry is multiplied by a
compact test. Global Euclidean-L2 integrability of Sg is not assumed. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombAuxiliaryRawTest {N : ℕ} (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) : TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombComplexCoreMulLocal (fun z => coulombRootMatrix z i j)
    (fun z hz => coulombRootMatrix_entry_contDiffAt i j hz)
    (TestFunction.postcompCLM Complex.ofRealCLM φ)

def coulombAuxiliaryRawPairingL {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    Lp (CoulombConfig N) 2 (coulombMeasure N β) →L[ℂ] ℂ :=
  ∑ j, (coulombComplexLebesgueTestPairingL hβ (coulombAuxiliaryRawTest i j φ)).comp
    ((EuclideanSpace.proj (𝕜 := ℂ) j).compLpL 2 (coulombMeasure N β))

theorem coulombAuxiliaryRawPairing_term {N : ℕ} {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombComplexLebesgueTestPairingL hβ (coulombAuxiliaryRawTest i j φ)
      ((EuclideanSpace.proj (𝕜 := ℂ) j).compLpL 2 (coulombMeasure N β) g) =
        ∫ z, (φ z : ℂ) * coulombRootMatrix z i j * g z j := by
  rw [coulombComplexLebesgueTestPairingL_apply]
  apply integral_congr_ae
  filter_upwards [(coulombMeasure_ae_iff hβ).mp
    ((EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) g)] with z hz
  rw [hz]
  change (coulombRootMatrix z i j * (φ z : ℂ)) * g z j = _
  ring

theorem coulombAuxiliaryRawPairing_term_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    Integrable (fun z => (φ z : ℂ) * coulombRootMatrix z i j * g z j) volume := by
  apply (coulombComplexLebesgueTestPairing_integrable hβ (coulombAuxiliaryRawTest i j φ)
    ((EuclideanSpace.proj (𝕜 := ℂ) j).compLpL 2 (coulombMeasure N β) g)).congr
  filter_upwards [(coulombMeasure_ae_iff hβ).mp
    ((EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) g)] with z hz
  rw [hz]
  change (coulombRootMatrix z i j * (φ z : ℂ)) * g z j = _
  ring

theorem coulombAuxiliaryRawPairingL_apply {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombAuxiliaryRawPairingL hβ i φ g =
      ∫ z, φ z • (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z)) i := by
  simp only [coulombAuxiliaryRawPairingL, _root_.sum_apply, ContinuousLinearMap.comp_apply]
  simp_rw [coulombAuxiliaryRawPairing_term]
  rw [← integral_finsetSum Finset.univ (fun j _ => coulombAuxiliaryRawPairing_term_integrable hβ i j φ g)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [dbarCLMMatrix_apply, Complex.real_smul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    change (φ z : ℂ) * coulombRootMatrix z i j * g z j =
      (φ z : ℂ) * (coulombRootMatrix z i j * g z j)
    ring

theorem coulombAuxiliaryRawPairing_core {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (ψ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombAuxiliaryRawPairingL hβ i φ (coulombAuxiliaryCoreDerivativeL N hβ ψ) =
      coulombL2Distribution hβ
        ((coulombCoordinate i).compLpL 2 (coulombMeasure N β) (coulombComplexCoreDbar hβ ψ)) φ := by
  have he : coulombAuxiliaryCoreDerivativeL N hβ ψ =
      coulombInverseRootL2L N β (coulombComplexCoreDbar hβ ψ) := by
    change coulombInverseRootL2L N β (coulombComplexDbarCoreLinear N hβ ψ) = _
    rw [coulombComplexDbarCoreLinear_apply]
  rw [he, coulombAuxiliaryRawPairingL_apply, coulombComplexCoreDbar_distribution_apply]
  apply integral_congr_ae
  filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombInverseRootL2_coe β (coulombComplexCoreDbar hβ ψ)),
    (coulombMeasure_ae_iff hβ).mp (coulombComplexCoreDbar_coe hβ ψ)] with z hR hψ
  change φ z • (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
    (coulombInverseRootL2 β (coulombComplexCoreDbar hβ ψ) z)) i = _
  rw [hR, hψ]
  have hi := congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L (coulombDbar ψ z))
    (dbarGraphMetricRoot_inverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hi
  rw [hi]
  rfl

end RepulsiveCoulomb
