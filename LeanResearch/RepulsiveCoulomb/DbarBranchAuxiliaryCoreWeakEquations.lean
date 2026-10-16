import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreL2Estimate
import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryRawWeakSystem

/-! Genuine compact vector cores belong to the actual auxiliary Hilbert
adjoint domain, and their raw exterior source satisfies the literal weak
curl equation. These identities supply the exact operator identification
for local smooth approximants without assuming graph-core density. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators LinearPMap
namespace RepulsiveCoulomb

theorem coulombAuxiliaryCore_adjoint_graph {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    (coulombComplexVectorCoreValue hβ ψ,
      coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ ψ)) ∈
        (coulombAuxiliaryDbarAdjoint N hβ).graph := by
  apply (coulombAuxiliaryDbarAdjoint_graph_iff hβ _ _).mpr
  intro φ
  exact coulombAuxiliaryCore_ibp hβ φ ψ

def coulombAuxiliaryRawCurlCore {N : ℕ}
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (p : Fin N × Fin N) :
    TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombDbarCoreCoordinateL N p.1 (coulombRootCore ψ p.2) -
    coulombDbarCoreCoordinateL N p.2 (coulombRootCore ψ p.1)

theorem coulombComplexCore_product_integrable_volume {N : ℕ}
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) :
    Integrable (fun z => φ z * ψ z) volume :=
  (φ.continuous.mul ψ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_right

theorem coulombAuxiliaryCore_raw_curl_ibp {N : ℕ}
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤)
    (p : Fin N × Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z, coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.1 * coulombRootCore ψ p.2 z -
      coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.2 * coulombRootCore ψ p.1 z) =
        -(∫ z, φ z • coulombAuxiliaryRawCurlCore ψ p z) := by
  let φc : TestFunction (coulombDomain N) ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM φ
  have hi := dbarComplexCore_bilinear_ibp φc (coulombRootCore ψ p.2) p.1
  have hj := dbarComplexCore_bilinear_ibp φc (coulombRootCore ψ p.1) p.2
  have hci := coulombComplexCore_product_integrable_volume
    (coulombDbarCoreCoordinateL N p.1 φc) (coulombRootCore ψ p.2)
  have hcj := coulombComplexCore_product_integrable_volume
    (coulombDbarCoreCoordinateL N p.2 φc) (coulombRootCore ψ p.1)
  have hdi := coulombComplexCore_product_integrable_volume φc
    (coulombDbarCoreCoordinateL N p.1 (coulombRootCore ψ p.2))
  have hdj := coulombComplexCore_product_integrable_volume φc
    (coulombDbarCoreCoordinateL N p.2 (coulombRootCore ψ p.1))
  simp only [coulombDbarCoreCoordinateL_apply] at hci hcj hdi hdj
  have he : (∫ z, φ z • coulombAuxiliaryRawCurlCore ψ p z) =
      (∫ z, φc z * coulombDbarCoordinate (coulombRootCore ψ p.2) z p.1) -
        ∫ z, φc z * coulombDbarCoordinate (coulombRootCore ψ p.1) z p.2 := by
    calc
      _ = ∫ z, φc z * coulombDbarCoordinate (coulombRootCore ψ p.2) z p.1 -
          φc z * coulombDbarCoordinate (coulombRootCore ψ p.1) z p.2 := by
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by
          simp only [coulombAuxiliaryRawCurlCore, _root_.sub_apply,
            coulombDbarCoreCoordinateL_apply, Complex.real_smul]
          change (φ z : ℂ) * (_ - _) = (φ z : ℂ) * _ - (φ z : ℂ) * _
          ring
      _ = _ := integral_sub hdi hdj
  change (∫ z, coulombDbarCoordinate φc z p.1 * coulombRootCore ψ p.2 z -
    coulombDbarCoordinate φc z p.2 * coulombRootCore ψ p.1 z) = _
  rw [integral_sub hci hcj, he]
  linear_combination hi - hj

theorem coulombAuxiliaryCore_raw_curl_constraint {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤)
    (p : Fin N × Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombAuxiliaryCurlConstraintL hβ p.1 p.2 φ (coulombComplexVectorCoreValue hβ ψ) =
      -(∫ z, φ z • coulombAuxiliaryRawCurlCore ψ p z) := by
  rw [coulombAuxiliaryCurlConstraint_integral]
  calc
    _ = ∫ z, coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.1 * coulombRootCore ψ p.2 z -
        coulombDbarCoordinate (fun x => (φ x : ℂ)) z p.2 * coulombRootCore ψ p.1 z := by
      apply integral_congr_ae
      filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombComplexVectorCoreValue_coe hβ ψ)] with z hz
      rw [hz, ← coulombRootCore_vector]
      rfl
    _ = _ := coulombAuxiliaryCore_raw_curl_ibp ψ p φ

end RepulsiveCoulomb
