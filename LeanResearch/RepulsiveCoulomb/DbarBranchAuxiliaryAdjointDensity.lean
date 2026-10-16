import LeanResearch.RepulsiveCoulomb.DbarBranchWeightedCorePairing
import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryMinimalOperator

/-! The genuine auxiliary adjoint, after the local change w=rho*u, is the
ordinary Lebesgue divergence -sum partial_j(Rw)_j. These are exact weak test
identities; the density change is not asserted to be a global L2 isomorphism. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators LinearPMap ComplexConjugate
namespace RepulsiveCoulomb

theorem coulombAuxiliaryDbarAdjoint_density_test {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    coulombComplexLebesgueTestPairingL hβ
      (coulombComplexCoreDensityMul β (TestFunction.postcompCLM Complex.ofRealCLM φ)) h =
      ∑ j, coulombComplexLebesgueTestPairingL hβ
        (coulombComplexCoreDensityMul β
          (coulombDCoreCoordinateL N j (TestFunction.postcompCLM Complex.ofRealCLM φ)))
        ((EuclideanSpace.proj (𝕜 := ℂ) j).compLpL 2 (coulombMeasure N β) (coulombInverseRootL2L N β u)) := by
  let ψ : TestFunction (coulombDomain N) ℂ ⊤ := TestFunction.postcompCLM Complex.ofRealCLM φ
  have ht := (coulombAuxiliaryDbarAdjoint_graph_iff hβ u h).mp huh ψ
  change inner ℂ (coulombInverseRootL2L N β (coulombComplexDbarCoreLinear N hβ ψ)) u = _ at ht
  rw [coulombComplexDbarCoreLinear_apply, coulombInverseRootL2L_selfAdjoint_pairing,
    ← coulombComplexVectorCoreValue_dbar hβ ψ, coulombComplexVectorCoreValue_inner_left] at ht
  simp_rw [coulombComplexCore_density_inner] at ht
  dsimp only [ψ] at ht
  simp_rw [coulombRealCore_dbar_conjugate] at ht
  have he : TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap
      (TestFunction.postcompCLM Complex.ofRealCLM φ) = TestFunction.postcompCLM Complex.ofRealCLM φ := by
    ext z
    exact Complex.conj_ofReal (φ z)
  rw [he] at ht
  exact ht.symm

theorem coulombAuxiliaryDbarAdjoint_density_weak {N : ℕ} {β : ℝ} (hβ : 0 < β)
    {u : Lp (CoulombConfig N) 2 (coulombMeasure N β)} {h : Lp ℂ 2 (coulombMeasure N β)}
    (huh : (u, h) ∈ (coulombAuxiliaryDbarAdjoint N hβ).graph)
    (φ : TestFunction (coulombDomain N) ℝ ⊤) :
    (∫ z, φ z • ((coulombDensity N β z : ℂ) * h z)) =
      ∑ j, ∫ z, coulombDCoordinate (fun x => (φ x : ℂ)) z j *
        ((coulombDensity N β z : ℂ) *
          (dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (u z)) j) := by
  calc
    _ = coulombComplexLebesgueTestPairingL hβ
        (coulombComplexCoreDensityMul β (TestFunction.postcompCLM Complex.ofRealCLM φ)) h := by
      rw [coulombComplexLebesgueTestPairingL_apply]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change φ z • ((coulombDensity N β z : ℂ) * h z) =
          ((coulombDensity N β z : ℂ) * (φ z : ℂ)) * h z
        rw [Complex.real_smul]
        ring
    _ = _ := by
      rw [coulombAuxiliaryDbarAdjoint_density_test hβ huh φ]
      apply Finset.sum_congr rfl
      intro j _
      rw [coulombComplexLebesgueTestPairingL_apply]
      apply integral_congr_ae
      filter_upwards [(coulombMeasure_ae_iff hβ).mp
          ((EuclideanSpace.proj (𝕜 := ℂ) j).coeFn_compLpL (p := 2) (μ := coulombMeasure N β)
            (coulombInverseRootL2L N β u)),
        (coulombMeasure_ae_iff hβ).mp (coulombInverseRootL2_coe β u)] with z hp hR
      rw [hp]
      change ((coulombDensity N β z : ℂ) *
        coulombDCoreCoordinateL N j (TestFunction.postcompCLM Complex.ofRealCLM φ) z) *
          (coulombInverseRootL2 β u z) j = _
      rw [hR, coulombDCoreCoordinateL_apply]
      simp only [TestFunction.postcompCLM_apply, Function.comp_def, Complex.ofRealCLM_apply]
      ring

end RepulsiveCoulomb
