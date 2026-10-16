module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCompatibility
public import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCutoffL2

@[expose] public section

/-! Actual multiplication and directional-product identities for compact
raw Sg test pairings. These are weak identities on auxiliary L2 and require
no global Euclidean-L2 integrability of Sg. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombRealCoreProduct {N : ℕ} (θ φ : TestFunction (coulombDomain N) ℝ ⊤) :
    TestFunction (coulombDomain N) ℝ ⊤ :=
  ⟨fun z => θ z * φ z, θ.contDiff.mul φ.contDiff, θ.hasCompactSupport.mul_right,
    tsupport_mul_subset_left.trans θ.tsupport_subset⟩

theorem coulombRealCoreProduct_lineDeriv {N : ℕ}
    (θ φ : TestFunction (coulombDomain N) ℝ ⊤) (v : CoulombConfig N) :
    (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v (coulombRealCoreProduct θ φ)) =
      coulombRealCoreProduct θ (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v φ) +
        coulombRealCoreProduct (TestFunction.lineDerivCLM (n := ⊤) (k := ⊤) ℝ v θ) φ := by
  ext z
  simp only [TestFunction.lineDerivCLM_eq_fderivCLM, TestFunction.fderivCLM_apply_of_le (n := ⊤) (k := ⊤) _ (by simp)]
  change fderiv ℝ (fun x => θ x * φ x) z v =
    θ z * fderiv ℝ (φ : CoulombConfig N → ℝ) z v + fderiv ℝ (θ : CoulombConfig N → ℝ) z v * φ z
  rw [fderiv_fun_mul (θ.contDiff.differentiable (by simp) z) (φ.contDiff.differentiable (by simp) z)]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

theorem coulombAuxiliaryRawPairing_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    Integrable (fun z => φ z •
      (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z)) i) volume := by
  have hsum := integrable_finsetSum Finset.univ
    (fun j _ => coulombAuxiliaryRawPairing_term_integrable hβ i j φ g)
  apply hsum.congr
  exact Eventually.of_forall fun z => by
    dsimp only
    rw [dbarCLMMatrix_apply, Complex.real_smul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => mul_assoc _ _ _)

theorem coulombAuxiliaryRawPairing_add_test {N : ℕ} {β : ℝ} (hβ : 0 < β) (i : Fin N)
    (φ ψ : TestFunction (coulombDomain N) ℝ ⊤)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombAuxiliaryRawPairingL hβ i (φ + ψ) g =
      coulombAuxiliaryRawPairingL hβ i φ g + coulombAuxiliaryRawPairingL hβ i ψ g := by
  rw [coulombAuxiliaryRawPairingL_apply, coulombAuxiliaryRawPairingL_apply, coulombAuxiliaryRawPairingL_apply]
  change (∫ z, (φ z + ψ z) • _) = _
  simp_rw [add_smul]
  exact integral_add (coulombAuxiliaryRawPairing_integrable hβ i φ g)
    (coulombAuxiliaryRawPairing_integrable hβ i ψ g)

theorem coulombAuxiliaryRawPairing_cutoff {N : ℕ} {β R : ℝ} (hβ : 0 < β) (hR : 0 < R)
    (i : Fin N) (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    coulombAuxiliaryRawPairingL hβ i φ (coulombMetricCutoffL2L hR (CoulombConfig N) g) =
      coulombAuxiliaryRawPairingL hβ i (coulombRealCoreProduct (coulombMetricCutoffTest hR) φ) g := by
  rw [coulombAuxiliaryRawPairingL_apply, coulombAuxiliaryRawPairingL_apply]
  apply integral_congr_ae
  filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombMetricCutoffL2L_coe hR g)] with z hz
  rw [hz]
  have hlin : dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
      (coulombMetricCutoff R z • g z) =
      coulombMetricCutoff R z • dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z) := by
    change dbarGraphMetricRoot _ ((coulombMetricCutoff R z : ℂ) • g z) =
      (coulombMetricCutoff R z : ℂ) • _
    exact map_smul _ _ _
  rw [hlin]
  let w : ℂ := dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (g z) i
  change φ z • (coulombMetricCutoff R z • w) = (coulombMetricCutoff R z * φ z) • w
  rw [smul_smul, mul_comm]

end RepulsiveCoulomb
