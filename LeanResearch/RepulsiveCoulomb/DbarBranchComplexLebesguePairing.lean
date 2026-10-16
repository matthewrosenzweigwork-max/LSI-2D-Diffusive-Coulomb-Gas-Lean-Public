import LeanResearch.RepulsiveCoulomb.DbarBranchAdjointTests
import LeanResearch.RepulsiveCoulomb.DbarBranchLocalCoreMultiplier

/-! Compact complex test functions define genuine continuous unweighted
Lebesgue pairings on the Gibbs L2 space. This permits local variable-coefficient
weak equations without requiring those coefficients to be globally bounded. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombComplexLebesgueTestPairingL {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) :
    Lp ℂ 2 (coulombMeasure N β) →L[ℂ] ℂ :=
  coulombL2TestPairingComplexL hβ (TestFunction.postcompCLM Complex.reCLM ψ) +
    Complex.I • coulombL2TestPairingComplexL hβ (TestFunction.postcompCLM Complex.imCLM ψ)

theorem coulombComplexLebesgueTestPairing_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (f : Lp ℂ 2 (coulombMeasure N β)) :
    Integrable (fun z => ψ z * f z) volume :=
  ψ.integrable_bilin (ContinuousLinearMap.mul ℝ ℂ) (coulombL2_locallyIntegrableOn hβ f)

theorem coulombComplexLebesgueTestPairingL_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (f : Lp ℂ 2 (coulombMeasure N β)) :
    coulombComplexLebesgueTestPairingL hβ ψ f = ∫ z, ψ z * f z := by
  let ψr : TestFunction (coulombDomain N) ℝ ⊤ := TestFunction.postcompCLM Complex.reCLM ψ
  let ψi : TestFunction (coulombDomain N) ℝ ⊤ := TestFunction.postcompCLM Complex.imCLM ψ
  have hr := ψr.integrable_smul (coulombL2_locallyIntegrableOn hβ f)
  have hi := ψi.integrable_smul (coulombL2_locallyIntegrableOn hβ f)
  change coulombL2TestPairingComplexL hβ ψr f + Complex.I * coulombL2TestPairingComplexL hβ ψi f = _
  rw [coulombL2TestPairingComplexL_apply, coulombL2Distribution_apply,
    coulombL2TestPairingComplexL_apply, coulombL2Distribution_apply,
    ← integral_const_mul, ← integral_add hr (hi.const_mul Complex.I)]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    change (ψ z).re • f z + Complex.I * ((ψ z).im • f z) = ψ z * f z
    simp only [Complex.real_smul]
    have h := Complex.re_add_im (ψ z)
    calc
      _ = ((ψ z).re + (ψ z).im * Complex.I) * f z := by ring
      _ = _ := by rw [h]

end RepulsiveCoulomb
