module

public import LeanResearch.RepulsiveCoulomb.DbarBranchWeightedCoreScore
public import LeanResearch.RepulsiveCoulomb.DbarBranchPotentialMixedWirtinger
public import LeanResearch.RepulsiveCoulomb.DbarBranchSecondWirtinger

@[expose] public section

/-! The actual compact-core commutator [dbar_i,delta_j], identified with the
actual Coulomb potential Hessian. The commutator itself is a genuine compact
test function, so subsequent weighted pairings have actual integrability. -/
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

def coulombWeightedCoreCommutator {N : ℕ} {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) : TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombDbarCoreCoordinateL N i (coulombWeightedCoreAdjointCoordinate hβ j φ) -
    coulombWeightedCoreAdjointCoordinate hβ j (coulombDbarCoreCoordinateL N i φ)

theorem coulombWeightedCoreCommutator_apply {N : ℕ} {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    coulombWeightedCoreCommutator hβ i j φ z =
      coulombDbarCoordinate (fun x => coulombDCoordinate (fun y => (coulombPotential β y : ℂ)) x j) z i * φ z := by
  have hφ2 : ContDiffAt ℝ 2 (φ : CoulombConfig N → ℂ) z := φ.contDiff.contDiffAt.of_le (by simp)
  have hDφ := (coulombDCoordinate_hasFDerivAt hφ2 j).differentiableAt
  have hDU := (coulombPotential_DCoordinate_hasFDerivAt β j hz).differentiableAt
  have hφ := φ.contDiff.differentiable (by simp) z
  have he : (coulombWeightedCoreAdjointCoordinate hβ j φ : CoulombConfig N → ℂ) =ᶠ[𝓝 z]
      fun x => -coulombDCoordinate φ x j + coulombDCoordinate (fun y => (coulombPotential β y : ℂ)) x j * φ x := by
    filter_upwards [(coulombDomain N).isOpen.mem_nhds hz] with x hx
    exact coulombWeightedCoreAdjointCoordinate_expanded hβ φ j hx
  have hb : ((coulombDbarCoreCoordinateL N i φ : TestFunction (coulombDomain N) ℂ ⊤) :
      CoulombConfig N → ℂ) = fun x => coulombDbarCoordinate φ x i :=
    funext (coulombDbarCoreCoordinateL_apply N i φ)
  change coulombDbarCoreCoordinateL N i (coulombWeightedCoreAdjointCoordinate hβ j φ) z -
    coulombWeightedCoreAdjointCoordinate hβ j (coulombDbarCoreCoordinateL N i φ) z = _
  rw [coulombDbarCoreCoordinateL_apply, coulombDbarCoordinate_congr_of_eventuallyEq he i]
  have hadd := coulombDbarCoordinate_add hDφ.neg (hDU.mul hφ) i
  simp only [Pi.neg_apply, Pi.mul_apply] at hadd
  rw [hadd]
  change coulombDbarCoordinate (fun x => -coulombDCoordinate φ x j) z i +
    coulombDbarCoordinate (fun x =>
      coulombDCoordinate (fun y => (coulombPotential β y : ℂ)) x j * φ x) z i -
    coulombWeightedCoreAdjointCoordinate hβ j (coulombDbarCoreCoordinateL N i φ) z = _
  rw [coulombDbarCoordinate_neg,
    coulombDbarCoordinate_mul hDU hφ, coulombDbar_D_commute hφ2 i j,
    coulombWeightedCoreAdjointCoordinate_expanded hβ (coulombDbarCoreCoordinateL N i φ) j hz,
    hb]
  ring

theorem coulombWeightedCoreCommutator_hessian {N : ℕ} {β : ℝ} (hβ : 0 < β) (i j : Fin N)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    coulombWeightedCoreCommutator hβ i j φ z =
      dbarRealHessianMatrix (fderiv ℝ (fderiv ℝ (coulombPotential β)) z) i j * φ z := by
  rw [coulombWeightedCoreCommutator_apply hβ i j φ hz, coulombPotential_mixedWirtinger_entry β i j hz]

end RepulsiveCoulomb
