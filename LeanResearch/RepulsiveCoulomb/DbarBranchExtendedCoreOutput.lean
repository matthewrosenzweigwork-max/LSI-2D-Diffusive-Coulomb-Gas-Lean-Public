module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreOutputIdentification
public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryLocalMollification

@[expose] public section

/-! On the constructed common support margin the compact coefficient
extension gives exactly the original local classical operator. Combining
this with weak-output uniqueness identifies the genuine compact auxiliary
adjoint and curl of the density-divided approximants. -/
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

def coulombAuxiliaryExtendedCoreOutput {N : ℕ} {β S : ℝ} (hβ : 0 < β) (hS : 0 < S)
    {L : Set (CoulombConfig N)} (hL : IsClosed L) (hLS : L ⊆ coulombGraphRadiusSublevel N S)
    (φ : Fin N → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (hφ : ∀ b, tsupport (φ b : CoulombConfig N → ℂ) ⊆ L) (q : CoulombAuxiliaryJointIndex N) :
    TestFunction (coulombDomain N) ℂ ⊤ :=
  coulombRestrictGlobalCore
    (dbarSystemCoreOutput (coulombAuxiliaryExtendedPrincipal N hβ hS)
      (coulombAuxiliaryExtendedLower N hβ hS) (dbarSystemDirection N) φ q)
    (fun z hz => (hLS (dbarSystemCoreOutput_tsupport_subset
      (coulombAuxiliaryExtendedPrincipal N hβ hS) (coulombAuxiliaryExtendedLower N hβ hS)
      (dbarSystemDirection N) φ hL hφ q hz)).1)

theorem coulombAuxiliaryExtendedOutput_eq_local {N : ℕ} {β S : ℝ}
    (hβ : 0 < β) (hS : 0 < S) {L : Set (CoulombConfig N)}
    (hLS : L ⊆ coulombGraphRadiusSublevel N S)
    (φ : Fin N → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (hφ : ∀ b, tsupport (φ b : CoulombConfig N → ℂ) ⊆ L)
    (q : CoulombAuxiliaryJointIndex N) (z : CoulombConfig N) :
    dbarSystemCoreOutput (coulombAuxiliaryExtendedPrincipal N hβ hS)
      (coulombAuxiliaryExtendedLower N hβ hS) (dbarSystemDirection N) φ q z =
      coulombLocalSystemCoreOutput (coulombAuxiliaryJointPrincipal β) (coulombAuxiliaryJointLower β)
        (fun q b d z hz => coulombAuxiliaryJointPrincipal_contDiffAt hβ q b d hz)
        (fun q b z hz => coulombAuxiliaryJointLower_contDiffAt hβ q b hz)
        (dbarSystemDirection N)
        (fun b => coulombRestrictGlobalCore (φ b) (fun z hz => (hLS (hφ b hz)).1)) q z := by
  rw [coulombLocalSystemCoreOutput_apply]
  simp only [dbarSystemCoreOutput, _root_.add_apply, _root_.sum_apply]
  change (∑ b, ∑ d, coulombAuxiliaryExtendedPrincipal N hβ hS q b d z *
      dbarVolumeCoreDerivative (dbarSystemDirection N d) (φ b) z) +
    (∑ b, coulombAuxiliaryExtendedLower N hβ hS q b z * φ b z) =
      (∑ b, ∑ d, coulombAuxiliaryJointPrincipal β q b d z *
        fderiv ℝ (φ b : CoulombConfig N → ℂ) z (dbarSystemDirection N d)) +
        ∑ b, coulombAuxiliaryJointLower β q b z * φ b z
  simp_rw [dbarVolumeCoreDerivative_apply]
  by_cases hz : z ∈ L
  · have hA (b : Fin N) (d : Fin N × Bool) :
        coulombAuxiliaryExtendedPrincipal N hβ hS q b d z = coulombAuxiliaryJointPrincipal β q b d z :=
      coulombCoefficientExtension_eq (coulombAuxiliaryJointPrincipal β q b d)
        (fun w hw => coulombAuxiliaryJointPrincipal_contDiffAt hβ q b d hw) hS (hLS hz)
    have hB (b : Fin N) :
        coulombAuxiliaryExtendedLower N hβ hS q b z = coulombAuxiliaryJointLower β q b z :=
      coulombCoefficientExtension_eq (coulombAuxiliaryJointLower β q b)
        (fun w hw => coulombAuxiliaryJointLower_contDiffAt hβ q b hw) hS (hLS hz)
    simp only [hA, hB]
  · have hn (b : Fin N) : z ∉ tsupport (φ b : CoulombConfig N → ℂ) := fun h => hz (hφ b h)
    have hv (b : Fin N) : φ b z = 0 := image_eq_zero_of_notMem_tsupport (hn b)
    have hd (b : Fin N) : fderiv ℝ (φ b : CoulombConfig N → ℂ) z = 0 :=
      fderiv_of_notMem_tsupport ℝ (hn b)
    simp only [hv, hd, ContinuousLinearMap.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]

theorem coulombAuxiliaryCoreJointOutput_div_eq_extended {N : ℕ} {β S : ℝ}
    (hβ : 0 < β) (hS : 0 < S) {L : Set (CoulombConfig N)}
    (hL : IsClosed L) (hLS : L ⊆ coulombGraphRadiusSublevel N S)
    (φ : Fin N → TestFunction (⊤ : Opens (CoulombConfig N)) ℂ ⊤)
    (hφ : ∀ b, tsupport (φ b : CoulombConfig N → ℂ) ⊆ L) :
    coulombAuxiliaryCoreJointOutput hβ
      (fun b => coulombComplexCoreDensityDiv hβ
        (coulombRestrictGlobalCore (φ b) (fun z hz => (hLS (hφ b hz)).1))) =
      fun q => coulombComplexCoreValue hβ (coulombAuxiliaryExtendedCoreOutput hβ hS hL hLS φ hφ q) := by
  rw [coulombAuxiliaryCoreJointOutput_div_eq_classical]
  funext q
  congr 1
  ext z
  exact (coulombAuxiliaryExtendedOutput_eq_local hβ hS hLS φ hφ q z).symm

end RepulsiveCoulomb
