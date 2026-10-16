module

public import LeanResearch.RepulsiveCoulomb.DbarBranchLeviMatrixContraction
public import LeanResearch.RepulsiveCoulomb.DbarBranchWirtingerAlgebra
public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCrossTerm

@[expose] public section

/-! The actual mixed Wirtinger derivatives of the potential, with their
contracted curvature exactly beta/2. This is a derivative identity, not the
L2 basic estimate or its passage to a maximal domain. -/
noncomputable section
open Set Filter InnerProductSpace
open scoped Topology BigOperators ComplexConjugate
namespace RepulsiveCoulomb

theorem coulombPotential_DCoordinate_eq {N : ℕ} (β : ℝ) (j : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    coulombDCoordinate (fun x => (coulombPotential β x : ℂ)) z j =
      ((fderiv ℝ (coulombPotential β) z (coulombCoordinateInjection N j 1) : ℂ) -
        Complex.I * (fderiv ℝ (coulombPotential β) z (coulombCoordinateInjection N j Complex.I) : ℂ)) / 2 := by
  have hd := Complex.ofRealCLM.hasFDerivAt.comp z
    ((coulombPotential_contDiffAt β hz).differentiableAt (by simp)).hasFDerivAt
  have hfd := hd.fderiv
  change fderiv ℝ (fun x => (coulombPotential β x : ℂ)) z = _ at hfd
  rw [coulombDCoordinate, hfd]
  rfl

theorem coulombPotential_DCoordinate_hasFDerivAt {N : ℕ} (β : ℝ) (j : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    HasFDerivAt (fun x => coulombDCoordinate (fun y => (coulombPotential β y : ℂ)) x j)
      ((1 / 2 : ℂ) •
        (Complex.ofRealCLM.comp ((fderiv ℝ (fderiv ℝ (coulombPotential β)) z).flip (coulombCoordinateInjection N j 1)) -
          Complex.I • Complex.ofRealCLM.comp
            ((fderiv ℝ (fderiv ℝ (coulombPotential β)) z).flip (coulombCoordinateInjection N j Complex.I)))) z := by
  have hx := Complex.ofRealCLM.hasFDerivAt.comp z
    (coulombPotential_component_hasFDerivAt β hz (coulombCoordinateInjection N j 1))
  have hy := Complex.ofRealCLM.hasFDerivAt.comp z
    (coulombPotential_component_hasFDerivAt β hz (coulombCoordinateInjection N j Complex.I))
  have hd := (hx.sub (hy.const_mul Complex.I)).const_mul (1 / 2 : ℂ)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(coulombDomain N).isOpen.mem_nhds hz] with x hΩ
  rw [coulombPotential_DCoordinate_eq β j hΩ]
  simp only [Function.comp_def, Complex.ofRealCLM_apply]
  change (_ - Complex.I * _) / 2 = (1 / 2 : ℂ) * (_ - Complex.I * _)
  ring

theorem coulombPotential_mixedWirtinger_entry {N : ℕ} (β : ℝ) (i j : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    coulombDbarCoordinate (fun x => coulombDCoordinate (fun y => (coulombPotential β y : ℂ)) x j) z i =
      dbarRealHessianMatrix (fderiv ℝ (fderiv ℝ (coulombPotential β)) z) i j := by
  rw [coulombDbarCoordinate, (coulombPotential_DCoordinate_hasFDerivAt β j hz).fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply, Complex.ofRealCLM_apply, smul_eq_mul,
    dbarRealHessianMatrix]
  push_cast
  ring_nf
  simp only [Complex.I_sq] <;> ring

theorem coulombPotential_mixedWirtinger_contraction {N : ℕ} (β : ℝ)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) (v : CoulombConfig N) :
    (∑ i, ∑ j, conj (v i) *
      coulombDbarCoordinate (fun x => coulombDCoordinate (fun y => (coulombPotential β y : ℂ)) x j) z i * v j).re =
        (β / 2) * ‖v‖ ^ 2 := by
  simp_rw [coulombPotential_mixedWirtinger_entry β _ _ hz]
  exact coulombPotential_levi_matrix_contraction β hz v

end RepulsiveCoulomb
