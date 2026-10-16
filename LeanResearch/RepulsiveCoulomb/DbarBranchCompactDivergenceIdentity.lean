module

public import LeanResearch.RepulsiveCoulomb.DbarBranchWeightedCoreCommutator
public import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCoreCurl
public import LeanResearch.RepulsiveCoulomb.DbarBranchDenseDomain

@[expose] public section

/-! Finite-sum weighted integration-by-parts identity on actual compact
complex vector cores. The curvature coefficient is derived from the actual
Coulomb mixed Hessian. No maximal-domain basic estimate is assumed. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace RepulsiveCoulomb

def dbarCoreVector {N : ℕ} (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) : CoulombConfig N :=
  WithLp.toLp 2 (fun i => v i z)

theorem dbarCoreVector_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) : MemLp (dbarCoreVector v) 2 (coulombMeasure N β) := by
  apply memLp_piLp_iff.mpr
  exact fun i => coulombComplexCore_memLp hβ (v i)

theorem dbarComplexCore_inner_eq_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) :
    inner ℂ (coulombComplexCoreValue hβ φ) (coulombComplexCoreValue hβ ψ) =
      ∫ z, conj (φ z) * ψ z ∂coulombMeasure N β := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [coulombComplexCoreValue_coe hβ φ, coulombComplexCoreValue_coe hβ ψ] with z hφ hψ
  simp only [hφ, hψ, RCLike.inner_apply']

theorem dbarComplexCore_adjoint_inner_left {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) (i : Fin N) :
    inner ℂ (coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ i φ)) (coulombComplexCoreValue hβ ψ) =
      inner ℂ (coulombComplexCoreValue hβ φ) (coulombComplexCoreValue hβ (coulombDbarCoreCoordinateL N i ψ)) := by
  rw [dbarComplexCore_inner_eq_integral, dbarComplexCore_inner_eq_integral]
  exact (coulombWeightedCoreAdjointCoordinate_ibp hβ φ ψ i).symm

theorem dbarComplexCore_adjoint_inner_right {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ ψ : TestFunction (coulombDomain N) ℂ ⊤) (i : Fin N) :
    inner ℂ (coulombComplexCoreValue hβ φ) (coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ i ψ)) =
      inner ℂ (coulombComplexCoreValue hβ (coulombDbarCoreCoordinateL N i φ)) (coulombComplexCoreValue hβ ψ) := by
  have h := congrArg (starRingEnd ℂ) (dbarComplexCore_adjoint_inner_left hβ ψ φ i)
  simpa only [inner_conj_symm] using h

theorem dbarCore_double_inner_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (a b : Fin N → Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    (∑ i, ∑ j, inner ℂ (coulombComplexCoreValue hβ (a i j)) (coulombComplexCoreValue hβ (b i j))).re =
      ∫ z, ∑ i, ∑ j, (conj (a i j z) * b i j z).re ∂coulombMeasure N β := by
  have hi (i j : Fin N) := dbarComplexCore_weighted_pair_integrable hβ (a i j) (b i j)
  have hsum := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))
  have hswap : (∑ i, ∑ j, inner ℂ (coulombComplexCoreValue hβ (a i j)) (coulombComplexCoreValue hβ (b i j))) =
      ∫ z, ∑ i, ∑ j, conj (a i j z) * b i j z ∂coulombMeasure N β := by
    simp_rw [dbarComplexCore_inner_eq_integral]
    rw [integral_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hi i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact (integral_finsetSum Finset.univ (fun j _ => hi i j)).symm
  have hreal : (∫ z, (∑ i, ∑ j, conj (a i j z) * b i j z).re ∂coulombMeasure N β) =
      (∫ z, ∑ i, ∑ j, conj (a i j z) * b i j z ∂coulombMeasure N β).re :=
    integral_re hsum
  rw [hswap, ← hreal]
  simp only [Complex.re_sum]

theorem dbarCore_curvature_sum_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    (∑ i, ∑ j, inner ℂ (coulombComplexCoreValue hβ (v i))
      (coulombComplexCoreValue hβ (coulombWeightedCoreCommutator hβ i j (v j)))).re =
      (β / 2) * (∫ z, ‖dbarCoreVector v z‖ ^ 2 ∂coulombMeasure N β) := by
  rw [dbarCore_double_inner_integral hβ (fun i _ => v i) (fun i j => coulombWeightedCoreCommutator hβ i j (v j)),
    ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [(coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae N)] with z hz
  have h := coulombPotential_levi_matrix_contraction β hz (dbarCoreVector v z)
  calc
    _ = ∑ i, ∑ j, (conj (v i z) *
        dbarRealHessianMatrix (fderiv ℝ (fderiv ℝ (coulombPotential β)) z) i j * v j z).re := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [coulombWeightedCoreCommutator_hessian hβ i j (v j) hz]
      exact congrArg Complex.re (mul_assoc _ _ _).symm
    _ = _ := by
      simpa only [Complex.re_sum, dbarCoreVector, WithLp.ofLp_toLp] using h

theorem dbarCore_cross_sum_integral {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    (∑ i, ∑ j, inner ℂ (coulombComplexCoreValue hβ (coulombDbarCoreCoordinateL N j (v i)))
      (coulombComplexCoreValue hβ (coulombDbarCoreCoordinateL N i (v j)))).re =
      ∫ z, dbarMatrixTransposeCross (dbarCoreJacobian v z) ∂coulombMeasure N β := by
  rw [dbarCore_double_inner_integral hβ
    (fun i j => coulombDbarCoreCoordinateL N j (v i)) (fun i j => coulombDbarCoreCoordinateL N i (v j))]
  apply integral_congr_ae
  exact Eventually.of_forall fun z => by
    simp only [dbarMatrixTransposeCross, dbarCoreJacobian, coulombDbarCoreCoordinateL_apply, mul_comm]

theorem dbarCore_divergence_pair_identity {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (i j : Fin N) :
    inner ℂ (coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ i (v i)))
      (coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (v j))) =
    inner ℂ (coulombComplexCoreValue hβ (coulombDbarCoreCoordinateL N j (v i)))
      (coulombComplexCoreValue hβ (coulombDbarCoreCoordinateL N i (v j))) +
    inner ℂ (coulombComplexCoreValue hβ (v i))
      (coulombComplexCoreValue hβ (coulombWeightedCoreCommutator hβ i j (v j))) := by
  have hsub : coulombComplexCoreValue hβ (coulombWeightedCoreCommutator hβ i j (v j)) =
      coulombComplexCoreValue hβ (coulombDbarCoreCoordinateL N i (coulombWeightedCoreAdjointCoordinate hβ j (v j))) -
        coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (coulombDbarCoreCoordinateL N i (v j))) :=
    map_sub (coulombComplexCoreValueLinear N hβ) _ _
  have he : coulombComplexCoreValue hβ (coulombDbarCoreCoordinateL N i (coulombWeightedCoreAdjointCoordinate hβ j (v j))) =
      coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (coulombDbarCoreCoordinateL N i (v j))) +
        coulombComplexCoreValue hβ (coulombWeightedCoreCommutator hβ i j (v j)) := by
    rw [hsub]
    abel
  rw [dbarComplexCore_adjoint_inner_left hβ (v i) (coulombWeightedCoreAdjointCoordinate hβ j (v j)) i,
    he, inner_add_right, dbarComplexCore_adjoint_inner_right]

theorem dbarCore_divergence_identity {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    ‖∑ j, coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (v j))‖ ^ 2 =
      (∫ z, dbarMatrixTransposeCross (dbarCoreJacobian v z) ∂coulombMeasure N β) +
        (β / 2) * (∫ z, ‖dbarCoreVector v z‖ ^ 2 ∂coulombMeasure N β) := by
  have hnorm : ‖∑ j, coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (v j))‖ ^ 2 =
      (∑ i, ∑ j, inner ℂ
        (coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ i (v i)))
        (coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (v j)))).re := by
    calc
      _ = (inner ℂ
        (∑ j, coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (v j)))
        (∑ j, coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (v j)))).re :=
          (inner_self_eq_norm_sq (𝕜 := ℂ) _).symm
      _ = _ := by
        simp only [sum_inner, inner_sum]
        exact congrArg Complex.re Finset.sum_comm
  rw [hnorm]
  simp_rw [dbarCore_divergence_pair_identity, Finset.sum_add_distrib, Complex.add_re]
  rw [dbarCore_cross_sum_integral, dbarCore_curvature_sum_integral]

end RepulsiveCoulomb
