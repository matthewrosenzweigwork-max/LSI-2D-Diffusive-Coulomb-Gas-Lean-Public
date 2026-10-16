module

public import LeanResearch.RepulsiveCoulomb.DbarBranchComplexVectorCore
public import LeanResearch.RepulsiveCoulomb.DbarBranchInverseRootL2

@[expose] public section

/-! Genuine compact integration by parts for T0 f=R dbar f in the ordinary
weighted Hilbert spaces. It supplies dense formal-adjoint test values for
closability, without asserting any adjoint graph-core density. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators ComplexConjugate
namespace RepulsiveCoulomb

theorem coulombComplexVectorCoreValue_inner {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    inner ℂ (coulombComplexVectorCoreValue hβ u) (coulombComplexVectorCoreValue hβ v) =
      ∑ i, inner ℂ (coulombComplexCoreValue hβ (u i)) (coulombComplexCoreValue hβ (v i)) := by
  rw [L2.inner_def]
  calc
    _ = ∫ z, ∑ i, conj (u i z) * v i z ∂coulombMeasure N β := by
      apply integral_congr_ae
      filter_upwards [coulombComplexVectorCoreValue_coe hβ u, coulombComplexVectorCoreValue_coe hβ v] with z hu hv
      rw [hu, hv, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dbarCoreVector, WithLp.ofLp_toLp, dotProduct, Pi.star_apply, Complex.star_def, mul_comm]
    _ = ∑ i, ∫ z, conj (u i z) * v i z ∂coulombMeasure N β :=
      integral_finsetSum Finset.univ (fun i _ => dbarComplexCore_weighted_pair_integrable hβ (u i) (v i))
    _ = _ := Finset.sum_congr rfl (fun i _ => (dbarComplexCore_inner_eq_integral hβ (u i) (v i)).symm)

theorem coulombComplexVectorCoreValue_dbar {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombComplexVectorCoreValue hβ (fun i => coulombDbarCoreCoordinateL N i φ) =
      coulombComplexCoreDbar hβ φ := by
  apply Lp.ext
  filter_upwards [coulombComplexVectorCoreValue_coe hβ (fun i => coulombDbarCoreCoordinateL N i φ),
    coulombComplexCoreDbar_coe hβ φ] with z hu hφ
  rw [hu, hφ]
  ext i
  exact coulombDbarCoreCoordinateL_apply N i φ z

def coulombComplexDbarCoreLinear (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    TestFunction (coulombDomain N) ℂ ⊤ →ₗ[ℂ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombComplexVectorCoreValueLinear N hβ).comp
    (LinearMap.pi (fun i => (coulombDbarCoreCoordinateL N i).toLinearMap))

theorem coulombComplexDbarCoreLinear_apply {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombComplexDbarCoreLinear N hβ φ = coulombComplexCoreDbar hβ φ :=
  coulombComplexVectorCoreValue_dbar hβ φ

theorem coulombInverseRootL2L_core {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    coulombInverseRootL2L N β (coulombComplexVectorCoreValue hβ u) =
      coulombComplexVectorCoreValue hβ (coulombInverseRootCore u) := by
  apply Lp.ext
  filter_upwards [coulombInverseRootL2_coe β (coulombComplexVectorCoreValue hβ u),
    coulombComplexVectorCoreValue_coe hβ u, coulombComplexVectorCoreValue_coe hβ (coulombInverseRootCore u)]
    with z hR hu hv
  change coulombInverseRootL2 β (coulombComplexVectorCoreValue hβ u) z = _
  rw [hR, hu, hv, coulombInverseRootCore_vector]

def coulombAuxiliaryCoreDerivativeL (N : ℕ) {β : ℝ} (hβ : 0 < β) :
    TestFunction (coulombDomain N) ℂ ⊤ →ₗ[ℂ] Lp (CoulombConfig N) 2 (coulombMeasure N β) :=
  (coulombInverseRootL2L N β).toLinearMap.comp (coulombComplexDbarCoreLinear N hβ)

theorem coulombCore_vector_ibp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    inner ℂ (coulombComplexCoreDbar hβ φ) (coulombComplexVectorCoreValue hβ u) =
      inner ℂ (coulombComplexCoreValue hβ φ)
        (coulombComplexCoreValue hβ (∑ j, coulombWeightedCoreAdjointCoordinate hβ j (u j))) := by
  rw [← coulombComplexVectorCoreValue_dbar hβ φ, coulombComplexVectorCoreValue_inner]
  simp_rw [← dbarComplexCore_adjoint_inner_right]
  rw [← inner_sum]
  congr 1
  exact (map_sum (coulombComplexCoreValueLinear N hβ) _ _).symm

theorem coulombAuxiliaryCore_ibp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : TestFunction (coulombDomain N) ℂ ⊤)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    inner ℂ (coulombAuxiliaryCoreDerivativeL N hβ φ) (coulombComplexVectorCoreValue hβ u) =
      inner ℂ (coulombComplexCoreValue hβ φ)
        (coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ u)) := by
  change inner ℂ (coulombInverseRootL2L N β (coulombComplexDbarCoreLinear N hβ φ)) _ = _
  rw [coulombComplexDbarCoreLinear_apply, coulombInverseRootL2L_selfAdjoint_pairing,
    coulombInverseRootL2L_core, coulombCore_vector_ibp]
  rfl

end RepulsiveCoulomb
