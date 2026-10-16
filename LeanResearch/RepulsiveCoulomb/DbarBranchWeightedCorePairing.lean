import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreIBP
import LeanResearch.RepulsiveCoulomb.DbarBranchComplexLebesguePairing

/-! Exact weighted core pairings with arbitrary Gibbs-L2 data. These formulas
make local density changes in genuine adjoint tests explicit, without assuming
any extra derivative or global unweighted integrability of the data. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators ComplexConjugate
namespace RepulsiveCoulomb

theorem coulombComplexCore_density_inner {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : TestFunction (coulombDomain N) ℂ ⊤) (f : Lp ℂ 2 (coulombMeasure N β)) :
    inner ℂ (coulombComplexCoreValue hβ ψ) f =
      coulombComplexLebesgueTestPairingL hβ (coulombComplexCoreDensityMul β
        (TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap ψ)) f := by
  rw [L2.inner_def, dbarCoulomb_integral_density hβ, coulombComplexLebesgueTestPairingL_apply]
  apply integral_congr_ae
  filter_upwards [(coulombMeasure_ae_iff hβ).mp (coulombComplexCoreValue_coe hβ ψ)] with z hz
  rw [hz, RCLike.inner_apply']
  change (coulombDensity N β z : ℂ) * (conj (ψ z) * f z) =
    ((coulombDensity N β z : ℂ) * conj (ψ z)) * f z
  ring

theorem coulombComplexVectorCoreValue_inner_left {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (ψ : Fin N → TestFunction (coulombDomain N) ℂ ⊤)
    (g : Lp (CoulombConfig N) 2 (coulombMeasure N β)) :
    inner ℂ (coulombComplexVectorCoreValue hβ ψ) g =
      ∑ i, inner ℂ (coulombComplexCoreValue hβ (ψ i))
        ((EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 (coulombMeasure N β) g) := by
  let gi := fun i => (EuclideanSpace.proj (𝕜 := ℂ) i).compLpL 2 (coulombMeasure N β) g
  have hi (i : Fin N) : Integrable (fun z => conj (ψ i z) * g z i) (coulombMeasure N β) := by
    apply (L2.integrable_inner (𝕜 := ℂ) (coulombComplexCoreValue hβ (ψ i)) (gi i)).congr
    filter_upwards [coulombComplexCoreValue_coe hβ (ψ i),
      (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) g] with z hψ hg
    rw [hψ, hg, RCLike.inner_apply']
    rfl
  rw [L2.inner_def]
  calc
    _ = ∫ z, ∑ i, conj (ψ i z) * g z i ∂coulombMeasure N β := by
      apply integral_congr_ae
      filter_upwards [coulombComplexVectorCoreValue_coe hβ ψ] with z hz
      rw [hz, EuclideanSpace.inner_eq_star_dotProduct]
      simp only [dbarCoreVector, WithLp.ofLp_toLp, dotProduct, Pi.star_apply, Complex.star_def, mul_comm]
    _ = ∑ i, ∫ z, conj (ψ i z) * g z i ∂coulombMeasure N β :=
      integral_finsetSum Finset.univ (fun i _ => hi i)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [coulombComplexCoreValue_coe hβ (ψ i),
        (EuclideanSpace.proj (𝕜 := ℂ) i).coeFn_compLpL (p := 2) (μ := coulombMeasure N β) g] with z hψ hg
      rw [hψ, hg, RCLike.inner_apply']
      rfl

theorem coulombRealCore_dbar_conjugate {N : ℕ}
    (φ : TestFunction (coulombDomain N) ℝ ⊤) (i : Fin N) :
    TestFunction.postcompCLM Complex.conjCLE.toContinuousLinearMap
      (coulombDbarCoreCoordinateL N i (TestFunction.postcompCLM Complex.ofRealCLM φ)) =
      coulombDCoreCoordinateL N i (TestFunction.postcompCLM Complex.ofRealCLM φ) := by
  ext z
  change conj (coulombDbarCoreCoordinateL N i (TestFunction.postcompCLM Complex.ofRealCLM φ) z) = _
  rw [coulombDbarCoreCoordinateL_apply, coulombDCoreCoordinateL_apply]
  change conj (coulombDbarCoordinate (fun x => (φ x : ℂ)) z i) =
    coulombDCoordinate (fun x => (φ x : ℂ)) z i
  rw [coulombDbarCoordinate_real (φ.contDiff.differentiable (by simp) z),
    coulombDCoordinate_real (φ.contDiff.differentiable (by simp) z)]
  simp only [map_div₀, map_ofNat]

end RepulsiveCoulomb
