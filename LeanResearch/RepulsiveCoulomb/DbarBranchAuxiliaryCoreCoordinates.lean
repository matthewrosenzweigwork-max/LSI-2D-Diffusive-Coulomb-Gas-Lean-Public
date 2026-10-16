module

public import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCoefficientSmoothness
public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactBasicEstimate

@[expose] public section

/-! Realize the compact metric inequality in ordinary fixed-fiber auxiliary
coordinates u: the scalar adjoint is delta(Ru), the raw exterior coefficient
is S u, and curvature controls the Euclidean square of R u. -/
noncomputable section
open Set MeasureTheory InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb

theorem dbarCLMMatrix_apply {N : ℕ} (L : CoulombConfig N →L[ℂ] CoulombConfig N)
    (u : CoulombConfig N) (i : Fin N) :
    L u i = ∑ j, dbarCLMMatrix L i j * u j := by
  calc
    _ = L (∑ j, u j • EuclideanSpace.single j 1) i :=
      congrArg (fun x => L x i) (dbarEuclidean_basis_sum u).symm
    _ = _ := by
      simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul, dbarCLMMatrix]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)

def coulombRootCore {N : ℕ} (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤)
    (i : Fin N) : TestFunction (coulombDomain N) ℂ ⊤ :=
  ∑ j, coulombComplexCoreMulLocal (fun z => coulombRootMatrix z i j)
    (fun z hz => coulombRootMatrix_entry_contDiffAt i j hz) (u j)

def coulombInverseRootCore {N : ℕ} (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤)
    (i : Fin N) : TestFunction (coulombDomain N) ℂ ⊤ :=
  ∑ j, coulombComplexCoreMulLocal (fun z => coulombInverseRootMatrix z i j)
    (fun z hz => coulombInverseRootMatrix_entry_contDiffAt i j hz) (u j)

theorem coulombRootCore_vector {N : ℕ} (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤)
    (z : CoulombConfig N) :
    dbarCoreVector (coulombRootCore u) z =
      dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (dbarCoreVector u z) := by
  ext i
  rw [dbarCLMMatrix_apply]
  simp only [dbarCoreVector, WithLp.ofLp_toLp, coulombRootCore, _root_.sum_apply,
    coulombComplexCoreMulLocal_apply, coulombRootMatrix]

theorem coulombInverseRootCore_vector {N : ℕ} (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤)
    (z : CoulombConfig N) :
    dbarCoreVector (coulombInverseRootCore u) z =
      dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) (dbarCoreVector u z) := by
  ext i
  rw [dbarCLMMatrix_apply]
  simp only [dbarCoreVector, WithLp.ofLp_toLp, coulombInverseRootCore, _root_.sum_apply,
    coulombComplexCoreMulLocal_apply, coulombInverseRootMatrix]

theorem coulombMetricCore_vector {N : ℕ} (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤)
    (z : CoulombConfig N) :
    dbarCoreVector (coulombMetricCoreComponent u) z = coulombReciprocalGraphMetric z (dbarCoreVector u z) := by
  ext i
  rw [dbarCLMMatrix_apply]
  simp only [dbarCoreVector, WithLp.ofLp_toLp, coulombMetricCoreComponent_apply]

theorem coulombRootCore_inverseRootCore {N : ℕ}
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    coulombRootCore (coulombInverseRootCore u) = u := by
  funext i
  ext z
  have h := congrArg (fun w : CoulombConfig N => w i)
    (coulombRootCore_vector (coulombInverseRootCore u) z)
  rw [coulombInverseRootCore_vector] at h
  have hinv := congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L (dbarCoreVector u z))
    (dbarGraphMetricRoot_inverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)))
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, dbarCoreVector,
    WithLp.ofLp_toLp] using h.trans (congrArg (fun w : CoulombConfig N => w i) hinv)

theorem coulombMetricCore_inverseRootCore {N : ℕ}
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    coulombMetricCoreComponent (coulombInverseRootCore u) = coulombRootCore u := by
  funext i
  ext z
  have hH := coulombMetricCore_vector (coulombInverseRootCore u) z
  rw [coulombInverseRootCore_vector, coulombReciprocalGraphMetric, dbarCovectorMetric_eq_rankOne,
    ← dbarGraphMetricRoot_square] at hH
  have hR := coulombRootCore_vector u z
  have hinv := congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L (dbarCoreVector u z))
    (dbarGraphMetricRoot_inverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hinv hH
  rw [hinv] at hH
  exact congrArg (fun w : CoulombConfig N => w i) (hH.trans hR.symm)

def coulombAuxiliaryCoreDivergence {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) : TestFunction (coulombDomain N) ℂ ⊤ :=
  ∑ j, coulombWeightedCoreAdjointCoordinate hβ j (coulombInverseRootCore u j)

def coulombAuxiliaryCoreCurl {N : ℕ}
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    Matrix (Fin N) (Fin N) ℂ :=
  coulombInverseRootMatrix z *
    Matrix.of (fun i j => coulombDbarCoordinate (coulombRootCore u j) z i -
      coulombDbarCoordinate (coulombRootCore u i) z j) *
        (coulombInverseRootMatrix z).transpose

theorem coulombAuxiliaryCoreCurl_eq {N : ℕ}
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    coulombAuxiliaryCoreCurl u z = dbarTransformedCoreCurl (coulombInverseRootCore u) z := by
  unfold coulombAuxiliaryCoreCurl dbarTransformedCoreCurl dbarMetricCoreCurl
  rw [coulombMetricCore_inverseRootCore]
  rfl

theorem coulombAuxiliaryCore_basic_estimate {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    (β / 2) * (∫ z, ‖dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
      (dbarCoreVector u z)‖ ^ 2 ∂coulombMeasure N β) ≤
      ‖coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ u)‖ ^ 2 +
        ∫ z, dbarAlternatingMatrixSq (coulombAuxiliaryCoreCurl u z) ∂coulombMeasure N β := by
  have h := dbarCore_basic_estimate hβ (coulombInverseRootCore u)
  have hdiv : coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ u) =
      ∑ j, coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (coulombInverseRootCore u j)) :=
    map_sum (coulombComplexCoreValueLinear N hβ) _ _
  simpa only [coulombInverseRootCore_vector, ← coulombAuxiliaryCoreCurl_eq, ← hdiv] using h

end RepulsiveCoulomb
