module

public import LeanResearch.RepulsiveCoulomb.DbarBranchGraphKahler
public import LeanResearch.RepulsiveCoulomb.DbarBranchLocalCoreMultiplier

@[expose] public section

/-! Actual compact covectors g=Hv and the exact cancellation of derivatives
of H in their exterior dbar. This applies the finite matrix algebra to the
literal coordinate derivatives of genuine compact smooth functions. -/
noncomputable section
open Set Matrix InnerProductSpace
open scoped BigOperators
namespace RepulsiveCoulomb

def coulombMetricCoreComponent {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (j : Fin N) :
    TestFunction (coulombDomain N) ℂ ⊤ :=
  ∑ k, coulombComplexCoreMulLocal
    (fun w => dbarCLMMatrix (coulombReciprocalGraphMetric w) j k)
    (fun z hz => coulombReciprocalGraphMetric_entry_contDiffAt j k hz) (v k)

theorem coulombMetricCoreComponent_apply {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (j : Fin N) (z : CoulombConfig N) :
    coulombMetricCoreComponent v j z = ∑ k, dbarCLMMatrix (coulombReciprocalGraphMetric z) j k * v k z := by
  simp only [coulombMetricCoreComponent, _root_.sum_apply, coulombComplexCoreMulLocal_apply]

def dbarCoreJacobian {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => coulombDbarCoordinate (v j) z i

def dbarMetricCoreCurl {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => coulombDbarCoordinate (coulombMetricCoreComponent v j) z i -
    coulombDbarCoordinate (coulombMetricCoreComponent v i) z j

theorem coulombMetricCoreComponent_dbar {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (i j : Fin N)
    {z : CoulombConfig N} (hz : z ∈ coulombDomain N) :
    coulombDbarCoordinate (coulombMetricCoreComponent v j) z i =
      ∑ k, (dbarCLMMatrix (coulombReciprocalGraphMetric z) j k * coulombDbarCoordinate (v k) z i +
        v k z * coulombDbarCoordinate (fun w => dbarCLMMatrix (coulombReciprocalGraphMetric w) j k) z i) := by
  rw [← coulombDbarCoreCoordinateL_apply N i, coulombMetricCoreComponent, map_sum]
  simp only [_root_.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  rw [coulombDbarCoreCoordinateL_apply]
  change coulombDbarCoordinate
    (fun w => dbarCLMMatrix (coulombReciprocalGraphMetric w) j k * v k w) z i = _
  exact coulombDbarCoordinate_mul
    ((coulombReciprocalGraphMetric_entry_contDiffAt j k hz).differentiableAt (by simp))
    ((v k).contDiff.differentiable (by simp) z) i

theorem dbarMetricCoreCurl_eq_matrix {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    dbarMetricCoreCurl v z =
      dbarCoreJacobian v z * (dbarCLMMatrix (coulombReciprocalGraphMetric z)).transpose -
        dbarCLMMatrix (coulombReciprocalGraphMetric z) * (dbarCoreJacobian v z).transpose := by
  ext i j
  change coulombDbarCoordinate (coulombMetricCoreComponent v j) z i -
    coulombDbarCoordinate (coulombMetricCoreComponent v i) z j = _
  rw [coulombMetricCoreComponent_dbar v i j hz, coulombMetricCoreComponent_dbar v j i hz]
  simp only [Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, dbarCoreJacobian,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [coulombReciprocalGraphMetric_kahler i j k hz]
  ring

theorem dbarMetricCoreCurl_antisymmetric {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) (i j : Fin N) :
    dbarMetricCoreCurl v z j i = -dbarMetricCoreCurl v z i j := by
  unfold dbarMetricCoreCurl
  ring

theorem dbarMetricCore_pointwise_identity {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    let a := dbarCovectorRiesz (coulombReciprocalDerivative z)
    let R := dbarCLMMatrix (dbarGraphMetricInverseRoot a)
    let S := dbarCLMMatrix (dbarGraphMetricRoot a)
    dbarAlternatingMatrixSq (R * dbarMetricCoreCurl v z * R.transpose) + dbarMatrixTransposeCross (dbarCoreJacobian v z) =
      dbarMatrixFrobeniusSq (R * dbarCoreJacobian v z * S.transpose) := by
  dsimp only
  rw [dbarMetricCoreCurl_eq_matrix v hz]
  have he : coulombReciprocalGraphMetric z = dbarGraphMetric (dbarCovectorRiesz (coulombReciprocalDerivative z)) :=
    dbarCovectorMetric_eq_rankOne (coulombReciprocalDerivative z)
  rw [he]
  exact dbarGraphMetric_matrices_curl_identity _ _

end RepulsiveCoulomb
