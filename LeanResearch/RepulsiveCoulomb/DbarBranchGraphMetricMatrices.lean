module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAlternatingMatrixIdentity
public import LeanResearch.RepulsiveCoulomb.DbarBranchCovectorMetric
public import LeanResearch.RepulsiveCoulomb.DbarBranchGraphMetricSquareRoot

@[expose] public section

/-! Apply the exact alternating-matrix identity to the explicit graph metric
square roots. The coordinate matrix convention is M_ij=(M e_j)_i. -/
noncomputable section
open Matrix InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace RepulsiveCoulomb

def dbarCLMMatrix {N : ℕ} (L : CoulombConfig N →L[ℂ] CoulombConfig N) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => L (EuclideanSpace.single j 1) i

theorem dbarEuclidean_basis_sum {N : ℕ} (z : CoulombConfig N) :
    (∑ i, z i • EuclideanSpace.single i 1) = z := by
  ext j
  simp [EuclideanSpace.single, Pi.single_apply, mul_ite, eq_comm]

theorem dbarCLMMatrix_id (N : ℕ) :
    dbarCLMMatrix (ContinuousLinearMap.id ℂ (CoulombConfig N)) = 1 := by
  ext i j
  simp [dbarCLMMatrix, EuclideanSpace.single, Matrix.one_apply, eq_comm]

theorem dbarCLMMatrix_comp {N : ℕ} (L M : CoulombConfig N →L[ℂ] CoulombConfig N) :
    dbarCLMMatrix (L.comp M) = dbarCLMMatrix L * dbarCLMMatrix M := by
  ext i j
  change L (M (EuclideanSpace.single j 1)) i = ∑ k, dbarCLMMatrix L i k * dbarCLMMatrix M k j
  calc
    _ = L (∑ k, (M (EuclideanSpace.single j 1)) k • EuclideanSpace.single k 1) i :=
      congrArg (fun z => L z i) (dbarEuclidean_basis_sum _).symm
    _ = ∑ k, (M (EuclideanSpace.single j 1)) k * L (EuclideanSpace.single k 1) i := by
      simp only [map_sum, map_smul, WithLp.ofLp_sum, WithLp.ofLp_smul,
        Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k _
      exact mul_comm _ _

theorem dbarCLMMatrix_isHermitian {N : ℕ} (L : CoulombConfig N →L[ℂ] CoulombConfig N)
    (hL : ∀ u v, inner ℂ (L u) v = inner ℂ u (L v)) : (dbarCLMMatrix L).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  have h := hL (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)
  simpa only [dbarCLMMatrix, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right,
    map_one, one_mul, starRingEnd_apply] using h

theorem dbarGraphMetric_matrix_entry {N : ℕ} (a : CoulombConfig N) (i j : Fin N) :
    dbarCLMMatrix (dbarGraphMetric a) i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j + a i * conj (a j) := by
  rw [dbarCLMMatrix, dbarGraphMetric_apply]
  simp [EuclideanSpace.single, EuclideanSpace.inner_single_right, Matrix.one_apply, eq_comm, mul_comm]

theorem dbarCovectorMetric_matrix_entry {N : ℕ} (A : CoulombConfig N →L[ℂ] ℂ) (i j : Fin N) :
    dbarCLMMatrix (dbarCovectorMetric A) i j = (1 : Matrix (Fin N) (Fin N) ℂ) i j +
      conj (A (EuclideanSpace.single i 1)) * A (EuclideanSpace.single j 1) := by
  rw [dbarCovectorMetric_eq_rankOne, dbarGraphMetric_matrix_entry,
    dbarCovectorRiesz_coordinate, dbarCovectorRiesz_coordinate]
  simp

theorem dbarGraphMetric_matrices_curl_identity {N : ℕ} (a : CoulombConfig N)
    (J : Matrix (Fin N) (Fin N) ℂ) :
    dbarAlternatingMatrixSq
      (dbarCLMMatrix (dbarGraphMetricInverseRoot a) *
        (J * (dbarCLMMatrix (dbarGraphMetric a)).transpose - dbarCLMMatrix (dbarGraphMetric a) * J.transpose) *
        (dbarCLMMatrix (dbarGraphMetricInverseRoot a)).transpose) +
      dbarMatrixTransposeCross J =
        dbarMatrixFrobeniusSq
          (dbarCLMMatrix (dbarGraphMetricInverseRoot a) * J * (dbarCLMMatrix (dbarGraphMetricRoot a)).transpose) := by
  let S := dbarCLMMatrix (dbarGraphMetricRoot a)
  let R := dbarCLMMatrix (dbarGraphMetricInverseRoot a)
  have hS : S.IsHermitian := dbarCLMMatrix_isHermitian _ (dbarGraphMetricRoot_selfAdjoint_pairing a)
  have hR : R.IsHermitian := dbarCLMMatrix_isHermitian _ (dbarGraphMetricInverseRoot_selfAdjoint_pairing a)
  have hRS : R * S = 1 := by
    rw [← dbarCLMMatrix_comp, dbarGraphMetricInverseRoot_root, dbarCLMMatrix_id]
  have hSR : S * R = 1 := by
    rw [← dbarCLMMatrix_comp, dbarGraphMetricRoot_inverseRoot, dbarCLMMatrix_id]
  have hSS : S * S = dbarCLMMatrix (dbarGraphMetric a) := by
    rw [← dbarCLMMatrix_comp, dbarGraphMetricRoot_square]
  have h := dbarMetric_compact_algebra_identity S R J hS hR hRS hSR
  rw [hSS] at h
  exact h

end RepulsiveCoulomb
