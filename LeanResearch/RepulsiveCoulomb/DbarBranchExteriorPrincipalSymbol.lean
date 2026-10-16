module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreCoordinates

@[expose] public section

/-! Exact principal-symbol cancellation and the Gram formula for the
half-Frobenius exterior norm. These preserve the normalization used by the
auxiliary complex and its cutoff commutator. -/
noncomputable section
open Set Matrix InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace RepulsiveCoulomb

def dbarVectorWedge {N : ℕ} (a b : CoulombConfig N) : Matrix (Fin N) (Fin N) ℂ :=
  fun i j => a i * b j - b i * a j

theorem dbarVectorWedge_gram {N : ℕ} (a b : CoulombConfig N) :
    dbarAlternatingMatrixSq (dbarVectorWedge a b) =
      ‖a‖ ^ 2 * ‖b‖ ^ 2 - ‖inner ℂ a b‖ ^ 2 := by
  let J : Matrix (Fin N) (Fin N) ℂ := Matrix.of (fun i j => a i * b j)
  have hw : dbarVectorWedge a b = J - J.transpose := by
    ext i j
    change a i * b j - b i * a j = a i * b j - a j * b i
    ring
  have hf : dbarMatrixFrobeniusSq J = ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
    simp only [dbarMatrixFrobeniusSq, J, Matrix.of_apply, norm_mul, mul_pow,
      EuclideanSpace.norm_sq_eq, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have hc : (∑ i, ∑ j, J i j * conj (J j i)) = conj (inner ℂ a b) * inner ℂ a b := by
    calc
      _ = inner ℂ a b * conj (inner ℂ a b) := by
        simp only [J, Matrix.of_apply, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
          Pi.star_apply, Complex.star_def, map_sum, map_mul, Complex.conj_conj,
          Finset.sum_mul, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := mul_comm _ _
  have hcross : dbarMatrixTransposeCross J = ‖inner ℂ a b‖ ^ 2 := by
    have he : (∑ i, ∑ j, a i * b j * conj (a j * b i)).re =
        (conj (inner ℂ a b) * inner ℂ a b).re := congrArg Complex.re hc
    have hn : (conj (inner ℂ a b) * inner ℂ a b).re = ‖inner ℂ a b‖ ^ 2 := by
      have h : (inner ℂ (inner ℂ a b) (inner ℂ a b)).re = ‖inner ℂ a b‖ ^ 2 :=
        inner_self_eq_norm_sq (𝕜 := ℂ) (inner ℂ a b)
      simpa only [RCLike.inner_apply', mul_comm] using h
    change (∑ i, ∑ j, (a i * b j * conj (a j * b i)).re) = _
    simpa only [Complex.re_sum] using he.trans hn
  rw [hw, dbarAlternatingMatrixSq_antisymmetrize, hf, hcross]

theorem dbarVectorWedge_bound {N : ℕ} (a b : CoulombConfig N) :
    dbarAlternatingMatrixSq (dbarVectorWedge a b) ≤ ‖a‖ ^ 2 * ‖b‖ ^ 2 := by
  rw [dbarVectorWedge_gram]
  exact sub_le_self _ (sq_nonneg _)

theorem dbarExterior_principal_matrix {N : ℕ} (R S J : Matrix (Fin N) (Fin N) ℂ)
    (hRS : R * S = 1) :
    R * (J * S.transpose - S * J.transpose) * R.transpose = R * J - (R * J).transpose := by
  calc
    _ = (R * J) * (S.transpose * R.transpose) - (R * S) * (J.transpose * R.transpose) := by noncomm_ring
    _ = _ := by
      rw [← Matrix.transpose_mul, hRS, Matrix.transpose_one, mul_one, one_mul,
        Matrix.transpose_mul]

theorem dbarMetric_exterior_principal_matrix {N : ℕ} (z : CoulombConfig N)
    (J : Matrix (Fin N) (Fin N) ℂ) :
    coulombInverseRootMatrix z *
      (J * (coulombRootMatrix z).transpose - coulombRootMatrix z * J.transpose) *
      (coulombInverseRootMatrix z).transpose =
        coulombInverseRootMatrix z * J - (coulombInverseRootMatrix z * J).transpose := by
  apply dbarExterior_principal_matrix
  rw [coulombInverseRootMatrix, coulombRootMatrix, ← dbarCLMMatrix_comp,
    dbarGraphMetricInverseRoot_root, dbarCLMMatrix_id]

theorem dbarMetric_cutoff_wedge {N : ℕ} (z a u : CoulombConfig N) :
    coulombInverseRootMatrix z *
      dbarVectorWedge a (dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) u) *
      (coulombInverseRootMatrix z).transpose =
        dbarVectorWedge
          (dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z)) a) u := by
  let R := dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
  let S := dbarGraphMetricRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
  have hinv : R (S u) = u :=
    congrArg (fun L : CoulombConfig N →L[ℂ] CoulombConfig N => L u)
      (dbarGraphMetricInverseRoot_root (dbarCovectorRiesz (coulombReciprocalDerivative z)))
  have hgeneral (b : CoulombConfig N) :
      dbarCLMMatrix R * dbarVectorWedge a b * (dbarCLMMatrix R).transpose =
        dbarVectorWedge (R a) (R b) := by
    ext i j
    change (∑ k, (∑ l, dbarCLMMatrix R i l * (a l * b k - b l * a k)) *
      dbarCLMMatrix R j k) = R a i * R b j - R b i * R a j
    rw [dbarCLMMatrix_apply R a i, dbarCLMMatrix_apply R b j,
      dbarCLMMatrix_apply R b i, dbarCLMMatrix_apply R a j]
    calc
      _ = ∑ k, ∑ l, ((dbarCLMMatrix R i l * a l) * (dbarCLMMatrix R j k * b k) -
          (dbarCLMMatrix R i l * b l) * (dbarCLMMatrix R j k * a k)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro l _
        ring
      _ = _ := by
        simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
  change dbarCLMMatrix R * dbarVectorWedge a (S u) * (dbarCLMMatrix R).transpose =
    dbarVectorWedge (R a) u
  rw [hgeneral (S u), hinv]

end RepulsiveCoulomb
