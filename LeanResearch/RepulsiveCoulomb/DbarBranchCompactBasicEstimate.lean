module

public import LeanResearch.RepulsiveCoulomb.DbarBranchMetricMatrixMeasurability
public import LeanResearch.RepulsiveCoulomb.DbarBranchCompactDivergenceIdentity

@[expose] public section

/-! The curvature estimate for actual compact vector cores. All differential
operators and the half-Frobenius exterior norm are literal. The passage to the
joint maximal domains is a separate obligation. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped BigOperators ComplexConjugate
namespace RepulsiveCoulomb

def dbarTransformedCoreCurl {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    Matrix (Fin N) (Fin N) ℂ :=
  coulombInverseRootMatrix z * dbarMetricCoreCurl v z * (coulombInverseRootMatrix z).transpose

theorem dbarMetricCoreCurl_entry_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (i j : Fin N) :
    MemLp (fun z => dbarMetricCoreCurl v z i j) 2 (coulombMeasure N β) := by
  have hi := coulombComplexCore_memLp hβ (coulombDbarCoreCoordinateL N i (coulombMetricCoreComponent v j))
  have hj := coulombComplexCore_memLp hβ (coulombDbarCoreCoordinateL N j (coulombMetricCoreComponent v i))
  have h := hi.sub hj
  change MemLp (fun z =>
    coulombDbarCoreCoordinateL N i (coulombMetricCoreComponent v j) z -
      coulombDbarCoreCoordinateL N j (coulombMetricCoreComponent v i) z)
    2 (coulombMeasure N β) at h
  simpa only [dbarMetricCoreCurl, coulombDbarCoreCoordinateL_apply] using h

theorem dbarTransformedCoreCurl_entry_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (i j : Fin N) :
    MemLp (fun z => dbarTransformedCoreCurl v z i j) 2 (coulombMeasure N β) := by
  have hinner (k : Fin N) : MemLp
      (fun z => ∑ l, coulombInverseRootMatrix z i l * dbarMetricCoreCurl v z l k)
      2 (coulombMeasure N β) := by
    exact memLp_finsetSum Finset.univ (fun l _ =>
      (coulombInverseRootMatrix_entry_memLp_top β i l).fun_mul
        (dbarMetricCoreCurl_entry_memLp hβ v l k))
  have hsum : MemLp
      (fun z => ∑ k, (∑ l, coulombInverseRootMatrix z i l * dbarMetricCoreCurl v z l k) *
        coulombInverseRootMatrix z j k) 2 (coulombMeasure N β) :=
    memLp_finsetSum Finset.univ (fun k _ =>
      (hinner k).fun_mul (coulombInverseRootMatrix_entry_memLp_top β j k))
  simpa only [dbarTransformedCoreCurl, Matrix.mul_apply, Matrix.transpose_apply] using hsum

theorem dbarTransformedCoreCurl_energy_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    Integrable (fun z => dbarAlternatingMatrixSq (dbarTransformedCoreCurl v z))
      (coulombMeasure N β) := by
  have hentry (i j : Fin N) : Integrable
      (fun z => ‖dbarTransformedCoreCurl v z i j‖ ^ 2) (coulombMeasure N β) :=
    (dbarTransformedCoreCurl_entry_memLp hβ v i j).integrable_norm_pow (by norm_num)
  exact (integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hentry i j))).const_mul (1 / 2 : ℝ)

theorem dbarCore_cross_integrable {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    Integrable (fun z => dbarMatrixTransposeCross (dbarCoreJacobian v z))
      (coulombMeasure N β) := by
  have hentry (i j : Fin N) : Integrable (fun z =>
      (conj (coulombDbarCoreCoordinateL N j (v i) z) *
        coulombDbarCoreCoordinateL N i (v j) z).re) (coulombMeasure N β) :=
    (dbarComplexCore_weighted_pair_integrable hβ
      (coulombDbarCoreCoordinateL N j (v i)) (coulombDbarCoreCoordinateL N i (v j))).re
  have hs : Integrable (fun z => ∑ i, ∑ j,
      (conj (coulombDbarCoreCoordinateL N j (v i) z) *
        coulombDbarCoreCoordinateL N i (v j) z).re) (coulombMeasure N β) :=
    integrable_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hentry i j))
  simpa only [dbarMatrixTransposeCross, dbarCoreJacobian, coulombDbarCoreCoordinateL_apply, mul_comm] using hs

theorem dbarCore_curl_cross_nonneg {N : ℕ}
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    0 ≤ dbarAlternatingMatrixSq (dbarTransformedCoreCurl v z) +
      dbarMatrixTransposeCross (dbarCoreJacobian v z) := by
  have h := dbarMetricCore_pointwise_identity v hz
  dsimp only at h
  change dbarAlternatingMatrixSq (dbarTransformedCoreCurl v z) +
      dbarMatrixTransposeCross (dbarCoreJacobian v z) = _ at h
  rw [h]
  exact dbarMatrixFrobeniusSq_nonneg _

theorem dbarCore_basic_estimate {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (v : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    (β / 2) * (∫ z, ‖dbarCoreVector v z‖ ^ 2 ∂coulombMeasure N β) ≤
      ‖∑ j, coulombComplexCoreValue hβ (coulombWeightedCoreAdjointCoordinate hβ j (v j))‖ ^ 2 +
        ∫ z, dbarAlternatingMatrixSq (dbarTransformedCoreCurl v z) ∂coulombMeasure N β := by
  have hnonneg : 0 ≤ ∫ z,
      dbarAlternatingMatrixSq (dbarTransformedCoreCurl v z) +
        dbarMatrixTransposeCross (dbarCoreJacobian v z) ∂coulombMeasure N β := by
    apply integral_nonneg_of_ae
    filter_upwards [(coulombMeasure_ae_iff hβ).mpr (coulombDomain_ae N)] with z hz
    exact dbarCore_curl_cross_nonneg v hz
  rw [integral_add (dbarTransformedCoreCurl_energy_integrable hβ v)
    (dbarCore_cross_integrable hβ v)] at hnonneg
  rw [dbarCore_divergence_identity hβ v]
  linarith

end RepulsiveCoulomb
