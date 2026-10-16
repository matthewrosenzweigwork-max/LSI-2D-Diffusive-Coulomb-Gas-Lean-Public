module

public import LeanResearch.RepulsiveCoulomb.DbarBranchAuxiliaryCoreIBP
public import LeanResearch.RepulsiveCoulomb.DbarBranchTwoFormFiber
public import LeanResearch.RepulsiveCoulomb.DbarBranchMetricCutoffL2

@[expose] public section

/-! The actual compact estimate expressed in fixed-fiber L2 norms, including
the exact i<j exterior normalization. The final lemma passes this proved
compact estimate along one sequence with both outputs converging; constructing
that sequence for genuine cutoff data remains a separate application. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem coulombAuxiliaryCoreCurl_antisymmetric {N : ℕ}
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) (i j : Fin N) :
    coulombAuxiliaryCoreCurl u z j i = -coulombAuxiliaryCoreCurl u z i j := by
  have hF : (dbarMetricCoreCurl (coulombInverseRootCore u) z).transpose =
      -dbarMetricCoreCurl (coulombInverseRootCore u) z := by
    ext k l
    exact dbarMetricCoreCurl_antisymmetric _ z k l
  have ht : (coulombAuxiliaryCoreCurl u z).transpose = -coulombAuxiliaryCoreCurl u z := by
    simp_rw [coulombAuxiliaryCoreCurl_eq]
    unfold dbarTransformedCoreCurl
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hF,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  exact congrArg (fun M : Matrix (Fin N) (Fin N) ℂ => M i j) ht

def coulombAuxiliaryCoreTwoForm {N : ℕ}
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    CoulombAuxiliaryTwoForm N :=
  WithLp.toLp 2 (fun p : coulombPairs N => coulombAuxiliaryCoreCurl u z p.1.1 p.1.2)

theorem coulombAuxiliaryCoreTwoForm_norm_sq {N : ℕ}
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) (z : CoulombConfig N) :
    ‖coulombAuxiliaryCoreTwoForm u z‖ ^ 2 = dbarAlternatingMatrixSq (coulombAuxiliaryCoreCurl u z) := by
  rw [dbarAlternatingMatrixSq_pairs _ (coulombAuxiliaryCoreCurl_antisymmetric u z),
    EuclideanSpace.norm_sq_eq]
  simp only [coulombAuxiliaryCoreTwoForm, WithLp.ofLp_toLp]
  exact Finset.sum_coe_sort (coulombPairs N)
    (fun p : Fin N × Fin N => ‖coulombAuxiliaryCoreCurl u z p.1 p.2‖ ^ 2)

theorem coulombAuxiliaryCoreTwoForm_memLp {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    MemLp (coulombAuxiliaryCoreTwoForm u) 2 (coulombMeasure N β) := by
  apply memLp_piLp_iff.mpr
  intro p
  change MemLp (fun z => coulombAuxiliaryCoreCurl u z p.1.1 p.1.2) 2 (coulombMeasure N β)
  simp_rw [coulombAuxiliaryCoreCurl_eq]
  exact dbarTransformedCoreCurl_entry_memLp hβ (coulombInverseRootCore u) p.1.1 p.1.2

def coulombAuxiliaryCoreCurlValue {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    Lp (CoulombAuxiliaryTwoForm N) 2 (coulombMeasure N β) :=
  (coulombAuxiliaryCoreTwoForm_memLp hβ u).toLp (coulombAuxiliaryCoreTwoForm u)

theorem coulombAuxiliaryCoreCurlValue_coe {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    coulombAuxiliaryCoreCurlValue hβ u =ᵐ[coulombMeasure N β] coulombAuxiliaryCoreTwoForm u :=
  MemLp.coeFn_toLp _

theorem coulombAuxiliaryCoreCurlValue_norm_sq {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    ‖coulombAuxiliaryCoreCurlValue hβ u‖ ^ 2 =
      ∫ z, dbarAlternatingMatrixSq (coulombAuxiliaryCoreCurl u z) ∂coulombMeasure N β := by
  rw [dbarRealHilbertLp_norm_sq]
  apply integral_congr_ae
  filter_upwards [coulombAuxiliaryCoreCurlValue_coe hβ u] with z hz
  rw [hz, coulombAuxiliaryCoreTwoForm_norm_sq]

theorem coulombAuxiliaryCore_basic_estimate_L2 {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (u : Fin N → TestFunction (coulombDomain N) ℂ ⊤) :
    (β / 2) * ‖coulombInverseRootL2L N β (coulombComplexVectorCoreValue hβ u)‖ ^ 2 ≤
      ‖coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ u)‖ ^ 2 +
        ‖coulombAuxiliaryCoreCurlValue hβ u‖ ^ 2 := by
  have hR : ‖coulombInverseRootL2L N β (coulombComplexVectorCoreValue hβ u)‖ ^ 2 =
      ∫ z, ‖dbarGraphMetricInverseRoot (dbarCovectorRiesz (coulombReciprocalDerivative z))
        (dbarCoreVector u z)‖ ^ 2 ∂coulombMeasure N β := by
    rw [dbarRealHilbertLp_norm_sq]
    apply integral_congr_ae
    filter_upwards [coulombInverseRootL2_coe β (coulombComplexVectorCoreValue hβ u),
      coulombComplexVectorCoreValue_coe hβ u] with z hR hu
    change ‖coulombInverseRootL2 β (coulombComplexVectorCoreValue hβ u) z‖ ^ 2 = _
    rw [hR, hu]
  rw [hR, coulombAuxiliaryCoreCurlValue_norm_sq]
  exact coulombAuxiliaryCore_basic_estimate hβ u

theorem coulombAuxiliaryCore_basic_estimate_of_joint_limit {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (φ : ℕ → Fin N → TestFunction (coulombDomain N) ℂ ⊤)
    (u : Lp (CoulombConfig N) 2 (coulombMeasure N β))
    (h : Lp ℂ 2 (coulombMeasure N β))
    (e : Lp (CoulombAuxiliaryTwoForm N) 2 (coulombMeasure N β))
    (hu : Tendsto (fun n => coulombComplexVectorCoreValue hβ (φ n)) atTop (𝓝 u))
    (hh : Tendsto (fun n => coulombComplexCoreValue hβ (coulombAuxiliaryCoreDivergence hβ (φ n)))
      atTop (𝓝 h))
    (he : Tendsto (fun n => coulombAuxiliaryCoreCurlValue hβ (φ n)) atTop (𝓝 e)) :
    (β / 2) * ‖coulombInverseRootL2L N β u‖ ^ 2 ≤ ‖h‖ ^ 2 + ‖e‖ ^ 2 := by
  have hRu := ((coulombInverseRootL2L N β).continuous.continuousAt.tendsto.comp hu).norm.pow 2
  exact le_of_tendsto_of_tendsto (hRu.const_mul (β / 2)) ((hh.norm.pow 2).add (he.norm.pow 2))
    (Eventually.of_forall fun n => coulombAuxiliaryCore_basic_estimate_L2 hβ (φ n))

end RepulsiveCoulomb
