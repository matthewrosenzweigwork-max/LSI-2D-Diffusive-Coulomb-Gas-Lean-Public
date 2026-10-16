import LeanResearch.RepulsiveCoulomb.DbarBranchInverseRootL2
import Mathlib.MeasureTheory.Function.Holder

/-! Literal bounded compact-coefficient multiplication on weighted scalar L2.
These maps are complex-linear; their representatives are the actual products. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RepulsiveCoulomb

def coulombCoreMultiplierL2L {N : ℕ} (β : ℝ)
    (A : TestFunction (coulombDomain N) ℂ ⊤) :
    Lp ℂ 2 (coulombMeasure N β) →L[ℂ] Lp ℂ 2 (coulombMeasure N β) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (coulombMeasure N β) ⊤ 2 2
    ((A.memLp_top (μ := coulombMeasure N β)).toLp A)

theorem coulombCoreMultiplierL2L_coe {N : ℕ} (β : ℝ)
    (A : TestFunction (coulombDomain N) ℂ ⊤) (f : Lp ℂ 2 (coulombMeasure N β)) :
    coulombCoreMultiplierL2L β A f =ᵐ[coulombMeasure N β] fun z => A z * f z := by
  filter_upwards [(ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
      ((A.memLp_top (μ := coulombMeasure N β)).toLp A) f,
    (A.memLp_top (μ := coulombMeasure N β)).coeFn_toLp] with z hz hA
  change ((ContinuousLinearMap.mul ℂ ℂ).holder 2
    ((A.memLp_top (μ := coulombMeasure N β)).toLp A) f) z = _
  rw [hz, hA]
  rfl

theorem coulombCoreMultiplierL2L_norm_le {N : ℕ} (β : ℝ)
    (A : TestFunction (coulombDomain N) ℂ ⊤) {C : ℝ}
    (hC : ∀ᵐ z ∂coulombMeasure N β, ‖A z‖ ≤ C)
    (f : Lp ℂ 2 (coulombMeasure N β)) :
    ‖coulombCoreMultiplierL2L β A f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [coulombCoreMultiplierL2L_coe β A f, hC] with z hz hCz
  rw [hz, norm_mul]
  exact mul_le_mul_of_nonneg_right hCz (norm_nonneg _)

theorem coulombCoreMultiplierL2L_core {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (A φ : TestFunction (coulombDomain N) ℂ ⊤) :
    coulombCoreMultiplierL2L β A (coulombComplexCoreValue hβ φ) =
      coulombComplexCoreValue hβ
        (coulombComplexCoreMulLocal A (fun z _ => A.contDiff.contDiffAt) φ) := by
  apply Lp.ext
  filter_upwards [coulombCoreMultiplierL2L_coe β A (coulombComplexCoreValue hβ φ),
    coulombComplexCoreValue_coe hβ φ,
    coulombComplexCoreValue_coe hβ (coulombComplexCoreMulLocal A (fun z _ => A.contDiff.contDiffAt) φ)]
    with z hM hφ hprod
  rw [hM, hφ, hprod]
  rfl

end RepulsiveCoulomb
