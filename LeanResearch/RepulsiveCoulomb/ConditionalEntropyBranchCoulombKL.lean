import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCoulombLabels
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchKernelIntegral

/-!
Genuine arbitrary-Q one-site conditional laws for the actual Gibbs system.
The manuscript summed conditional entropy is defined by expected fiber KL,
identified with the convenient joint costs, and proved finite under finite
global Gibbs KL. Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

def conditionalEntropyBranchCoulombQKernel {N : ℕ}
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q] (i : Fin (N + 1)) :
    Kernel (CoulombConfig N) ℂ :=
  conditionalEntropyBranchKernel (Q.map (conditionalEntropyBranchCoulombChart i))

instance conditionalEntropyBranchCoulombQKernel_isMarkov {N : ℕ}
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q] (i : Fin (N + 1)) :
    IsMarkovKernel (conditionalEntropyBranchCoulombQKernel Q i) := by
  unfold conditionalEntropyBranchCoulombQKernel
  infer_instance

theorem conditionalEntropyBranch_coulomb_site_chain {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q] (i : Fin (N + 1)) :
    klDiv Q (coulombMeasure (N + 1) β) =
      klDiv (Q.map (conditionalEntropyBranchCoulombChart i)).fst (coulombOneSiteMarginal N β) +
        conditionalEntropyBranchCoulombSiteCost hβ Q i := by
  letI := coulombMeasure_isProbability (N := N + 1) hβ
  letI := coulombOneSiteMarginal_isProbability (N := N) hβ
  have h := klDiv_compProd_eq_add (Q.map (conditionalEntropyBranchCoulombChart i)).fst
    (coulombOneSiteMarginal N β)
    (conditionalEntropyBranchKernel (Q.map (conditionalEntropyBranchCoulombChart i)))
    (coulombOneSiteKernel N β hβ)
  rw [conditionalEntropyBranch_disintegration,
    ← conditionalEntropyBranch_coulomb_chart_law hβ i,
    conditionalEntropyBranch_kl_map_equiv] at h
  exact h

theorem conditionalEntropyBranch_coulomb_site_finite {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞) (i : Fin (N + 1)) :
    conditionalEntropyBranchCoulombSiteCost hβ Q i ≠ ∞ := by
  rw [conditionalEntropyBranch_coulomb_site_chain hβ Q i] at hKL
  exact (ENNReal.add_ne_top.mp hKL).2

theorem conditionalEntropyBranch_coulomb_site_expected_kl {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q] (i : Fin (N + 1)) :
    conditionalEntropyBranchCoulombSiteCost hβ Q i =
      ∫⁻ y, klDiv (conditionalEntropyBranchCoulombQKernel Q i y) (coulombOneSiteKernel N β hβ y)
        ∂(Q.map (conditionalEntropyBranchCoulombChart i)).fst := by
  have h := conditionalEntropyBranch_compProd_kl_integral
    (conditionalEntropyBranchKernel (Q.map (conditionalEntropyBranchCoulombChart i)))
    (coulombOneSiteKernel N β hβ) (Q.map (conditionalEntropyBranchCoulombChart i)).fst
  rw [conditionalEntropyBranch_disintegration] at h
  exact h

theorem conditionalEntropyBranch_coulomb_site_expected_kl_real {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞) (i : Fin (N + 1)) :
    (conditionalEntropyBranchCoulombSiteCost hβ Q i).toReal =
      ∫ y, (klDiv (conditionalEntropyBranchCoulombQKernel Q i y) (coulombOneSiteKernel N β hβ y)).toReal
        ∂(Q.map (conditionalEntropyBranchCoulombChart i)).fst := by
  have hm := conditionalEntropyBranch_fiber_kl_measurable
    (conditionalEntropyBranchCoulombQKernel Q i) (coulombOneSiteKernel N β hβ)
  have hf := conditionalEntropyBranch_coulomb_site_finite hβ Q hKL i
  rw [conditionalEntropyBranch_coulomb_site_expected_kl hβ Q i] at hf ⊢
  exact (integral_toReal hm.aemeasurable (ae_lt_top hm hf)).symm

/-- The manuscript S_N, in its literal averaged conditional KL form. -/
def conditionalEntropyBranchCoulombS {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q] : ℝ≥0∞ :=
  ∑ i : Fin (N + 1), ∫⁻ y,
    klDiv (conditionalEntropyBranchCoulombQKernel Q i y) (coulombOneSiteKernel N β hβ y)
      ∂(Q.map (conditionalEntropyBranchCoulombChart i)).fst

theorem conditionalEntropyBranchCoulombS_eq_sum {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q] :
    conditionalEntropyBranchCoulombS hβ Q =
      ∑ i : Fin (N + 1), conditionalEntropyBranchCoulombSiteCost hβ Q i := by
  simp only [conditionalEntropyBranchCoulombS, conditionalEntropyBranch_coulomb_site_expected_kl]

theorem conditionalEntropyBranchCoulombS_finite {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (Q : Measure (CoulombConfig (N + 1))) [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞) :
    conditionalEntropyBranchCoulombS hβ Q ≠ ∞ := by
  rw [conditionalEntropyBranchCoulombS_eq_sum]
  exact ENNReal.sum_ne_top.mpr (fun i _ => conditionalEntropyBranch_coulomb_site_finite hβ Q hKL i)

end RepulsiveCoulomb
