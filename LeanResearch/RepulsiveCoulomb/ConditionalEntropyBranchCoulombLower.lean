import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCanonicalEntropy
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchConditionalIntegrability
import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchIntegratedTilt

/-!
Actual one-site lower comparison and its summed pre-variational entropy bound
for every labeled finite-entropy competitor under the original B hypothesis.
The product Han--Shearer inequality, arbitrary-Q conditional construction,
thermal tilt identity, signed integrability, and ordered counting are supplied
by proved-in-source modules. No analytic tensorization premise is introduced.
All new source remains records-only and uncompiled.
-/
noncomputable section
open MeasureTheory ProbabilityTheory InformationTheory Real Filter
open scoped ENNReal BigOperators
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_coulomb_site_lower {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) (i : Fin (N + 1)) :
    (conditionalEntropyBranchCost (Q.map (conditionalEntropyBranchCoulombChart i))
      (R.measure : Measure ℂ)).toReal +
      β * (∫ z, (conditionalEntropyBranchThermalPhi R
        (conditionalEntropyBranchCoulombChart i z).1 (conditionalEntropyBranchCoulombChart i z).2 -
        ∫ w, conditionalEntropyBranchThermalPhi R (conditionalEntropyBranchCoulombChart i z).1 w
          ∂(R.measure : Measure ℂ)) ∂Q) ≤
      (conditionalEntropyBranchCoulombSiteCost hβ Q i).toReal := by
  have hProduct := conditionalEntropyBranch_product_entropy_finite hβ R hKL hB
  have hBase : conditionalEntropyBranchCost (Q.map (conditionalEntropyBranchCoulombChart i))
      (R.measure : Measure ℂ) ≠ ∞ := by
    rw [conditionalEntropyBranch_coulomb_base_cost]
    exact (conditionalEntropyBranch_site_finite _ _ hProduct i).2
  have hMean := conditionalEntropyBranch_reference_mean_integrable hβ R hKL hB i
  have h := conditionalEntropyBranch_integrated_tilt_lower
    (Q.map (conditionalEntropyBranchCoulombChart i)) (R.measure : Measure ℂ)
    (coulombOneSiteKernel N β hβ) β
    (fun p : CoulombConfig N × ℂ => conditionalEntropyBranchThermalPhi R p.1 p.2)
    (conditionalEntropyBranch_phi_joint_integrable hβ R hKL hB i)
    (conditionalEntropyBranch_reference_phi_integrable R)
    (conditionalEntropyBranch_thermal_exp_integrable hβ R) hMean
    (fun y => (conditionalEntropyBranch_thermal_tilt_eq_kernel hβ R y).symm) hBase
    (conditionalEntropyBranch_coulomb_site_finite hβ Q hKL i)
  have hPhiEq :
      (∫ p : CoulombConfig N × ℂ, conditionalEntropyBranchThermalPhi R p.1 p.2
        ∂Q.map (conditionalEntropyBranchCoulombChart i)) =
      ∫ z, conditionalEntropyBranchThermalPhi R (conditionalEntropyBranchCoulombChart i z).1
        (conditionalEntropyBranchCoulombChart i z).2 ∂Q :=
    integral_map (conditionalEntropyBranchCoulombChart i).measurable.aemeasurable
      (conditionalEntropyBranchThermalPhi_measurable R).aestronglyMeasurable
  have hMm : Measurable (fun y : CoulombConfig N => ∫ w,
      conditionalEntropyBranchThermalPhi R y w ∂(R.measure : Measure ℂ)) :=
    (conditionalEntropyBranchThermalPhi_measurable R).stronglyMeasurable.integral_prod_right'.measurable
  have hMeanEq :
      (∫ y : CoulombConfig N, ∫ w, conditionalEntropyBranchThermalPhi R y w
        ∂(R.measure : Measure ℂ) ∂(Q.map (conditionalEntropyBranchCoulombChart i)).fst) =
      ∫ z, ∫ w, conditionalEntropyBranchThermalPhi R (conditionalEntropyBranchCoulombChart i z).1 w
        ∂(R.measure : Measure ℂ) ∂Q := by
    have hMmJoint : Measurable (fun p : CoulombConfig N × ℂ =>
        ∫ w, conditionalEntropyBranchThermalPhi R p.1 w ∂(R.measure : Measure ℂ)) :=
      hMm.comp measurable_fst
    rw [Measure.fst, integral_map measurable_fst.aemeasurable hMm.aestronglyMeasurable]
    exact integral_map (μ := Q)
      (conditionalEntropyBranchCoulombChart i).measurable.aemeasurable
        hMmJoint.aestronglyMeasurable
  rw [hPhiEq, hMeanEq, ← integral_sub
    (conditionalEntropyBranch_phi_comp_integrable hβ R hKL hB i)
    (conditionalEntropyBranch_reference_mean_comp_integrable hβ R hKL hB i)] at h
  exact h

/-- The exact intermediate inequality S_N(Q) >= H(Q|P)+beta E_Q B-log K,
with no subtraction of infinite quantities. -/
theorem conditionalEntropyBranch_coulomb_pre_variational_lower {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig (N + 1))} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure (N + 1) β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) :
    (klDiv Q (coulombMeasure (N + 1) β)).toReal +
      β * (∫ z, conditionalEntropyBranchThermalB R z ∂Q) -
      Real.log (equilibriumReferencePartition (N + 1) β R) ≤
        (conditionalEntropyBranchCoulombS hβ Q).toReal := by
  have hProduct := conditionalEntropyBranch_product_entropy_finite hβ R hKL hB
  have hHan :
      (klDiv (Q.map (@WithLp.ofLp 2 (Fin (N + 1) → ℂ)))
        (Measure.pi (fun _ : Fin (N + 1) => (R.measure : Measure ℂ)))).toReal ≤
      ∑ i : Fin (N + 1), (conditionalEntropyBranchCost
        (Q.map (conditionalEntropyBranchCoulombChart i)) (R.measure : Measure ℂ)).toReal := by
    simpa only [conditionalEntropyBranch_coulomb_base_cost] using
      conditionalEntropyBranch_han_shearer_real _ _ hProduct
  let D : Fin (N + 1) → CoulombConfig (N + 1) → ℝ := fun i z =>
    conditionalEntropyBranchThermalPhi R (conditionalEntropyBranchCoulombChart i z).1
      (conditionalEntropyBranchCoulombChart i z).2 -
      ∫ w, conditionalEntropyBranchThermalPhi R (conditionalEntropyBranchCoulombChart i z).1 w
        ∂(R.measure : Measure ℂ)
  have hDi (i : Fin (N + 1)) : Integrable (D i) Q :=
    (conditionalEntropyBranch_phi_comp_integrable hβ R hKL hB i).sub
      (conditionalEntropyBranch_reference_mean_comp_integrable hβ R hKL hB i)
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    (fun i _ => conditionalEntropyBranch_coulomb_site_lower hβ R hKL hB i)
  change (∑ i, ((conditionalEntropyBranchCost (Q.map (conditionalEntropyBranchCoulombChart i))
      (R.measure : Measure ℂ)).toReal + β * ∫ z, D i z ∂Q)) ≤ _ at hsum
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    ← integral_finsetSum Finset.univ (fun i _ => hDi i)] at hsum
  have hD : (∫ z, ∑ i, D i z ∂Q) =
      ∫ z, (2 * equilibriumModulatedEnergy R.density (WithLp.ofLp z) +
        (∑ i, equilibriumDensityPotential R.density (z i)) / ((N + 1 : ℕ) : ℝ)) ∂Q := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun z => conditionalEntropyBranch_thermal_centered_sum R z)
  rw [hD] at hsum
  have hA := (conditionalEntropyBranch_finite_entropy_A_integrable hβ R hKL hB).2
  have hU := conditionalEntropyBranch_thermal_sum_integrable R
    (coulomb_finite_entropy_quadratic_moment hβ hKL).1
  rw [integral_add (hA.const_mul 2) (hU.div_const _), integral_const_mul, integral_div] at hsum
  have hBint : (∫ z, conditionalEntropyBranchThermalB R z ∂Q) =
      (∫ z, equilibriumModulatedEnergy R.density (WithLp.ofLp z) ∂Q) +
        (∫ z, ∑ i, equilibriumDensityPotential R.density (z i) ∂Q) / ((N + 1 : ℕ) : ℝ) := by
    unfold conditionalEntropyBranchThermalB
    rw [integral_add hA (hU.div_const _), integral_div]
  have hEntropy := conditionalEntropyBranch_canonical_entropy_identity hβ R hKL hB
  have hSreal : (conditionalEntropyBranchCoulombS hβ Q).toReal =
      ∑ i : Fin (N + 1), (conditionalEntropyBranchCoulombSiteCost hβ Q i).toReal := by
    rw [conditionalEntropyBranchCoulombS_eq_sum,
      ENNReal.toReal_sum (fun i _ => conditionalEntropyBranch_coulomb_site_finite hβ Q hKL i)]
  rw [hSreal, hBint, hEntropy]
  nlinarith [hHan, hsum]

end RepulsiveCoulomb
