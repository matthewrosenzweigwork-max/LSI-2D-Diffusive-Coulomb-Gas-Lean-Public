module

public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchCompetitorIntegrability
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchTilt
public import LeanResearch.RepulsiveCoulomb.ConditionalEntropyBranchBinaryKL
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCanonicalSplitting

@[expose] public section

/-!
Actual canonical/modulated entropy correspondence for finite-KL competitors.
A-integrability is derived from the manuscript B hypothesis and the genuine
finite-entropy moment adapter before applying the scalar tilted-law identity.
All constructed-reference/splitting dependencies remain explicit uncompiled
future inputs. Records-only draft, not staged or checked.
-/
noncomputable section
open MeasureTheory InformationTheory
open scoped ENNReal
namespace RepulsiveCoulomb

theorem conditionalEntropyBranch_product_entropy_finite {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig N)} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure N β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) :
    klDiv (Q.map (@WithLp.ofLp 2 (Fin N → ℂ)))
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) ≠ ∞ := by
  letI := coulombMeasure_isProbability (N := N) hβ
  let e := (MeasurableEquiv.toLp 2 (Fin N → ℂ)).symm
  have hLaw : (coulombMeasure N β).map e =
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))).tilted
        (fun z => -β * equilibriumModulatedEnergy R.density z) := by
    simpa only [e, MeasurableEquiv.coe_toLp_symm] using
      equilibriumReference_coulombMeasure_eq_tilted hβ R N
  have hA := (conditionalEntropyBranch_finite_entropy_A_integrable hβ R hKL hB).2
  have hAm := equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable (N := N)
  have hAmap : Integrable (equilibriumModulatedEnergy R.density) (Q.map e) :=
    (integrable_map_measure hAm.aestronglyMeasurable e.measurable.aemeasurable).mpr hA
  have htilt : klDiv (Q.map e)
      ((Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))).tilted
        (fun z => -β * equilibriumModulatedEnergy R.density z)) ≠ ∞ := by
    rw [← hLaw,
      conditionalEntropyBranch_kl_map_equiv Q (coulombMeasure N β) e]
    exact hKL
  exact conditionalEntropyBranch_base_finite_of_tilt
    (equilibriumReference_canonical_exp_integrable hβ R N) (hAmap.const_mul (-β)) htilt

/-- The exact Gibbs/product relative-entropy equality, with every term finite
and with the physical competitor and unchanged canonical partition function. -/
theorem conditionalEntropyBranch_canonical_entropy_identity {N : ℕ} {β : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β)
    {Q : Measure (CoulombConfig N)} [IsProbabilityMeasure Q]
    (hKL : klDiv Q (coulombMeasure N β) ≠ ∞)
    (hB : Integrable (conditionalEntropyBranchThermalB R) Q) :
    (klDiv Q (coulombMeasure N β)).toReal =
      (klDiv (Q.map (@WithLp.ofLp 2 (Fin N → ℂ)))
        (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)))).toReal +
      β * (∫ z, equilibriumModulatedEnergy R.density (WithLp.ofLp z) ∂Q) +
      Real.log (equilibriumReferencePartition N β R) := by
  letI := coulombMeasure_isProbability (N := N) hβ
  let e := (MeasurableEquiv.toLp 2 (Fin N → ℂ)).symm
  have hLaw : (coulombMeasure N β).map e =
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))).tilted
        (fun z => -β * equilibriumModulatedEnergy R.density z) := by
    simpa only [e, MeasurableEquiv.coe_toLp_symm] using
      equilibriumReference_coulombMeasure_eq_tilted hβ R N
  have hA := (conditionalEntropyBranch_finite_entropy_A_integrable hβ R hKL hB).2
  have hAm := equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable (N := N)
  have hAmap : Integrable (equilibriumModulatedEnergy R.density) (Q.map e) :=
    (integrable_map_measure hAm.aestronglyMeasurable e.measurable.aemeasurable).mpr hA
  have h := conditionalEntropyBranch_tilt_kl_identity
    (equilibriumReference_canonical_exp_integrable hβ R N) (hAmap.const_mul (-β))
      (conditionalEntropyBranch_product_entropy_finite hβ R hKL hB)
  rw [← hLaw,
    conditionalEntropyBranch_kl_map_equiv Q (coulombMeasure N β) e,
    integral_const_mul, integral_map e.measurable.aemeasurable hAm.aestronglyMeasurable] at h
  simpa only [e, MeasurableEquiv.coe_toLp_symm, neg_mul, sub_neg_eq_add,
    equilibriumReferencePartition] using h

end RepulsiveCoulomb
