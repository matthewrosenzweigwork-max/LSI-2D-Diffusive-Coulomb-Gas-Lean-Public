module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.ThermalDiskReferenceBounds
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchPartitionBasic

@[expose] public section

/-! Fixed-N exponential integrability directly from the original logarithmic
lower bound and genuine disk-derived polynomial moments. No Onsager/zero-mass
positivity theorem is needed for this elementary integrability prerequisite. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem paper_reference_modulated_polynomial_lower {β : ℝ}
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) (z : Fin N → ℂ) :
    -(∑ i, equilibriumLogMoment (z i)) - (N : ℝ) / 2 +
      (N : ℝ) * equilibriumDensityInteraction R.density / 2 ≤
        equilibriumModulatedEnergy R.density z := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hp (i j : Fin N) :
      -equilibriumLogMoment (z i) - equilibriumLogMoment (z j) ≤
        if i = j then 0 else equilibriumLogKernel (z i - z j) := by
    split_ifs with hij
    · have hi := equilibriumLogMoment_nonneg (z i)
      have hj := equilibriumLogMoment_nonneg (z j)
      linarith
    · exact equilibriumLogKernel_sub_lower (z i) (z j)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
    Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin N))) => hp i j))
  have he : (∑ i : Fin N, ∑ j : Fin N,
      (-equilibriumLogMoment (z i) - equilibriumLogMoment (z j))) =
        -(2 * (N : ℝ)) * ∑ i, equilibriumLogMoment (z i) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
    ring
  rw [he] at hs
  change -(2 * (N : ℝ)) * (∑ i, equilibriumLogMoment (z i)) ≤
    equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) at hs
  have hdiv : -(∑ i, equilibriumLogMoment (z i)) ≤
      equilibriumOrderedOffDiagonalSum (fun i j => equilibriumLogKernel (z i - z j)) /
        (2 * (N : ℝ)) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * N)).mpr
    nlinarith only [hs]
  have hu : (∑ i : Fin N, equilibriumDensityPotential R.density (z i)) ≤ (N : ℝ) / 2 := by
    have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      equilibriumReference_potential_upper R (z i))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      mul_one_div] using h
  unfold equilibriumModulatedEnergy
  linarith

theorem paper_reference_modulated_exp_polynomial_bound {β t : ℝ}
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) (ht : 0 ≤ t)
    (z : Fin N → ℂ) :
    Real.exp (-t * equilibriumModulatedEnergy R.density z) ≤
      Real.exp (t * ((N : ℝ) / 2 - (N : ℝ) * equilibriumDensityInteraction R.density / 2)) *
        ∏ i, (1 + ‖z i‖) ^ t := by
  have hlo := paper_reference_modulated_polynomial_lower R hN z
  have hmul := mul_le_mul_of_nonneg_left hlo ht
  have h := Real.exp_le_exp.mpr (show -t * equilibriumModulatedEnergy R.density z ≤
      t * ((N : ℝ) / 2 - (N : ℝ) * equilibriumDensityInteraction R.density / 2) +
        ∑ i, t * equilibriumLogMoment (z i) by
    rw [← Finset.mul_sum]
    nlinarith only [hmul])
  rw [Real.exp_add, Real.exp_sum] at h
  apply h.trans_eq
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [Real.rpow_def_of_pos (by positivity : 0 < 1 + ‖z i‖)]
  unfold equilibriumLogMoment
  congr 1
  ring

theorem paper_reference_modulated_exp_integrable_polynomial {β t : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β) {N : ℕ}
    (hN : 0 < N) (ht : 0 ≤ t) :
    Integrable (fun z : Fin N → ℂ => Real.exp (-t * equilibriumModulatedEnergy R.density z))
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) := by
  have hi := (paper_reference_polynomial_moment_bound_disk hβ le_rfl le_rfl ht R).1
  have hprod : Integrable (fun z : Fin N → ℂ => ∏ i, (1 + ‖z i‖) ^ t)
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) :=
    Integrable.fintype_prod (fun _ : Fin N => hi)
  have hm : Measurable (fun z : Fin N → ℂ => Real.exp
      (-t * equilibriumModulatedEnergy R.density z)) := (measurable_const.mul
    (equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable)).exp
  apply (hprod.const_mul (Real.exp (t * ((N : ℝ) / 2 -
    (N : ℝ) * equilibriumDensityInteraction R.density / 2)))).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall (fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact paper_reference_modulated_exp_polynomial_bound R hN ht z)

theorem paper_reference_partition_lower_polynomial {β t : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β) {N : ℕ}
    (hN : 0 < N) (ht : 0 ≤ t) :
    Real.exp (t * equilibriumDensityInteraction R.density / 2) ≤
      equilibriumReferencePartition N t R := by
  obtain ⟨hAi, hAm⟩ := equilibriumReference_modulated_integrable_mean hβ R hN
  have hExp := paper_reference_modulated_exp_integrable_polynomial hβ R hN ht
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun _ => mem_univ _)) (hAi.const_mul (-t)) hExp
  rw [integral_const_mul, hAm] at h
  have he : -t * (-equilibriumDensityInteraction R.density / 2) =
      t * equilibriumDensityInteraction R.density / 2 := by ring
  rwa [he] at h

theorem paper_reference_partition_pos_polynomial {β t : ℝ}
    (hβ : 0 < β) (R : EquilibriumConstructedReference β) {N : ℕ}
    (hN : 0 < N) (ht : 0 ≤ t) : 0 < equilibriumReferencePartition N t R :=
  (Real.exp_pos _).trans_le (paper_reference_partition_lower_polynomial hβ R hN ht)

end RepulsiveCoulomb.PaperRoute
