module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.EmpiricalSpatialInteraction
public import LeanResearch.RepulsiveCoulomb.PaperRoute.ReferencePartitionBounds

@[expose] public section

/-! Additive experimental source; verification is recorded separately in evidence. The actual physical
reference discharges all row/product integrability and atomlessness facts.
Canonical finite-label energy agrees with N*F_N first on collision-free
configurations, then almost everywhere under the actual product reference. -/
noncomputable section
open MeasureTheory Set Real Filter
open scoped BigOperators ENNReal
namespace RepulsiveCoulomb.PaperRoute

private theorem reference_log_row {β : ℝ} (R : EquilibriumConstructedReference β) (x : ℂ) :
    Integrable (fun y => paperSpatialLogKernel (x,y)) (R.measure : Measure ℂ) := by
  rw [← R.density_measure]
  apply (equilibriumDensityMeasure_integrable_iff R.smooth.continuous.measurable
    (fun y => (R.positive y).le) _).mpr
  simpa only [paperSpatialLogKernel, mul_comm] using
    equilibriumLogKernel_mul_integrable R.smooth.continuous.measurable
      (fun y => (R.positive y).le) R.cap R.integrable
      (equilibriumReference_logMoment_integrable R) x

private theorem reference_log_column {β : ℝ} (R : EquilibriumConstructedReference β) (y : ℂ) :
    Integrable (fun x => paperSpatialLogKernel (x,y)) (R.measure : Measure ℂ) := by
  simpa only [paperSpatialLogKernel, equilibriumLogKernel, norm_sub_rev] using reference_log_row R y

private theorem reference_row_integral {β : ℝ} (R : EquilibriumConstructedReference β) (x : ℂ) :
    (∫ y, paperSpatialLogKernel (x,y) ∂R.measure) = equilibriumDensityPotential R.density x := by
  rw [← R.density_measure]
  exact (equilibriumDensityPotential_eq_measureIntegral R.smooth.continuous.measurable
    (fun y => (R.positive y).le) x).symm

private theorem reference_column_integral {β : ℝ} (R : EquilibriumConstructedReference β) (y : ℂ) :
    (∫ x, paperSpatialLogKernel (x,y) ∂R.measure) = equilibriumDensityPotential R.density y := by
  simpa only [paperSpatialLogKernel, equilibriumLogKernel, norm_sub_rev] using reference_row_integral R y

/-- Actual HasProd and signed-variation integrability are established along
with the collision-free numerical identity. No integral defaults are used. -/
theorem paper_reference_spatial_bridge {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N)
    (z : Fin N → ℂ) (hz : Function.Injective z) :
    VectorMeasure.HasProd
      ((paperEmpiricalMeasure z).toSignedMeasure - (R.measure : Measure ℂ).toSignedMeasure)
      ((paperEmpiricalMeasure z).toSignedMeasure - (R.measure : Measure ℂ).toSignedMeasure)
      (ContinuousLinearMap.lsmul ℝ ℝ) ∧
    ((paperSignedSquare ((paperEmpiricalMeasure z).toSignedMeasure -
      (R.measure : Measure ℂ).toSignedMeasure)).restrict paperSpatialOffDiagonal).Integrable
        paperSpatialLogKernel ∧
    paperSpatialModulatedEnergy (R.measure : Measure ℂ) z = equilibriumModulatedEnergy R.density z := by
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ R.objective_finite
  let : NullSingletonClass (R.measure : Measure ℂ) := ⟨fun x => hAC (measure_singleton x)⟩
  have hm : Measurable paperSpatialLogKernel :=
    equilibriumLogKernel_measurable.comp (measurable_fst.sub measurable_snd)
  have hp : Integrable paperSpatialLogKernel ((R.measure : Measure ℂ).prod R.measure) :=
    equilibriumObjective_finite_logEnergy_integrable hβ R.objective_finite
  obtain ⟨hAA,hAB,hBA,hBB,eAA,eAB,eBA,eBB⟩ := paper_empirical_spatial_integrals z hz
    (R.measure : Measure ℂ) hm (reference_log_row R) (reference_log_column R) hp
  refine ⟨paper_signed_hasProd _,
    paper_signed_restricted_square_integrable _ _ paperSpatialOffDiagonal_measurable hAA hAB hBA hBB, ?_⟩
  have he := paper_signed_restricted_square_integral _ _ paperSpatialOffDiagonal_measurable hAA hAB hBA hBB
  rw [eAA, eAB, eBA, eBB] at he
  simp_rw [reference_row_integral, reference_column_integral] at he
  rw [show (∫ p, paperSpatialLogKernel p ∂(R.measure : Measure ℂ).prod R.measure) =
    equilibriumDensityInteraction R.density from equilibriumReference_measureInteraction hβ R] at he
  unfold paperSpatialModulatedEnergy paperSpatialModulatedF
  rw [he]
  unfold equilibriumModulatedEnergy equilibriumOrderedOffDiagonalSum
  change (N : ℝ) * ((1 / 2 : ℝ) *
    ((N : ℝ)⁻¹ * (N : ℝ)⁻¹ * (∑ i, ∑ j, if i = j then 0 else equilibriumLogKernel (z i - z j)) -
      (N : ℝ)⁻¹ * (∑ i, equilibriumDensityPotential R.density (z i)) -
      (N : ℝ)⁻¹ * (∑ i, equilibriumDensityPotential R.density (z i)) + equilibriumDensityInteraction R.density)) = _
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring

/-- Only product-almost-everywhere injective configurations identify the
spatial diagonal removal with distinct-label removal. -/
theorem paper_reference_spatial_energy_ae {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) :
    paperSpatialModulatedEnergy (R.measure : Measure ℂ) =ᵐ[
      Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))] equilibriumModulatedEnergy R.density := by
  filter_upwards [equilibriumReference_product_injective_ae hβ R N] with z hz
  exact (paper_reference_spatial_bridge hβ R hN z hz).2.2

def paperSpatialPartition {β : ℝ} (N : ℕ) (t : ℝ) (R : EquilibriumConstructedReference β) : ℝ :=
  ∫ z : Fin N → ℂ, Real.exp (-t * paperSpatialModulatedEnergy (R.measure : Measure ℂ) z)
    ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))

theorem paper_reference_spatial_exponential_integrable {β t : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) (ht : 0 ≤ t) :
    Integrable (fun z : Fin N → ℂ => Real.exp (-t * paperSpatialModulatedEnergy (R.measure : Measure ℂ) z))
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) := by
  apply (paper_reference_modulated_exp_integrable_polynomial hβ R hN ht).congr
  filter_upwards [paper_reference_spatial_energy_ae hβ R hN] with z hz
  rw [hz]

theorem paper_reference_spatial_partition_eq {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) (t : ℝ) :
    paperSpatialPartition N t R = equilibriumReferencePartition N t R := by
  apply integral_congr_ae
  filter_upwards [paper_reference_spatial_energy_ae hβ R hN] with z hz
  rw [hz]

/-- Literal spatial-interaction partition bound with the fixed-T numerical
constant selected before beta, the supplied reference, N and lower coupling. -/
theorem paper_spatial_partition_uniform {T : ℝ} (hT : 0 < T) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (_hβ : 0 < β) (R : EquilibriumConstructedReference β),
      ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t → t ≤ T → paperSpatialPartition N t R ≤ C := by
  obtain ⟨C,hC,hb⟩ := paper_reference_partition_uniform hT
  refine ⟨C,hC,?_⟩
  intro β hβ R N hN t ht htT
  rw [paper_reference_spatial_partition_eq hβ R (by omega) t]
  exact hb β hβ R N hN t ht htT

end RepulsiveCoulomb.PaperRoute
