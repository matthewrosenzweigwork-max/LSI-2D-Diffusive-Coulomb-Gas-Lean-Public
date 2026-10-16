module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferencePartitionDefinition
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchProductModulation
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferenceBounds
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-! The actual canonical modulated partition: its integrand is integrable for
every fixed N and t>=0, and Jensen gives the exact exp(t*c_beta/2) lower bound.
The fixed-N upper estimate grows as N^(t/4); the uniform-in-N upper bound is
not asserted here and still requires the correlation/partition argument. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

/-- The actual product reference gives full measure to the injective particle
positions needed for the singular deterministic estimate. -/
theorem equilibriumReference_product_injective_ae {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (N : ℕ) :
    ∀ᵐ z : Fin N → ℂ ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)), Function.Injective z := by
  have hAC := equilibriumObjective_finite_absolutelyContinuous hβ R.objective_finite
  letI : NullSingletonClass (R.measure : Measure ℂ) := ⟨fun x => hAC (measure_singleton x)⟩
  filter_upwards [equilibriumProduct_coordinates_distinct_ae N (R.measure : Measure ℂ)] with z hz
  intro i j hij
  by_contra hne
  exact hz i j hne hij

theorem equilibriumReference_modulated_exp_bound_ae {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    ∀ᵐ z : Fin N → ℂ ∂Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ)),
      Real.exp (-t * equilibriumModulatedEnergy R.density z) ≤
        Real.exp (t * (Real.log (N : ℝ) / 4 + 1 / 2)) := by
  filter_upwards [equilibriumReference_product_injective_ae hβ R N] with z hz
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left (equilibriumReference_modulated_log_lower hβ R hN z hz) ht
  nlinarith

/-- Genuine fixed-N exponential integrability, derived before using Jensen. -/
theorem equilibriumReference_modulated_exp_integrable {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun z : Fin N → ℂ => Real.exp (-t * equilibriumModulatedEnergy R.density z))
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) := by
  have hm : Measurable (fun z : Fin N → ℂ => Real.exp (-t * equilibriumModulatedEnergy R.density z)) :=
    (measurable_const.mul (equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable)).exp
  apply (integrable_const (Real.exp (t * (Real.log (N : ℝ) / 4 + 1 / 2)))).mono'
    hm.aestronglyMeasurable
  filter_upwards [equilibriumReference_modulated_exp_bound_ae hβ R hN ht] with z hz
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact hz

/-- Exact Jensen lower bound under the literal product reference. -/
theorem equilibriumReferencePartition_lower {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    Real.exp (t * equilibriumDensityInteraction R.density / 2) ≤ equilibriumReferencePartition N t R := by
  obtain ⟨hAi, hAm⟩ := equilibriumReference_modulated_integrable_mean hβ R hN
  have hExp := equilibriumReference_modulated_exp_integrable hβ R hN ht
  have h := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun _ => mem_univ _)) (hAi.const_mul (-t)) hExp
  rw [integral_const_mul, hAm] at h
  have he : -t * (-equilibriumDensityInteraction R.density / 2) =
      t * equilibriumDensityInteraction R.density / 2 := by ring
  rwa [he] at h

theorem equilibriumReferencePartition_pos {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    0 < equilibriumReferencePartition N t R :=
  (Real.exp_pos _).trans_le (equilibriumReferencePartition_lower hβ R hN ht)

/-- This explicit fixed-N estimate establishes finiteness but deliberately
retains its log-N growth; it is not the manuscript uniform partition bound. -/
theorem equilibriumReferencePartition_fixedN_upper {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : 0 ≤ t) :
    equilibriumReferencePartition N t R ≤ Real.exp (t * (Real.log (N : ℝ) / 4 + 1 / 2)) := by
  have h := integral_mono_ae (equilibriumReference_modulated_exp_integrable hβ R hN ht)
    (integrable_const _) (equilibriumReference_modulated_exp_bound_ae hβ R hN ht)
  simpa only [equilibriumReferencePartition, integral_const, probReal_univ, one_smul] using h

/-- The manuscript lower partition bound is uniform on a compact positive
beta interval and a bounded nonnegative coupling interval, for every N>=1. -/
theorem equilibriumReferencePartition_compact_lower {βlo βhi T : ℝ}
    (hlo : 0 < βlo) (hord : βlo ≤ βhi) (hT : 0 ≤ T) :
    ∃ a : ℝ, 0 < a ∧ ∀ β (hβlo : βlo ≤ β) (hβhi : β ≤ βhi), ∀ N : ℕ, 0 < N →
      ∀ t : ℝ, 0 ≤ t → t ≤ T →
      a ≤ equilibriumReferencePartition N t (equilibriumConstructedReference β (hlo.trans_le hβlo)) := by
  let M : ℝ := 2 * equilibriumCompactLogBound βlo + 1 / 2
  refine ⟨Real.exp (-T * M / 2), Real.exp_pos _, ?_⟩
  intro β hβlo hβhi N hN t ht htT
  let R := equilibriumConstructedReference β (hlo.trans_le hβlo)
  have hc : |equilibriumDensityInteraction R.density| ≤ M :=
    equilibriumReference_interaction_abs_bound hlo hβlo R
  have hM : 0 ≤ M := (abs_nonneg _).trans hc
  have hcl : -M ≤ equilibriumDensityInteraction R.density := (abs_le.mp hc).1
  have h1 := mul_le_mul_of_nonneg_left hcl ht
  have h2 := mul_le_mul_of_nonneg_right htT hM
  have he : -T * M / 2 ≤ t * equilibriumDensityInteraction R.density / 2 := by nlinarith
  exact (Real.exp_le_exp.mpr he).trans
    (equilibriumReferencePartition_lower (hlo.trans_le hβlo) R hN ht)

end RepulsiveCoulomb
