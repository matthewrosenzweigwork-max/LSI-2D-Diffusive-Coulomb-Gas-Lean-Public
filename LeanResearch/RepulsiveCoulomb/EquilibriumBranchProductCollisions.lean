import LeanResearch.RepulsiveCoulomb.LabeledCoulombModel
import Mathlib.Probability.Independence.Basic

/-! Actual product-reference collision nullity. The reference is literally
mu to the Nth tensor power, transported to physical l2 configurations.
This does not substitute an index-off-diagonal condition for distinct points. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
namespace RepulsiveCoulomb

/-- Literal tensor-product reference in the manuscript's configuration space. -/
def equilibriumProductReference (N : ℕ) (μ : Measure ℂ) : Measure (CoulombConfig N) :=
  Measure.map (@WithLp.toLp 2 (Fin N → ℂ)) (Measure.pi (fun _ : Fin N => μ))

instance equilibriumProductReference_probability (N : ℕ) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] : IsProbabilityMeasure (equilibriumProductReference N μ) := by
  unfold equilibriumProductReference
  infer_instance

theorem equilibriumProduct_pair_distinct_ae (N : ℕ) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x : Fin N → ℂ ∂Measure.pi (fun _ : Fin N => μ), x i ≠ x j := by
  have hind := (iIndepFun_pi (μ := fun _ : Fin N => μ)
    (X := fun _ : Fin N => (id : ℂ → ℂ)) (fun _ => aemeasurable_id)).indepFun hij
  have hm := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  change Measure.map (fun x : Fin N → ℂ => (x i, x j)) (Measure.pi (fun _ : Fin N => μ)) =
    (Measure.map (Function.eval i) (Measure.pi (fun _ : Fin N => μ))).prod
      (Measure.map (Function.eval j) (Measure.pi (fun _ : Fin N => μ))) at hm
  rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq,
    (measurePreserving_eval (fun _ : Fin N => μ) j).map_eq] at hm
  have hpair : ∀ᵐ p : ℂ × ℂ ∂μ.prod μ, p.1 ≠ p.2 := by
    apply (Measure.ae_prod_iff_ae_ae (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mpr
    exact Eventually.of_forall (fun x => (μ.ae_ne x).mono (fun _ h => h.symm))
  rw [← hm] at hpair
  exact (ae_map_iff (by fun_prop)
    (isClosed_eq continuous_fst continuous_snd).measurableSet.compl).mp hpair

theorem equilibriumProduct_coordinates_distinct_ae (N : ℕ) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ x : Fin N → ℂ ∂Measure.pi (fun _ : Fin N => μ),
      ∀ i j : Fin N, i ≠ j → x i ≠ x j := by
  apply ae_all_iff.mpr
  intro i
  apply ae_all_iff.mpr
  intro j
  by_cases hij : i = j
  · exact Eventually.of_forall (fun _ h => (h hij).elim)
  · exact (equilibriumProduct_pair_distinct_ae N μ hij).mono (fun _ h _ => h)

/-- The actual product reference assigns full measure to the physical
collision-free domain, for every particle number. -/
theorem equilibriumProductReference_domain_ae (N : ℕ) (μ : Measure ℂ)
    [IsProbabilityMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ z ∂equilibriumProductReference N μ, z ∈ coulombDomain N := by
  unfold equilibriumProductReference
  apply (ae_map_iff (PiLp.continuous_toLp 2 (fun _ : Fin N => ℂ)).measurable.aemeasurable
    (coulombDomain N).isOpen.measurableSet).mpr
  filter_upwards [equilibriumProduct_coordinates_distinct_ae N μ] with x hx
  exact (coulombVandermonde_ne_zero_iff (WithLp.toLp 2 x)).mpr hx

end RepulsiveCoulomb
