module

public import LeanResearch.RepulsiveCoulomb.CoulombProductVolume
public import LeanResearch.RepulsiveCoulomb.CoulombCollisionNull
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace

@[expose] public section

/-! Actual coordinate transport for physical Euclidean volume and the genuine
Coulomb weight. Collision-nullity is transported from the checked physical
model, and the normalization uses its finite positive partition integral.
Records-only uncompiled source. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibriumCoordinates_toLp_measurePreserving (N : ℕ) :
    MeasurePreserving (@WithLp.toLp 2 (Fin N → ℂ))
      (Measure.pi (fun _ : Fin N => (volume : Measure ℂ)))
      (volume : Measure (CoulombConfig N)) := by
  have h : MeasurePreserving (MeasurableEquiv.toLp 2 (Fin N → ℂ)).symm
      (volume : Measure (CoulombConfig N))
      (Measure.pi (fun _ : Fin N => (volume : Measure ℂ))) :=
    ⟨WithLp.measurable_ofLp 2 _, coulomb_volume_map_coordinates N⟩
  exact MeasurePreserving.symm (MeasurableEquiv.toLp 2 (Fin N → ℂ)).symm h

theorem equilibriumCoordinates_injective_ae (N : ℕ) :
    ∀ᵐ z : Fin N → ℂ ∂Measure.pi (fun _ : Fin N => (volume : Measure ℂ)),
      Function.Injective z := by
  filter_upwards [(equilibriumCoordinates_toLp_measurePreserving N).quasiMeasurePreserving.ae
    (coulombDomain_ae N)] with z hz
  have hp := (coulombVandermonde_ne_zero_iff (WithLp.toLp 2 z)).mp hz
  intro i j hij
  by_contra hne
  exact hp i j hne hij

theorem equilibriumCoordinates_weight_integrable {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    Integrable (fun z : Fin N → ℂ => coulombWeight β (WithLp.toLp 2 z))
      (Measure.pi (fun _ : Fin N => (volume : Measure ℂ))) :=
  (equilibriumCoordinates_toLp_measurePreserving N).integrable_comp_of_integrable
    (coulombWeight_integrable hβ)

theorem equilibriumCoordinates_weight_integral {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    (∫ z : Fin N → ℂ, coulombWeight β (WithLp.toLp 2 z)
      ∂Measure.pi (fun _ : Fin N => (volume : Measure ℂ))) = (coulombPartition N β).toReal := by
  rw [(equilibriumCoordinates_toLp_measurePreserving N).integral_comp
    (MeasurableEquiv.toLp 2 (Fin N → ℂ)).measurableEmbedding (coulombWeight β)]
  rw [coulombPartition, ← ofReal_integral_eq_lintegral_ofReal (coulombWeight_integrable hβ)
    (Eventually.of_forall (coulombWeight_nonneg β)),
    ENNReal.toReal_ofReal (integral_nonneg (coulombWeight_nonneg β))]

/-- Coordinate transport of the actual unnormalized Gibbs measure. -/
theorem equilibriumCoordinates_weight_measure {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    Measure.map (@WithLp.ofLp 2 (Fin N → ℂ))
      ((volume : Measure (CoulombConfig N)).withDensity (fun z => ENNReal.ofReal (coulombWeight β z))) =
    (Measure.pi (fun _ : Fin N => (volume : Measure ℂ))).withDensity
      (fun z => ENNReal.ofReal (coulombWeight β (WithLp.toLp 2 z))) := by
  have hf := WithLp.measurable_ofLp 2 (Fin N → ℂ)
  have hg := WithLp.measurable_toLp 2 (Fin N → ℂ)
  have hw := (coulombWeight_continuous (N := N) hβ.le).measurable.ennreal_ofReal
  have hwt := hw.comp hg
  apply Measure.ext_of_lintegral
  intro φ hφ
  rw [lintegral_map hφ hf]
  have hl := lintegral_withDensity_eq_lintegral_mul volume hw (hφ.comp hf)
  have hr := lintegral_withDensity_eq_lintegral_mul
    (Measure.pi (fun _ : Fin N => (volume : Measure ℂ))) hwt hφ
  simp only [Function.comp_def] at hl hr
  rw [hl, hr, ← coulomb_volume_map_coordinates N]
  have hm := lintegral_map (μ := (volume : Measure (CoulombConfig N))) (hwt.mul hφ) hf
  simp only [Function.comp_def] at hm
  rw [hm]
  rfl

/-- The pushed-forward probability law has the same exact ENNReal
normalization constant as the physical l2 model. -/
theorem equilibriumCoordinates_coulombMeasure {β : ℝ} (hβ : 0 < β) (N : ℕ) :
    Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β) =
      (coulombPartition N β)⁻¹ •
        (Measure.pi (fun _ : Fin N => (volume : Measure ℂ))).withDensity
          (fun z => ENNReal.ofReal (coulombWeight β (WithLp.toLp 2 z))) := by
  rw [coulombMeasure, Measure.map_smul _ (WithLp.measurable_ofLp 2 _).aemeasurable,
    equilibriumCoordinates_weight_measure hβ N]

end RepulsiveCoulomb
