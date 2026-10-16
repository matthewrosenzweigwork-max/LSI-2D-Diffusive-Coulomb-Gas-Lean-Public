module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchCoordinateWeight
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchSplittingWeight
public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchReferencePartitionDefinition
public import Mathlib.MeasureTheory.Measure.Tilted

@[expose] public section

/-! The genuine canonical Gibbs law as the exponentially tilted literal
product reference. Exponential integrability is obtained directly from the
checked physical Coulomb weight, independently of the later partition bound.
All singular pointwise identities are used only on a full-volume set of
injective configurations. Records-only uncompiled source. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibriumReference_splitting_weight_ae {β : ℝ}
    (R : EquilibriumConstructedReference β) (N : ℕ) :
    (fun z : Fin N → ℂ => equilibriumProductDensity N R.density z *
      Real.exp (-β * equilibriumModulatedEnergy R.density z)) =ᵐ[
        Measure.pi (fun _ : Fin N => (volume : Measure ℂ))]
      (fun z => equilibriumSplittingConstant N R * coulombWeight β (WithLp.toLp 2 z)) := by
  filter_upwards [equilibriumCoordinates_injective_ae N] with z hz
  exact equilibriumReference_splitting_weight R N z hz

/-- Actual canonical-coupling exponential integrability, derived from the
physical normalizer rather than from an assumed partition estimate. -/
theorem equilibriumReference_canonical_exp_integrable {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (N : ℕ) :
    Integrable (fun z : Fin N → ℂ => Real.exp (-β * equilibriumModulatedEnergy R.density z))
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))) := by
  rw [equilibriumReference_product_density R N]
  have hm := (equilibriumProductDensity_measurable R.smooth.continuous.measurable N).ennreal_ofReal
  apply (integrable_withDensity_iff hm (Eventually.of_forall
    (fun _ => ENNReal.ofReal_lt_top))).mpr
  simp only [ENNReal.toReal_ofReal (equilibriumProductDensity_nonneg (fun x => (R.positive x).le) N _)]
  apply ((equilibriumCoordinates_weight_integrable hβ N).const_mul
    (equilibriumSplittingConstant N R)).congr
  filter_upwards [equilibriumReference_splitting_weight_ae R N] with z hz
  calc
    equilibriumSplittingConstant N R * coulombWeight β (WithLp.toLp 2 z) =
        equilibriumProductDensity N R.density z *
          Real.exp (-β * equilibriumModulatedEnergy R.density z) := hz.symm
    _ = _ := mul_comm _ _

/-- Exact normalizer relation, including the N-dependent equilibrium constant
and self-interaction scalar from the canonical one-body centering. -/
theorem equilibriumReferencePartition_canonical_eq {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (N : ℕ) :
    equilibriumReferencePartition N β R =
      equilibriumSplittingConstant N R * (coulombPartition N β).toReal := by
  rw [equilibriumReferencePartition, equilibriumReference_product_density R N,
    integral_withDensity_eq_integral_toReal_smul
      (equilibriumProductDensity_measurable R.smooth.continuous.measurable N).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (equilibriumProductDensity_nonneg (fun x => (R.positive x).le) N _),
    smul_eq_mul]
  calc
    _ = ∫ z : Fin N → ℂ, equilibriumSplittingConstant N R * coulombWeight β (WithLp.toLp 2 z)
        ∂Measure.pi (fun _ : Fin N => (volume : Measure ℂ)) :=
      integral_congr_ae (equilibriumReference_splitting_weight_ae R N)
    _ = _ := by rw [integral_const_mul, equilibriumCoordinates_weight_integral hβ N]

theorem equilibriumReferencePartition_canonical_pos {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (N : ℕ) : 0 < equilibriumReferencePartition N β R := by
  rw [equilibriumReferencePartition_canonical_eq hβ R N]
  exact mul_pos (equilibriumSplittingConstant_pos N R)
    (ENNReal.toReal_pos (coulombPartition_pos (N := N) hβ).ne'
      (coulombPartition_lt_top (N := N) hβ).ne)

/-- Exact probability-law splitting in particle coordinates. In particular,
there is no pointwise collision-separation assumption in the law statement. -/
theorem equilibriumReference_coulombMeasure_eq_tilted {β : ℝ} (hβ : 0 < β)
    (R : EquilibriumConstructedReference β) (N : ℕ) :
    Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β) =
      (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))).tilted
        (fun z => -β * equilibriumModulatedEnergy R.density z) := by
  let V := Measure.pi (fun _ : Fin N => (volume : Measure ℂ))
  let w : (Fin N → ℂ) → ℝ := fun z => coulombWeight β (WithLp.toLp 2 z)
  let Z : ℝ≥0∞ := coulombPartition N β
  have hZtop : Z ≠ ∞ := (coulombPartition_lt_top (N := N) hβ).ne
  have hZ : 0 < Z.toReal := ENNReal.toReal_pos (coulombPartition_pos (N := N) hβ).ne' hZtop
  have hC := equilibriumSplittingConstant_pos N R
  have hρ0 := equilibriumProductDensity_nonneg (fun x => (R.positive x).le) N
  have hρm := equilibriumProductDensity_measurable R.smooth.continuous.measurable N
  have hwm : Measurable (fun z => ENNReal.ofReal (w z)) :=
    ((coulombWeight_continuous (N := N) hβ.le).measurable.comp
      (WithLp.measurable_toLp 2 _)).ennreal_ofReal
  have hem : Measurable (fun z : Fin N → ℂ => ENNReal.ofReal
      (Real.exp (-β * equilibriumModulatedEnergy R.density z) /
        equilibriumReferencePartition N β R)) := by
    have he : Measurable (fun z : Fin N → ℂ =>
        Real.exp (-β * equilibriumModulatedEnergy R.density z)) :=
      (measurable_const.mul (equilibriumModulatedEnergy_measurable R.smooth.continuous.measurable)).exp
    exact (he.div_const (equilibriumReferencePartition N β R)).ennreal_ofReal
  symm
  calc
    _ = V.withDensity (fun z => ENNReal.ofReal (w z / Z.toReal)) := by
      rw [Measure.tilted]
      change (Measure.pi (fun _ : Fin N => (R.measure : Measure ℂ))).withDensity
        (fun z => ENNReal.ofReal (Real.exp (-β * equilibriumModulatedEnergy R.density z) /
          equilibriumReferencePartition N β R)) = _
      rw [equilibriumReference_product_density R N, ← withDensity_mul V hρm.ennreal_ofReal hem]
      apply withDensity_congr_ae
      filter_upwards [equilibriumReference_splitting_weight_ae R N] with z hz
      dsimp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (hρ0 z)]
      congr 1
      rw [← mul_div_assoc, hz, equilibriumReferencePartition_canonical_eq hβ R N]
      dsimp only [w, Z]
      field_simp [hC.ne']
    _ = Z⁻¹ • V.withDensity (fun z => ENNReal.ofReal (w z)) := by
      rw [← withDensity_smul Z⁻¹ hwm]
      apply withDensity_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only [Pi.smul_apply, smul_eq_mul]
        rw [ENNReal.ofReal_div_of_pos hZ, ENNReal.ofReal_toReal hZtop,
          div_eq_mul_inv, mul_comm])
    _ = _ := (equilibriumCoordinates_coulombMeasure hβ N).symm

/-- The selected reference is the one produced by the actual minimization,
EL and regularity construction; no equilibrium existence premise is supplied. -/
theorem equilibriumConstructedReference_coulombMeasure_eq_tilted {β : ℝ} (hβ : 0 < β)
    (N : ℕ) :
    Measure.map (@WithLp.ofLp 2 (Fin N → ℂ)) (coulombMeasure N β) =
      (Measure.pi (fun _ : Fin N =>
        ((equilibriumConstructedReference β hβ).measure : Measure ℂ))).tilted
          (fun z => -β * equilibriumModulatedEnergy
            (equilibriumConstructedReference β hβ).density z) :=
  equilibriumReference_coulombMeasure_eq_tilted hβ (equilibriumConstructedReference β hβ) N

end RepulsiveCoulomb
