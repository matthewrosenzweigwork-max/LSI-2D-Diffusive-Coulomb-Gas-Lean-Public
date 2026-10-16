import LeanResearch.RepulsiveCoulomb.UnitDiskNormalization

/-! The tail division in Lemma 3.3 using its literal displayed disk witness,
without replacing the earlier annular endpoint or normalization proof. -/
noncomputable section
open MeasureTheory Real Filter Set
open scoped ENNReal BigOperators Topology
namespace RepulsiveCoulomb

theorem pointMeasure_le_disk_envelope {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {s : Set ℂ} (hs : MeasurableSet s) :
    pointMeasure γ a y s ≤ (ENNReal.ofReal (pointDiskLowerConstant γ Q))⁻¹ *
      ∫⁻ z in s, ENNReal.ofReal (pointEnvelope γ Q z) := by
  have hA0 : ENNReal.ofReal (pointLocationFactor a y) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (pointLocationFactor_pos a y))
  have hC0 : ENNReal.ofReal (pointDiskLowerConstant γ Q) ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (pointDiskLowerConstant_pos γ Q))
  have hP := pointPartition_unitDisk_lower_uniform hγ ha hQ y
  rw [ENNReal.ofReal_mul (pointDiskLowerConstant_pos γ Q).le] at hP
  have hratio : (pointPartition γ a y)⁻¹ * ENNReal.ofReal (pointLocationFactor a y) ≤
      (ENNReal.ofReal (pointDiskLowerConstant γ Q))⁻¹ := by
    calc
      _ ≤ (ENNReal.ofReal (pointDiskLowerConstant γ Q) *
          ENNReal.ofReal (pointLocationFactor a y))⁻¹ * ENNReal.ofReal (pointLocationFactor a y) :=
        mul_le_mul_left (ENNReal.inv_le_inv.mpr hP) _
      _ = _ := by
        rw [ENNReal.mul_inv (Or.inl hC0) (Or.inl ENNReal.ofReal_ne_top),
          ENNReal.inv_mul_cancel_right hA0 ENNReal.ofReal_ne_top]
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ ↦ ha j)).trans hQ
  rw [pointMeasure, Measure.smul_apply, smul_eq_mul, withDensity_apply _ hs]
  calc
    _ ≤ (pointPartition γ a y)⁻¹ *
        ∫⁻ z in s, ENNReal.ofReal (pointLocationFactor a y * pointEnvelope γ Q z) := by
      gcongr with z
      exact pointWeight_le_envelope γ ha hQ y z
    _ = ((pointPartition γ a y)⁻¹ * ENNReal.ofReal (pointLocationFactor a y)) *
        ∫⁻ z in s, ENNReal.ofReal (pointEnvelope γ Q z) := by
      simp_rw [ENNReal.ofReal_mul (pointLocationFactor_pos a y).le]
      rw [lintegral_const_mul _ (pointEnvelope_continuous γ hQ0).measurable.ennreal_ofReal,
        ← mul_assoc]
    _ ≤ _ := mul_le_mul_left hratio _

theorem pointMeasure_disk_tail_le {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) (R : ℝ) :
    pointMeasure γ a y {z | R < ‖z‖} ≤
      ENNReal.ofReal ((pointDiskLowerConstant γ Q)⁻¹ *
        ∫ z : ℂ in {z | R < ‖z‖}, pointEnvelope γ Q z) := by
  have hQ0 := (Finset.sum_nonneg (fun j _ ↦ ha j)).trans hQ
  have hs : MeasurableSet {z : ℂ | R < ‖z‖} := measurableSet_lt measurable_const continuous_norm.measurable
  have h := pointMeasure_le_disk_envelope hγ ha hQ y hs
  rw [← ofReal_integral_eq_lintegral_ofReal (pointEnvelope_integrable hγ hQ0).restrict
    (Eventually.of_forall (pointEnvelope_nonneg γ Q)),
    ← ENNReal.ofReal_inv_of_pos (pointDiskLowerConstant_pos γ Q),
    ← ENNReal.ofReal_mul (inv_nonneg.mpr (pointDiskLowerConstant_pos γ Q).le)] at h
  exact h

theorem pointMeasure_disk_tail_real_le {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) (R : ℝ) :
    (pointMeasure γ a y).real {z | R < ‖z‖} ≤
      (pointDiskLowerConstant γ Q)⁻¹ * ∫ z : ℂ in {z | R < ‖z‖}, pointEnvelope γ Q z := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top (pointMeasure_disk_tail_le hγ ha hQ y R)
  simpa only [Measure.real, ENNReal.toReal_ofReal
    (mul_nonneg (inv_nonneg.mpr (pointDiskLowerConstant_pos γ Q).le)
      (integral_nonneg (pointEnvelope_nonneg γ Q)))] using h

end RepulsiveCoulomb
