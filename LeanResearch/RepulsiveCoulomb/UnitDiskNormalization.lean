module

public import LeanResearch.RepulsiveCoulomb.UnitDiskLogIntegral

@[expose] public section

/-! The literal lower witness displayed in manuscript Lemma 3.3.
The density convention is exp(-gamma*|z|^2/2). Its unit-disk minimum is
exp(-gamma/2); Jensen is applied to the logarithm of the raw product. -/
noncomputable section
open MeasureTheory Set Real Filter Metric
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

/-- The displayed unit-disk normalization witness, separate from the existing
annular witness and without changing any endpoint theorem. -/
def pointDiskLowerConstant (γ Q : ℝ) : ℝ :=
  Real.pi * Real.exp (-γ / 2 - (Real.log 2 + 1 / 2) * Q)

theorem pointDiskLowerConstant_pos (γ Q : ℝ) : 0 < pointDiskLowerConstant γ Q := by
  unfold pointDiskLowerConstant
  positivity

theorem unitDisk_exp_average_le {f : ℂ → ℝ}
    (hf : IntegrableOn f (closedBall (0 : ℂ) 1))
    (he : IntegrableOn (Real.exp ∘ f) (closedBall (0 : ℂ) 1)) :
    Real.exp (⨍ z in closedBall (0 : ℂ) 1, f z) ≤
      ⨍ z in closedBall (0 : ℂ) 1, Real.exp (f z) := by
  let μ : Measure ℂ := volume.restrict (closedBall (0 : ℂ) 1)
  have hμ : μ ≠ 0 := by
    intro h
    have hm := congrArg (fun ν : Measure ℂ => ν.real univ) h
    have hv : μ.real univ = Real.pi := by
      simp [μ, Measure.real, Complex.volume_closedBall]
    rw [hv] at hm
    exact Real.pi_ne_zero (by simpa [Measure.real] using hm)
  letI : NeZero μ := ⟨hμ⟩
  letI : IsFiniteMeasure μ := ⟨by
    change (volume.restrict (closedBall (0 : ℂ) 1)) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact (isCompact_closedBall (0 : ℂ) 1).measure_lt_top⟩
  exact convexOn_exp.map_average_le (μ := μ) Real.continuous_exp.continuousOn isClosed_univ
    (Eventually.of_forall (fun _ => mem_univ _)) hf he

theorem unitDisk_raw_log_average_lower {m : ℕ} {Q : ℝ}
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    -(Real.log 2 + 1 / 2) * Q + ∑ j, a j * Real.log (1 + ‖y j‖) ≤
      ⨍ z in closedBall (0 : ℂ) 1, ∑ j, a j * Real.log ‖z - y j‖ := by
  rw [average_fun_finsetSum (fun j _ => (log_distance_unitDisk_integrable (y j)).const_mul (a j))]
  simp_rw [average_const_mul]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    mul_le_mul_of_nonneg_left (unitDisk_log_average_lower (y j)) (ha j))
  simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at hs
  have hc : 0 ≤ Real.log 2 + 1 / 2 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    linarith
  have hq := mul_le_mul_of_nonneg_right hQ hc
  linarith

theorem unitDisk_raw_weight_jensen {m : ℕ} {Q : ℝ}
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    Real.exp (-(Real.log 2 + 1 / 2) * Q) * pointLocationFactor a y ≤
      ⨍ z in closedBall (0 : ℂ) 1, pointWeight 0 a y z := by
  let f : ℂ → ℝ := fun z => ∑ j, a j * Real.log ‖z - y j‖
  have hf : IntegrableOn f (closedBall (0 : ℂ) 1) :=
    integrable_finsetSum _ (fun j _ => (log_distance_unitDisk_integrable (y j)).const_mul (a j))
  have heq : (Real.exp ∘ f) =ᵐ[volume.restrict (closedBall (0 : ℂ) 1)] pointWeight 0 a y := by
    have hav : ∀ᵐ z : ℂ, ∀ j, z ≠ y j := ae_all_iff.mpr (fun j => volume.ae_ne (y j))
    filter_upwards [ae_restrict_of_ae hav] with z hz
    simpa [pointLogWeight, f] using exp_pointLogWeight 0 a y hz
  have hw : IntegrableOn (pointWeight 0 a y) (closedBall (0 : ℂ) 1) :=
    (pointWeight_continuous 0 ha y).continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)
  have hj := unitDisk_exp_average_le hf (hw.congr heq.symm)
  have havg : (⨍ z in closedBall (0 : ℂ) 1, Real.exp (f z)) =
      ⨍ z in closedBall (0 : ℂ) 1, pointWeight 0 a y z := average_congr heq
  rw [havg] at hj
  calc
    _ = Real.exp (-(Real.log 2 + 1 / 2) * Q + ∑ j, a j * Real.log (1 + ‖y j‖)) := by
      rw [pointLocationFactor_eq_exp_sum, Real.exp_add]
    _ ≤ Real.exp (⨍ z in closedBall (0 : ℂ) 1, f z) :=
      Real.exp_le_exp.mpr (unitDisk_raw_log_average_lower ha hQ y)
    _ ≤ _ := hj

theorem pointWeight_unitDisk_gaussian_lower {m : ℕ} {γ : ℝ} (hγ : 0 ≤ γ)
    (a : Fin m → ℝ) (y : Fin m → ℂ) {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) 1) :
    Real.exp (-γ / 2) * pointWeight 0 a y z ≤ pointWeight γ a y z := by
  have hn : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
  have hs : ‖z‖ ^ 2 ≤ 1 := by nlinarith [norm_nonneg z]
  have hm := mul_le_mul_of_nonneg_left hs hγ
  have he : Real.exp (-γ / 2) ≤ Real.exp (-γ * ‖z‖ ^ 2 / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  simpa [pointWeight] using mul_le_mul_of_nonneg_right he
    (Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (norm_nonneg (z - y j)) (a j)))

theorem pointPartition_unitDisk_lower_uniform {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    ENNReal.ofReal (pointDiskLowerConstant γ Q * pointLocationFactor a y) ≤
      pointPartition γ a y := by
  have hv : (volume.restrict (closedBall (0 : ℂ) 1)).real univ = Real.pi := by
    simp [Measure.real, Complex.volume_closedBall]
  have hw0 : IntegrableOn (pointWeight 0 a y) (closedBall (0 : ℂ) 1) :=
    (pointWeight_continuous 0 ha y).continuousOn.integrableOn_compact (isCompact_closedBall (0 : ℂ) 1)
  have hwγ := (pointWeight_integrable hγ ha y).integrableOn (s := closedBall (0 : ℂ) 1)
  have hj := mul_le_mul_of_nonneg_left (unitDisk_raw_weight_jensen ha hQ y) Real.pi_pos.le
  rw [average_eq, hv] at hj
  have hcancel : Real.pi * ((Real.pi)⁻¹ •
      ∫ z in closedBall (0 : ℂ) 1, pointWeight 0 a y z) =
      ∫ z in closedBall (0 : ℂ) 1, pointWeight 0 a y z := by
    simp only [smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ Real.pi_ne_zero, one_mul]
  rw [hcancel] at hj
  have hbound : pointDiskLowerConstant γ Q * pointLocationFactor a y ≤
      ∫ z in closedBall (0 : ℂ) 1, pointWeight γ a y z := by
    calc
      _ = Real.exp (-γ / 2) *
          (Real.pi * (Real.exp (-(Real.log 2 + 1 / 2) * Q) * pointLocationFactor a y)) := by
        rw [pointDiskLowerConstant, sub_eq_add_neg, Real.exp_add]
        simp only [neg_mul]
        ring
      _ ≤ Real.exp (-γ / 2) * ∫ z in closedBall (0 : ℂ) 1, pointWeight 0 a y z :=
        mul_le_mul_of_nonneg_left hj (Real.exp_pos _).le
      _ = ∫ z in closedBall (0 : ℂ) 1, Real.exp (-γ / 2) * pointWeight 0 a y z :=
        (integral_const_mul _ _).symm
      _ ≤ _ := setIntegral_mono_on (hw0.const_mul _) hwγ isClosed_closedBall.measurableSet
        (fun z hz => pointWeight_unitDisk_gaussian_lower hγ.le a y hz)
  calc
    _ ≤ ENNReal.ofReal (∫ z in closedBall (0 : ℂ) 1, pointWeight γ a y z) :=
      ENNReal.ofReal_le_ofReal hbound
    _ = ∫⁻ z in closedBall (0 : ℂ) 1, ENNReal.ofReal (pointWeight γ a y z) :=
      ofReal_integral_eq_lintegral_ofReal hwγ (Eventually.of_forall (pointWeight_nonneg γ a y))
    _ ≤ pointPartition γ a y := lintegral_mono' Measure.restrict_le_self le_rfl

/-- The same displayed witness directly for the manuscript's real partition integral. -/
theorem pointPartition_integral_unitDisk_lower {m : ℕ} {γ Q : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ) :
    Real.pi * Real.exp (-γ / 2 - (Real.log 2 + 1 / 2) * Q) * pointLocationFactor a y ≤
      ∫ z : ℂ, pointWeight γ a y z := by
  have h := pointPartition_unitDisk_lower_uniform hγ ha hQ y
  rw [pointPartition_eq_ofReal_integral hγ ha y] at h
  exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (pointWeight_nonneg γ a y))).mp h

end RepulsiveCoulomb
