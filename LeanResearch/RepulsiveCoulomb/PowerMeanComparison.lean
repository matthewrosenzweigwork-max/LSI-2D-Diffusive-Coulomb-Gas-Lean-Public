import LeanResearch.RepulsiveCoulomb.MeanRpowCentering

/-! Actual comparison of quadratic and higher moments under a finite measure. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem average_sq_le_average_rpow {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] [NeZero μ] (u : X → ℝ) {κ : ℝ} (hκ : 1 ≤ κ)
    (hsq : Integrable (fun x => ‖u x‖ ^ 2) μ)
    (hp : Integrable (fun x => ‖u x‖ ^ (2 * κ)) μ) :
    (⨍ x, ‖u x‖ ^ 2 ∂μ) ≤ (⨍ x, ‖u x‖ ^ (2 * κ) ∂μ) ^ (1 / κ) := by
  have hκ0 : 0 < κ := lt_of_lt_of_le zero_lt_one hκ
  have he (x : X) : (‖u x‖ ^ 2) ^ κ = ‖u x‖ ^ (2 * κ) := by
    simpa only [Nat.cast_ofNat] using (Real.rpow_natCast_mul (norm_nonneg (u x)) 2 κ).symm
  have hp' : Integrable (fun x => (‖u x‖ ^ 2) ^ κ) μ := by simpa only [he] using hp
  have hj := (convexOn_rpow hκ).map_average_le
    (Real.continuous_rpow_const hκ0.le).continuousOn isClosed_Ici
    (Eventually.of_forall (fun x => sq_nonneg ‖u x‖)) hsq hp'
  simp only [he] at hj
  rw [one_div]
  exact (Real.le_rpow_inv_iff_of_pos (average_nonneg (fun x => sq_nonneg _))
    (average_nonneg (fun x => Real.rpow_nonneg (norm_nonneg _) _)) hκ0).mpr hj

end RepulsiveCoulomb
