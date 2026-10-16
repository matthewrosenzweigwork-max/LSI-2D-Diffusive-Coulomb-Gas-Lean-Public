module

public import LeanResearch.RepulsiveCoulomb.RawPointVolumeGrowth

@[expose] public section

/-! Explicit exponents satisfying the quantitative volume-balance condition in
Bjorn's Sobolev upgrade. This is exponent data, not an asserted Sobolev theorem. -/
noncomputable section
namespace RepulsiveCoulomb

def pointSobolevKappa (Q : ℝ) : ℝ := (Q + 2) / (Q + 1)
def pointSobolevGain (Q : ℝ) : ℝ := 1 / (2 * (Q + 2))

theorem pointSobolevKappa_gt_one {Q : ℝ} (hQ : 0 ≤ Q) : 1 < pointSobolevKappa Q := by
  unfold pointSobolevKappa
  apply (one_lt_div (by linarith : 0 < Q + 1)).mpr
  linarith

theorem pointSobolevGain_pos {Q : ℝ} (hQ : 0 ≤ Q) : 0 < pointSobolevGain Q := by
  unfold pointSobolevGain
  positivity

theorem pointSobolevGain_add_inverse {Q : ℝ} (hQ : 0 ≤ Q) :
    pointSobolevGain Q + 1 / (2 * pointSobolevKappa Q) = 1 / 2 := by
  unfold pointSobolevGain pointSobolevKappa
  field_simp [show Q + 1 ≠ 0 by linarith, show Q + 2 ≠ 0 by linarith]
  <;> ring

theorem pointSobolevGain_volume_exponent {Q : ℝ} (hQ : 0 ≤ Q) :
    (Q + 2) * pointSobolevGain Q = 1 / 2 := by
  unfold pointSobolevGain
  field_simp [show Q + 2 ≠ 0 by linarith]

theorem pointSobolev_interpolation_exponent {Q : ℝ} (hQ : 0 ≤ Q) :
    pointSobolevKappa Q / (2 * pointSobolevKappa Q - 1) = (Q + 2) / (Q + 3) := by
  unfold pointSobolevKappa
  field_simp [show Q + 1 ≠ 0 by linarith, show Q + 3 ≠ 0 by linarith]
  <;> ring_nf
  <;> field_simp [show 3 + Q ≠ 0 by linarith]
  <;> ring

theorem pointSobolev_superPoincare_power {Q : ℝ} (hQ : 0 ≤ Q) :
    pointSobolevKappa Q / (pointSobolevKappa Q - 1) = Q + 2 := by
  unfold pointSobolevKappa
  field_simp [show Q + 1 ≠ 0 by linarith]
  <;> ring

theorem power_balance_of_mass_bound {t u A s δ β : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hu : 0 < u) (hA : 0 < A) (hδ : 0 ≤ δ)
    (hsδ : s * δ ≤ 1) (he : δ + β = 1 / 2) (hm : t ^ s ≤ A * u) :
    t * u ^ β ≤ A ^ δ * u ^ (1 / 2 : ℝ) := by
  have h := Real.rpow_le_rpow (Real.rpow_nonneg ht.le _) hm hδ
  rw [← Real.rpow_mul ht.le, Real.mul_rpow hA.le hu.le] at h
  have ht' : t ≤ t ^ (s * δ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge ht ht1 hsδ
  calc
    _ ≤ (A ^ δ * u ^ δ) * u ^ β :=
      mul_le_mul_of_nonneg_right (ht'.trans h) (Real.rpow_nonneg hu.le _)
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hu, he]

end RepulsiveCoulomb
