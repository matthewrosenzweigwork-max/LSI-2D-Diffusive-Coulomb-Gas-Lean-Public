module

public import LeanResearch.RepulsiveCoulomb.HedbergPowerIdentity

@[expose] public section

/-! Exact normalization of the weak Sobolev coefficient. -/
noncomputable section
namespace RepulsiveCoulomb

theorem pointSobolevGain_times_q {Q : ℝ} (hQ : 0 ≤ Q) :
    pointSobolevGain Q * (2 * pointSobolevKappa Q) = 1 / (Q + 1) := by
  unfold pointSobolevGain pointSobolevKappa
  have h1 : Q + 1 ≠ 0 := by positivity
  have h2 : Q + 2 ≠ 0 := by positivity
  field_simp

theorem pointSobolevGain_times_q_add_one {Q : ℝ} (hQ : 0 ≤ Q) :
    pointSobolevGain Q * (2 * pointSobolevKappa Q) + 1 = pointSobolevKappa Q := by
  rw [pointSobolevGain_times_q hQ]
  unfold pointSobolevKappa
  have h1 : Q + 1 ≠ 0 := by positivity
  field_simp
  ring

theorem sobolev_distribution_coefficient {C D G R I N q δ κ : ℝ}
    (hC : 0 ≤ C) (hG : 0 ≤ G) (hR : 0 ≤ R) (hI : 0 ≤ I) (hN : 0 < N)
    (hexp : δ * q + 1 = κ) (hκ : κ ≠ 0) :
    (C * R * (G * I / N) ^ δ) ^ q * (D * I) =
      (D * C ^ q * G ^ (δ * q)) * R ^ q * N * (I / N) ^ κ := by
  have hu : 0 ≤ I / N := div_nonneg hI hN.le
  have hE : 0 ≤ G * I / N := div_nonneg (mul_nonneg hG hI) hN.le
  rw [Real.mul_rpow (mul_nonneg hC hR) (Real.rpow_nonneg hE δ),
    Real.mul_rpow hC hR, ← Real.rpow_mul hE]
  rw [mul_div_assoc, Real.mul_rpow hG hu]
  have hi : I = N * (I / N) := by field_simp
  have hp : (I / N) ^ (δ * q) * (I / N) = (I / N) ^ κ := by
    rw [← Real.rpow_add_one' hu (by rwa [hexp]), hexp]
  calc
    _ = (D * C ^ q * G ^ (δ * q)) * R ^ q * N *
        ((I / N) ^ (δ * q) * (I / N)) := by
      conv_lhs => rhs; rhs; rw [hi]
      ring
    _ = _ := by rw [hp]

end RepulsiveCoulomb
