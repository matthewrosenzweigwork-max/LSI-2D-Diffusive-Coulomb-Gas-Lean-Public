import LeanResearch.RepulsiveCoulomb.PointSobolevExponents

/-! Exact exponents in the pointwise Sobolev interpolation bound. -/
noncomputable section
namespace RepulsiveCoulomb

def pointSobolevMaximalExponent (Q : ℝ) : ℝ := (Q + 1) / (2 * (Q + 2))

theorem pointSobolevMaximalExponent_pos {Q : ℝ} (hQ : 0 ≤ Q) :
    0 < pointSobolevMaximalExponent Q := by unfold pointSobolevMaximalExponent; positivity

theorem pointSobolevMaximalExponent_times_q {Q : ℝ} (hQ : 0 ≤ Q) :
    pointSobolevMaximalExponent Q * (2 * pointSobolevKappa Q) = 1 := by
  unfold pointSobolevMaximalExponent pointSobolevKappa
  have h1 : Q + 1 ≠ 0 := by positivity
  have h2 : Q + 2 ≠ 0 := by positivity
  field_simp

theorem hedberg_quotient_eq_power {A B t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (ht : 0 < t) (ht1 : t < 1) :
    A / (A / B) ^ t = A ^ (1 - t) * B ^ t := by
  by_cases ha : A = 0
  · simp [ha, Real.zero_rpow (by linarith : 1 - t ≠ 0)]
  by_cases hb : B = 0
  · simp [hb, Real.zero_rpow ht.ne']
  have hAp : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
  rw [Real.div_rpow hA hB, div_div_eq_mul_div, Real.rpow_sub hAp, Real.rpow_one]
  ring

theorem hedberg_sqrt_quotient_eq_power {Q M E : ℝ} (hQ : 0 ≤ Q) (hM : 0 ≤ M) (hE : 0 ≤ E) :
    Real.sqrt M / (Real.sqrt M / Real.sqrt E) ^ (1 / (Q + 2)) =
      M ^ pointSobolevMaximalExponent Q * E ^ pointSobolevGain Q := by
  have hk : 0 < Q + 2 := by positivity
  have ht : 0 < 1 / (Q + 2) := by positivity
  have ht1 : 1 / (Q + 2) < 1 := (div_lt_one hk).mpr (by linarith)
  rw [hedberg_quotient_eq_power (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) ht ht1,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hM, ← Real.rpow_mul hE]
  congr 1
  · congr 1
    unfold pointSobolevMaximalExponent
    field_simp
    ring
  · congr 1
    unfold pointSobolevGain
    field_simp

end RepulsiveCoulomb
