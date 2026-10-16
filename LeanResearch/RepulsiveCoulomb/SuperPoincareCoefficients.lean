import LeanResearch.RepulsiveCoulomb.InterpolationYoung

/-! Exact Young coefficient and Gaussian-radius majorants. -/
noncomputable section
namespace RepulsiveCoulomb

theorem interpolation_coefficient_identity {D u θ : ℝ} (hD : 0 < D) (hu : 0 < u)
    (hθ : θ < 1) :
    D ^ θ * (u / D ^ θ) ^ (-θ / (1 - θ)) =
      D ^ (θ / (1 - θ)) * u ^ (-θ / (1 - θ)) := by
  rw [Real.div_rpow hu.le (Real.rpow_nonneg hD.le _)]
  calc
    _ = (D ^ θ / (D ^ θ) ^ (-θ / (1 - θ))) * u ^ (-θ / (1 - θ)) := by ring
    _ = D ^ (θ - θ * (-θ / (1 - θ))) * u ^ (-θ / (1 - θ)) := by
      rw [← Real.rpow_mul hD.le, Real.rpow_sub hD]
    _ = _ := by
      congr 2
      field_simp [show 1 - θ ≠ 0 by linarith]
      <;> ring

theorem local_gaussian_square_coefficient {C R : ℝ} (hC : 0 ≤ C) :
    8 + 8 * (C * Real.exp (C * R ^ 2) * R) ^ 2 ≤
      (8 + 8 * C ^ 2) * Real.exp ((2 * C + 1) * R ^ 2) := by
  have hR : R ^ 2 ≤ Real.exp (R ^ 2) := by linarith [Real.add_one_le_exp (R ^ 2)]
  have he : 1 ≤ Real.exp ((2 * C + 1) * R ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hR
    (mul_nonneg (sq_nonneg C) (Real.exp_pos (2 * (C * R ^ 2))).le)
  have hid : (C * Real.exp (C * R ^ 2) * R) ^ 2 =
      C ^ 2 * Real.exp (2 * (C * R ^ 2)) * R ^ 2 := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul]
    ring
  have heq : C ^ 2 * Real.exp (2 * (C * R ^ 2)) * Real.exp (R ^ 2) =
      C ^ 2 * Real.exp ((2 * C + 1) * R ^ 2) := by
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq] at hmul
  rw [hid]
  nlinarith only [hmul, he]

theorem local_spi_coefficient_bound {D A B η u R : ℝ}
    (hD : 0 ≤ D) (hA : 0 < A) (hB : 0 ≤ B) (hη : 0 ≤ η)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (h : D ≤ A * Real.exp (B * R ^ 2)) :
    u + D ^ η * u ^ (-η) ≤ (1 + A ^ η) * Real.exp ((B * η) * R ^ 2) * u ^ (-η) := by
  have hpow := Real.rpow_le_rpow hD h hη
  rw [Real.mul_rpow hA.le (Real.exp_pos _).le, ← Real.exp_mul] at hpow
  have he : 1 ≤ Real.exp ((B * η) * R ^ 2) := Real.one_le_exp_iff.mpr (by positivity)
  have huPow : 1 ≤ u ^ (-η) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_ge hu hu1 (show -η ≤ 0 by linarith)
  have hfirst : u ≤ Real.exp ((B * η) * R ^ 2) * u ^ (-η) :=
    hu1.trans (one_le_mul_of_one_le_of_one_le he huPow)
  have hsecond := mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hu.le (-η))
  have heq : B * R ^ 2 * η = (B * η) * R ^ 2 := by ring
  rw [heq] at hsecond
  nlinarith only [hfirst, hsecond]

end RepulsiveCoulomb
