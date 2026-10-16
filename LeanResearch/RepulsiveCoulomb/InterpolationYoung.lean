import Mathlib.Analysis.MeanInequalities

/-! Tunable real-power absorption for the super-Poincare interpolation. -/
noncomputable section
namespace RepulsiveCoulomb

theorem rpow_interpolation_young {θ t x y : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (ht : 0 < t) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    x ^ θ * y ^ (1 - θ) ≤ t * x + t ^ (-θ / (1 - θ)) * y := by
  have he : θ + (-θ / (1 - θ)) * (1 - θ) = 0 := by
    field_simp [show 1 - θ ≠ 0 by linarith]
    <;> ring
  have hp : t ^ θ * (t ^ (-θ / (1 - θ))) ^ (1 - θ) = 1 := by
    rw [← Real.rpow_mul ht.le, ← Real.rpow_add ht, he, Real.rpow_zero]
  have h := Real.geom_mean_le_arith_mean2_weighted hθ0.le
    (show 0 ≤ 1 - θ by linarith) (mul_nonneg ht.le hx)
    (mul_nonneg (Real.rpow_nonneg ht.le (-θ / (1 - θ))) hy) (by ring : θ + (1 - θ) = 1)
  rw [Real.mul_rpow ht.le hx, Real.mul_rpow (Real.rpow_nonneg ht.le (-θ / (1 - θ))) hy] at h
  have hid : t ^ θ * x ^ θ * ((t ^ (-θ / (1 - θ))) ^ (1 - θ) * y ^ (1 - θ)) =
      x ^ θ * y ^ (1 - θ) := by
    calc
      _ = (t ^ θ * (t ^ (-θ / (1 - θ))) ^ (1 - θ)) * (x ^ θ * y ^ (1 - θ)) := by ring
      _ = _ := by rw [hp, one_mul]
  rw [hid] at h
  have h1 := mul_le_mul_of_nonneg_right hθ1.le (mul_nonneg ht.le hx)
  have h2 := mul_le_mul_of_nonneg_right (show 1 - θ ≤ 1 by linarith)
    (mul_nonneg (Real.rpow_nonneg ht.le (-θ / (1 - θ))) hy)
  nlinarith

theorem scaled_interpolation_young {θ A u E L : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hA : 0 < A) (hu : 0 < u)
    (hE : 0 ≤ E) (hL : 0 ≤ L) :
    A * (E ^ θ * L ^ (1 - θ)) ≤
      u * E + (A * (u / A) ^ (-θ / (1 - θ))) * L := by
  have h := mul_le_mul_of_nonneg_left
    (rpow_interpolation_young hθ0 hθ1 (div_pos hu hA) hE hL) hA.le
  have hid : A * ((u / A) * E + (u / A) ^ (-θ / (1 - θ)) * L) =
      u * E + (A * (u / A) ^ (-θ / (1 - θ))) * L := by
    field_simp
    <;> ring
  rwa [hid] at h

end RepulsiveCoulomb
