module

public import LeanResearch.RepulsiveCoulomb.IntegralPowerInterpolation
public import LeanResearch.RepulsiveCoulomb.InterpolationYoung

@[expose] public section

/-! L1--Lq interpolation in squared-norm form, and local energy absorption. -/
noncomputable section
open MeasureTheory
namespace RepulsiveCoulomb

theorem l1_lq_l2_interpolation {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {f : X → ℝ} {r : ℝ} (hr : 2 < r)
    (h1 : Integrable (fun x => |f x|) μ)
    (hrint : Integrable (fun x => |f x| ^ r) μ)
    (h2 : Integrable (fun x => f x ^ 2) μ) :
    (∫ x, f x ^ 2 ∂μ) ≤
      ((∫ x, |f x| ^ r ∂μ) ^ (2 / r)) ^ (r / (2 * (r - 1))) *
        ((∫ x, |f x| ∂μ) ^ 2) ^ (1 - r / (2 * (r - 1))) := by
  have hd : 0 < r - 1 := by linarith
  have hp : 0 < (r - 2) / (r - 1) := div_pos (by linarith) hd
  have hq : 0 < 1 / (r - 1) := one_div_pos.mpr hd
  have he1 : (r - 2) / (r - 1) + 1 / (r - 1) = 1 := by field_simp <;> ring
  have he2 : (r - 2) / (r - 1) + r * (1 / (r - 1)) = 2 := by field_simp <;> ring
  have h := integral_l1_rpow_interpolation (by linarith : 0 < r) hp hq he1 he2 h1 hrint h2
  have hL : 0 ≤ ∫ x, |f x| ∂μ := integral_nonneg (fun x => abs_nonneg (f x))
  have hN : 0 ≤ ∫ x, |f x| ^ r ∂μ := integral_nonneg (fun x => Real.rpow_nonneg (abs_nonneg (f x)) r)
  rw [← Real.rpow_mul hN]
  have he3 : (2 / r) * (r / (2 * (r - 1))) = 1 / (r - 1) := by field_simp <;> ring
  rw [he3, ← Real.rpow_two (∫ x, |f x| ∂μ), ← Real.rpow_mul hL]
  have he4 : (2 : ℝ) * (1 - r / (2 * (r - 1))) = (r - 2) / (r - 1) := by field_simp <;> ring
  rw [he4, mul_comm]
  exact h

theorem local_norm_square_bound {N L E H : ℝ} (hN : 0 ≤ N) (hL : 0 ≤ L)
    (hE : 0 ≤ E) (hH : 0 ≤ H) (h : N ≤ 2 * L + 2 * H * Real.sqrt E) :
    N ^ 2 ≤ (8 + 8 * H ^ 2) * (E + L ^ 2) := by
  have hs := mul_self_le_mul_self hN h
  have hy := sq_nonneg (L - H * Real.sqrt E)
  have hr := Real.sq_sqrt hE
  have hh := mul_nonneg (sq_nonneg H) (sq_nonneg L)
  nlinarith

theorem local_interpolation_energy_absorb {M N L E D θ u : ℝ}
    (hN : 0 ≤ N) (hL : 0 ≤ L) (hE : 0 ≤ E) (hD : 0 < D)
    (hθ0 : 0 < θ) (hθ1 : θ < 1) (hu : 0 < u)
    (hi : M ≤ N ^ θ * L ^ (1 - θ)) (hs : N ≤ D * (E + L)) :
    M ≤ u * E + (u + D ^ θ * (u / D ^ θ) ^ (-θ / (1 - θ))) * L := by
  have hn := Real.rpow_le_rpow hN hs hθ0.le
  rw [Real.mul_rpow hD.le (add_nonneg hE hL)] at hn
  have hm := hi.trans (mul_le_mul_of_nonneg_right hn (Real.rpow_nonneg hL _))
  have hy := scaled_interpolation_young hθ0 hθ1 (Real.rpow_pos_of_pos hD θ) hu
    (add_nonneg hE hL) hL
  have hid : D ^ θ * (E + L) ^ θ * L ^ (1 - θ) =
      D ^ θ * ((E + L) ^ θ * L ^ (1 - θ)) := by ring
  rw [hid] at hm
  have hb := hm.trans hy
  nlinarith only [hb]

end RepulsiveCoulomb
