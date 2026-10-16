import LeanResearch.RepulsiveCoulomb.PointScoreAnnularUniformBound

/-! Finite dyadic summation and absorption with explicit analytic premises.
The next core application must discharge every integrability/support premise. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem pointScore_finite_moment_bound {m : ℕ} {γ Q C : ℝ}
    (hγ : 0 < γ) (hC : 0 ≤ C)
    (hbound : ∀ R : ℝ, 0 < R → ∀ z : ℂ, ‖gradient (annularCutoff R) z‖ ≤ C / R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hmass : Integrable (fun x => ψ x ^ 2))
    (henergy : Integrable (fun x => ‖gradient ψ x‖ ^ 2))
    (hmoment : Integrable (fun x => ‖x‖ ^ 2 * ψ x ^ 2))
    (hscore : Integrable (fun x => ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2))
    (N : ℕ) (hN : ∀ x, ψ x ^ 2 ≠ 0 → ‖x‖ < dyadicScoreRadius 1 N) :
    (∫ x, ‖x‖ ^ 2 * ψ x ^ 2) ≤
      (96 / γ ^ 2) * (∫ x, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2) +
      1152 * pointScoreAnnularMassConstant γ Q ^ 2 * (∫ x, ‖gradient ψ x‖ ^ 2) +
      (2 + 1152 * pointScoreAnnularMassConstant γ Q ^ 2 * C ^ 2) * (∫ x, ψ x ^ 2) := by
  let K := pointScoreAnnularMassConstant γ Q
  let s := Finset.range N
  let A : ℕ → ℝ := fun k => ∫ x in enlargedScoreAnnulus (dyadicScoreRadius 1 k), ψ x ^ 2
  let B : ℕ → ℝ := fun k => ∫ x in enlargedScoreAnnulus (dyadicScoreRadius 1 k), ‖gradient ψ x‖ ^ 2
  let S : ℕ → ℝ := fun k => ∫ x in enlargedScoreAnnulus (dyadicScoreRadius 1 k), ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2
  let W : ℕ → ℝ := fun k => (dyadicScoreRadius 1 k) ^ 2 *
    (∫ x in scoreRadialAnnulus (dyadicScoreRadius 1 k), ψ x ^ 2)
  have hl (k : ℕ) : W k ≤ (4 / γ ^ 2) * S k +
      (1 / 96 : ℝ) * ((dyadicScoreRadius 1 k) ^ 2 * A k) +
      (48 * K ^ 2) * B k + (48 * K ^ 2 * C ^ 2) * A k := by
    have hr : 1 ≤ dyadicScoreRadius 1 k := by
      simpa only [dyadicScoreRadius, mul_one] using (one_le_pow₀ (a := (2 : ℝ)) (by norm_num) : 1 ≤ (2 : ℝ) ^ k)
    have hrp := dyadicScoreRadius_pos (by norm_num : (0 : ℝ) < 1) k
    simpa only [W, S, A, B, K, mul_assoc] using
      pointScore_annular_uniform_bound hγ hr hC (hbound _ hrp) ha y hQ ψ hψ hscore
  have hsum := Finset.sum_le_sum (fun k (_hk : k ∈ s) => hl k)
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  have haSum : (∑ k ∈ s, A k) ≤ 3 * ∫ x, ψ x ^ 2 :=
    dyadicScoreAnnuli_integral_sum_le (by norm_num) s hmass (fun _ => sq_nonneg _)
  have hbSum : (∑ k ∈ s, B k) ≤ 3 * ∫ x, ‖gradient ψ x‖ ^ 2 :=
    dyadicScoreAnnuli_integral_sum_le (by norm_num) s henergy (fun _ => sq_nonneg _)
  have hsSum : (∑ k ∈ s, S k) ≤ 3 * ∫ x, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2 :=
    dyadicScoreAnnuli_integral_sum_le (by norm_num) s hscore
      (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hwSum : (∑ k ∈ s, (dyadicScoreRadius 1 k) ^ 2 * A k) ≤
      12 * ∫ x, ‖x‖ ^ 2 * ψ x ^ 2 :=
    dyadicScoreAnnuli_weighted_integral_sum_le (by norm_num) s hmass (fun _ => sq_nonneg _) hmoment
  have hm := dyadicScoreAnnuli_moment_integral (by norm_num : (0 : ℝ) < 1) N hmass
    (fun _ => sq_nonneg _) hmoment hN
  change (∫ x, ‖x‖ ^ 2 * ψ x ^ 2) ≤ 1 ^ 2 * (∫ x, ψ x ^ 2) + 4 * ∑ k ∈ s, W k at hm
  have hsScaled := mul_le_mul_of_nonneg_left hsSum (show 0 ≤ 4 / γ ^ 2 by positivity)
  have hbScaled := mul_le_mul_of_nonneg_left hbSum (show 0 ≤ 48 * K ^ 2 by positivity)
  have haScaled := mul_le_mul_of_nonneg_left haSum (show 0 ≤ 48 * K ^ 2 * C ^ 2 by positivity)
  have hwScaled := mul_le_mul_of_nonneg_left hwSum (show (0 : ℝ) ≤ 1 / 96 by norm_num)
  change (∫ x, ‖x‖ ^ 2 * ψ x ^ 2) ≤ (96 / γ ^ 2) * _ + 1152 * K ^ 2 * _ + (2 + 1152 * K ^ 2 * C ^ 2) * _
  have hcoef : 96 / γ ^ 2 = 24 * (4 / γ ^ 2) := by ring
  rw [hcoef]
  nlinarith only [hm, hsum, hsScaled, hbScaled, haScaled, hwScaled]

end RepulsiveCoulomb
