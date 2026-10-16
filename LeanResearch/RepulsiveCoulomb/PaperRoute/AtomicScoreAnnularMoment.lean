import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicScoreAnnularMass
import LeanResearch.RepulsiveCoulomb.PointScoreAnnularDecomposition

/-! Finite dyadic annular summation and absorption, using the new atomic-maximal K.
The generic overlap constants 3 and 12 and absorption delta=1/96 are unchanged.

Proof bodies are adapted from the corresponding frozen score/annular/moment
modules. This new application replaces every hardwired old weak-force, bad-area,
uncertainty and moment producer with the new finite-atomic maximal route.
Generic cutoff, overlap, integrability, ground-state and Fatou identities are
reused unchanged; actual proof-body dependencies are audited separately. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem atomic_pointScore_annular_uniform_bound {m : ℕ} {γ Q R C : ℝ}
    (hγ : 0 < γ) (hR : 1 ≤ R) (hC : 0 ≤ C)
    (hbound : ∀ z : ℂ, ‖gradient (annularCutoff R) z‖ ≤ C / R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q)
    (ψ : ℂ → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hscore : Integrable (fun x => ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2)) :
    R ^ 2 * (∫ x in scoreRadialAnnulus R, ψ x ^ 2) ≤
      (4 / γ ^ 2) * (∫ x in enlargedScoreAnnulus R, ‖pointScore γ a y x‖ ^ 2 * ψ x ^ 2) +
      (1 / 96 : ℝ) * R ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2) +
      48 * atomicScoreAnnularMassConstant γ Q ^ 2 * (∫ x in enlargedScoreAnnulus R, ‖gradient ψ x‖ ^ 2) +
      48 * atomicScoreAnnularMassConstant γ Q ^ 2 * C ^ 2 * (∫ x in enlargedScoreAnnulus R, ψ x ^ 2) := by
  have hRp : 0 < R := by linarith
  have hb := atomic_pointScore_bad_annulus_localized hRp hC hbound hγ
    (by norm_num : (0 : ℝ) < 1 / 96) ha y hQ ψ hψ
  have hg := pointScore_annular_mass_decomposition hγ hRp a y ψ hψ.continuous hscore
  have hratio : 0 ≤ C / R := div_nonneg hC hRp.le
  have hratioupper : C / R ≤ C := (div_le_iff₀ hRp).mpr (by nlinarith)
  have hsq : (C / R) ^ 2 ≤ C ^ 2 := by nlinarith
  have hmass : 0 ≤ ∫ x in enlargedScoreAnnulus R, ψ x ^ 2 := integral_nonneg (fun _ => sq_nonneg _)
  have hscaled := mul_le_mul_of_nonneg_right hsq hmass
  have hk := mul_le_mul_of_nonneg_left hscaled (sq_nonneg (atomicScoreAnnularMassConstant γ Q))
  norm_num at hb
  nlinarith [hg, hb, hk]

theorem atomic_pointScore_finite_moment_bound {m : ℕ} {γ Q C : ℝ}
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
      1152 * atomicScoreAnnularMassConstant γ Q ^ 2 * (∫ x, ‖gradient ψ x‖ ^ 2) +
      (2 + 1152 * atomicScoreAnnularMassConstant γ Q ^ 2 * C ^ 2) * (∫ x, ψ x ^ 2) := by
  let K := atomicScoreAnnularMassConstant γ Q
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
      atomic_pointScore_annular_uniform_bound hγ hr hC (hbound _ hrp) ha y hQ ψ hψ hscore
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

end RepulsiveCoulomb.PaperRoute
