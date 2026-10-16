import LeanResearch.RepulsiveCoulomb.PointCoreSmoothTruncation
import Mathlib.Analysis.SpecificLimits.Normed

/-! Weighted dyadic mass bounds directly from the proved Gaussian SPI. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem finite_dyadic_geometric_error (N : ℕ) :
    (∑ k ∈ Finset.range N, ((k : ℝ) + 1) / (2 : ℝ) ^ (k + 1)) ≤ 2 := by
  have hs : HasSum (fun n : ℕ => (n : ℝ) * (1 / 2 : ℝ) ^ n) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one (r := (1 / 2 : ℝ)) (by norm_num) using 1 <;> norm_num
  have h := sum_le_hasSum (Finset.range (N + 1)) (fun n _ => by positivity) hs
  rw [Finset.sum_range_succ'] at h
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, pow_zero, zero_mul, add_zero,
    div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using h

theorem pointCore_spi_weighted_truncation {m : ℕ} {γ A B : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hA : 0 < A) (hB : 0 < B)
    (hSPI : ∀ s : ℝ, 0 < s → ∀ ψ : TestFunction (pointDomain a y) ℝ ⊤,
      (∫ x, ψ x ^ 2 ∂pointMeasure γ a y) ≤
        s * (∫ x, ‖gradient (ψ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * Real.exp (B / s) * (∫ x, |ψ x| ∂pointMeasure γ a y) ^ 2)
    (φ : TestFunction (pointDomain a y) ℝ ⊤)
    (hφ : (∫ x, φ x ^ 2 ∂pointMeasure γ a y) = 1) (k : ℕ) :
    ((k : ℝ) + 1) * (∫ x, (pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) φ x) ^ 2 ∂pointMeasure γ a y) ≤
      (B / Real.log 2) * (∫ x, ‖gradient
        (pointCoreSmoothTruncation ((2 : ℝ) ^ (k + 1)) (by positivity) φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) +
        A * (((k : ℝ) + 1) / (2 : ℝ) ^ (k + 1)) := by
  let b : ℝ := (2 : ℝ) ^ (k + 1)
  have hb : 0 < b := by dsimp [b]; positivity
  let ψ := pointCoreSmoothTruncation b hb φ
  let j : ℝ := (k : ℝ) + 1
  have hj : 0 < j := by dsimp [j]; positivity
  have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  let s := B / (j * Real.log 2)
  have hs : 0 < s := div_pos hB (mul_pos hj hl)
  have hrate : Real.exp (B / s) = b := by
    have hid : B / s = j * Real.log 2 := by dsimp [s]; field_simp
    rw [hid]
    change Real.exp (((k : ℝ) + 1) * Real.log 2) = (2 : ℝ) ^ (k + 1)
    rw [← Nat.cast_add_one, Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hl1 := pointCore_truncation_l1_le_mass hγ ha y hb φ
  rw [hφ] at hl1
  have hlsq : (∫ x, |ψ x| ∂pointMeasure γ a y) ^ 2 ≤ (1 / b) ^ 2 := by
    have hn : 0 ≤ ∫ x, |ψ x| ∂pointMeasure γ a y := integral_nonneg (fun _ => abs_nonneg _)
    change (∫ x, |ψ x| ∂pointMeasure γ a y) ≤ 1 / b at hl1
    nlinarith [one_div_pos.mpr hb]
  have h := hSPI s hs ψ
  rw [hrate] at h
  have h' := h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left hlsq (mul_pos hA hb).le))
  have h'' := mul_le_mul_of_nonneg_left h' hj.le
  have hc : j * s = B / Real.log 2 := by dsimp [s]; field_simp
  have he : A * b * (1 / b) ^ 2 = A / b := by field_simp
  rw [he] at h''
  change j * (∫ x, ψ x ^ 2 ∂pointMeasure γ a y) ≤ _
  calc
    _ ≤ j * (s * (∫ x, ‖gradient (ψ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) + A / b) := h''
    _ = _ := by rw [mul_add, ← mul_assoc, hc]; ring

end RepulsiveCoulomb
