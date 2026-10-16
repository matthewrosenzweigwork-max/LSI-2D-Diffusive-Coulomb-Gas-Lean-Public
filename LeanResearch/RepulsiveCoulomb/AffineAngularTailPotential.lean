import LeanResearch.RepulsiveCoulomb.ScalarTailPotentialComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

/-! Uncompiled additive successor. Explicit decreasing angular-tail potential
in the original affine parameter. No inverse radius map or FTC is assumed. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def angularTailPotential (A B D r : ℝ) : ℝ :=
  (2 / (1 + B)) * (Real.rpow A (1 + B) / Real.rpow r (1 + B)) + (2 * D / B) / r

theorem angularTailPotential_hasDerivAt
    {r : ℝ → ℝ} {t A B D r' : ℝ} (hr : 0 < r t) (hB : 0 < B)
    (hrD : HasDerivAt r r' t) :
    HasDerivAt (fun u => angularTailPotential A B D (r u))
      (-(2 * (Real.rpow A (1 + B) / Real.rpow (r t) (1 + B) + D / (B * r t)) * r' / r t)) t := by
  have hp : 0 < 1 + B := by linarith
  have hrpow : 0 < (r t) ^ (1 + B) := Real.rpow_pos_of_pos hr _
  have hpowD := hrD.rpow_const (p := 1 + B) (Or.inl (ne_of_gt hr))
  have hfirst := ((hasDerivAt_const t (Real.rpow A (1 + B))).fun_div hpowD (ne_of_gt hrpow)).const_mul (2 / (1 + B))
  have hsecond := (hasDerivAt_const t (2 * D / B)).fun_div hrD (ne_of_gt hr)
  have h := hfirst.add hsecond
  have hpow : (r t) ^ (1 + B) = (r t) ^ B * r t := by
    rw [show 1 + B = B + 1 by ring, Real.rpow_add hr, Real.rpow_one]
  have hBpow : 0 < (r t) ^ B := Real.rpow_pos_of_pos hr _
  convert h using 1
  · rfl
  · simp only [Real.rpow_eq_pow, zero_mul, sub_zero, zero_sub,
      show 1 + B - 1 = B by ring]
    rw [hpow]
    field_simp [ne_of_gt hr, ne_of_gt hB, ne_of_gt hp, ne_of_gt hBpow] <;> ring

theorem cos_half_le_of_nonneg_of_abs_sin_le_half {ψ : ℝ}
    (hcos : 0 ≤ Real.cos ψ) (hsin : |Real.sin ψ| ≤ 1 / 2) : 1 / 2 ≤ Real.cos ψ := by
  have hs := abs_le.mp hsin
  have hmul := mul_nonneg (by linarith : 0 ≤ 1 / 2 - Real.sin ψ)
    (by linarith : 0 ≤ 1 / 2 + Real.sin ψ)
  have htrig := Real.sin_sq_add_cos_sq ψ
  nlinarith

theorem affine_angular_derivative_le_tail
    {r v ψ H : ℝ} (hr : 0 < r) (hv : 0 ≤ v)
    (hcos : 1 / 2 ≤ Real.cos ψ) (hsin : |Real.sin ψ| ≤ H) :
    |(v / r) * Real.sin ψ| ≤ 2 * H * (v * Real.cos ψ) / r := by
  have hH : 0 ≤ H := (abs_nonneg _).trans hsin
  rw [abs_mul, abs_of_nonneg (div_nonneg hv hr.le)]
  calc
    (v / r) * |Real.sin ψ| ≤ (v / r) * H := mul_le_mul_of_nonneg_left hsin (div_nonneg hv hr.le)
    _ ≤ 2 * H * (v * Real.cos ψ) / r := by
      rw [div_mul_eq_mul_div]
      apply (div_le_div_iff_of_pos_right hr).mpr
      nlinarith [mul_nonneg hv hH]

theorem angular_increment_bound_of_affine_tail_data
    {r φ ψ v : ℝ → ℝ} {a b A B D : ℝ} (hab : a ≤ b)
    (hA : 0 ≤ A) (hB : 0 < B) (hD : 0 ≤ D)
    (hrc : ContinuousOn r (Icc a b)) (hφc : ContinuousOn φ (Icc a b))
    (hr : ∀ t ∈ Icc a b, 0 < r t)
    (hv : ∀ t ∈ Ioo a b, 0 ≤ v t)
    (hrD : ∀ t ∈ Ioo a b, HasDerivAt r (v t * Real.cos (ψ t)) t)
    (hφD : ∀ t ∈ Ioo a b, HasDerivAt φ ((v t / r t) * Real.sin (ψ t)) t)
    (hcos : ∀ t ∈ Ioo a b, 1 / 2 ≤ Real.cos (ψ t))
    (hsin : ∀ t ∈ Ioo a b, |Real.sin (ψ t)| ≤
      Real.rpow A (1 + B) / Real.rpow (r t) (1 + B) + D / (B * r t)) :
    |φ b - φ a| ≤ angularTailPotential A B D (r a) := by
  let G : ℝ → ℝ := fun t => angularTailPotential A B D (r t)
  let G' : ℝ → ℝ := fun t => -(2 *
    (Real.rpow A (1 + B) / Real.rpow (r t) (1 + B) + D / (B * r t)) *
      (v t * Real.cos (ψ t)) / r t)
  have hGc : ContinuousOn G (Icc a b) := by
    unfold G angularTailPotential
    apply ContinuousOn.add
    · apply ContinuousOn.mul continuousOn_const
      exact continuousOn_const.div
        (hrc.rpow_const (fun t ht => Or.inl (ne_of_gt (hr t ht))))
        (fun t ht => ne_of_gt (Real.rpow_pos_of_pos (hr t ht) _))
    · exact continuousOn_const.div hrc (fun t ht => ne_of_gt (hr t ht))
  have hGd : ∀ t ∈ Ioo a b, HasDerivAt G (G' t) t := by
    intro t ht
    exact angularTailPotential_hasDerivAt (hr t ⟨ht.1.le, ht.2.le⟩) hB (hrD t ht)
  have hbound : ∀ t ∈ Ioo a b, |(v t / r t) * Real.sin (ψ t)| ≤ -(G' t) := by
    intro t ht
    dsimp [G']
    rw [neg_neg]
    exact affine_angular_derivative_le_tail (hr t ⟨ht.1.le, ht.2.le⟩)
      (hv t ht) (hcos t ht) (hsin t ht)
  have h := abs_increment_le_of_decreasing_tail_potential hab hφc hGc hφD hGd hbound
  have hGb : 0 ≤ G b := by
    dsimp [G, angularTailPotential]
    have hp : 0 < 1 + B := by linarith
    exact add_nonneg
      (mul_nonneg (div_nonneg (by norm_num) hp.le)
        (div_nonneg (Real.rpow_nonneg hA _) (Real.rpow_nonneg (hr b ⟨hab, le_rfl⟩).le _)))
      (div_nonneg (div_nonneg (mul_nonneg (by norm_num) hD) hB.le) (hr b ⟨hab, le_rfl⟩).le)
  linarith

end RepulsiveCoulomb
