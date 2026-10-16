import LeanResearch.RepulsiveCoulomb.PointAffineAngularMomentum
import LeanResearch.RepulsiveCoulomb.ScalarTailPotentialComparison
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Tactic

/-! Uncompiled additive successor. The original-time momentum derivative is
bounded by the derivative of D/B*r^B. Scalar comparison gives the uniform sine
estimate without an inverse-radius map or an arclength reparameterization. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem affine_momentum_derivative_le_potential
    {r B D v ψ e : ℝ} (hr : 0 < r) (hB : 0 < B) (hD : 0 ≤ D)
    (hv : 0 ≤ v) (hcos : 0 ≤ Real.cos ψ) (he : |e| ≤ (D / r ^ 2) * v) :
    |-(Real.rpow r (1 + B) * Real.cos ψ * e)| ≤
      (D / B) * ((v * Real.cos ψ) * B * Real.rpow r (B - 1)) := by
  have hpow : r ^ (1 + B) = r ^ (B - 1) * r ^ 2 := by
    rw [show 1 + B = (B - 1) + 2 by ring, Real.rpow_add hr, Real.rpow_two]
  have hp : 0 ≤ Real.rpow r (1 + B) := Real.rpow_nonneg hr.le _
  calc
    |-(Real.rpow r (1 + B) * Real.cos ψ * e)| =
        (Real.rpow r (1 + B) * Real.cos ψ) * |e| := by
      rw [abs_neg, abs_mul, abs_of_nonneg (mul_nonneg hp hcos)]
    _ ≤ (Real.rpow r (1 + B) * Real.cos ψ) * ((D / r ^ 2) * v) :=
      mul_le_mul_of_nonneg_left he (mul_nonneg hp hcos)
    _ = (D / B) * ((v * Real.cos ψ) * B * Real.rpow r (B - 1)) := by
      simp only [Real.rpow_eq_pow]
      rw [hpow]
      field_simp [ne_of_gt hr, ne_of_gt hB] <;> ring

theorem sine_bound_of_affine_radial_tail
    {r ψ v e : ℝ → ℝ} {a b B D : ℝ} (hab : a ≤ b)
    (hB : 0 < B) (hD : 0 ≤ D)
    (hrc : ContinuousOn r (Icc a b)) (hψc : ContinuousOn ψ (Icc a b))
    (hr : ∀ t ∈ Icc a b, 0 < r t)
    (hv : ∀ t ∈ Ioo a b, 0 ≤ v t)
    (hcos : ∀ t ∈ Ioo a b, 0 ≤ Real.cos (ψ t))
    (hrD : ∀ t ∈ Ioo a b, HasDerivAt r (v t * Real.cos (ψ t)) t)
    (hψD : ∀ t ∈ Ioo a b,
      HasDerivAt ψ (-((1 + B) * (v t / r t) * Real.sin (ψ t)) - e t) t)
    (he : ∀ t ∈ Ioo a b, |e t| ≤ (D / (r t) ^ 2) * v t) :
    |Real.sin (ψ b)| ≤
      Real.rpow (r a) (1 + B) / Real.rpow (r b) (1 + B) + D / (B * r b) := by
  let J : ℝ → ℝ := fun t => Real.rpow (r t) (1 + B) * Real.sin (ψ t)
  let H : ℝ → ℝ := fun t => (D / B) * Real.rpow (r t) B
  let J' : ℝ → ℝ := fun t => -(Real.rpow (r t) (1 + B) * Real.cos (ψ t) * e t)
  let H' : ℝ → ℝ := fun t => (D / B) * ((v t * Real.cos (ψ t)) * B * Real.rpow (r t) (B - 1))
  have hJc : ContinuousOn J (Icc a b) :=
    (hrc.rpow_const (fun t ht => Or.inl (ne_of_gt (hr t ht)))).mul
      (Real.continuous_sin.comp_continuousOn hψc)
  have hHc : ContinuousOn H (Icc a b) :=
    continuousOn_const.mul (hrc.rpow_const (fun t ht => Or.inl (ne_of_gt (hr t ht))))
  have hJd : ∀ t ∈ Ioo a b, HasDerivAt J (J' t) t := by
    intro t ht
    exact affine_angularMomentum_hasDerivAt (hr t ⟨ht.1.le, ht.2.le⟩) (hrD t ht) (hψD t ht)
  have hHd : ∀ t ∈ Ioo a b, HasDerivAt H (H' t) t := by
    intro t ht
    exact ((hrD t ht).rpow_const (p := B)
      (Or.inl (ne_of_gt (hr t ⟨ht.1.le, ht.2.le⟩)))).const_mul (D / B)
  have hbound : ∀ t ∈ Ioo a b, |J' t| ≤ H' t := by
    intro t ht
    exact affine_momentum_derivative_le_potential (hr t ⟨ht.1.le, ht.2.le⟩)
      hB hD (hv t ht) (hcos t ht) (he t ht)
  have hcompare := abs_endpoint_le_of_potential_derivative_bound hab hJc hHc hJd hHd hbound
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hpa : 0 < Real.rpow (r a) (1 + B) := Real.rpow_pos_of_pos (hr a ha) _
  have hpb : 0 < Real.rpow (r b) (1 + B) := Real.rpow_pos_of_pos (hr b hb) _
  simp only [Real.rpow_eq_pow] at hpa hpb
  have hJa : |J a| ≤ Real.rpow (r a) (1 + B) := by
    dsimp [J]
    rw [abs_mul, abs_of_pos hpa]
    exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) hpa.le).trans_eq (mul_one _)
  have hJb : |J b| = Real.rpow (r b) (1 + B) * |Real.sin (ψ b)| := by
    dsimp [J]
    rw [abs_mul, abs_of_pos hpb]
  have hHa : 0 ≤ H a :=
    mul_nonneg (div_nonneg hD hB.le) (Real.rpow_nonneg (hr a ha).le _)
  have hraw : Real.rpow (r b) (1 + B) * |Real.sin (ψ b)| ≤
      Real.rpow (r a) (1 + B) + (D / B) * Real.rpow (r b) B := by
    rw [hJb] at hcompare
    dsimp [H] at hcompare hHa
    simp only [Real.rpow_eq_pow] at hJa ⊢
    linarith
  have hquot : |Real.sin (ψ b)| ≤
      (Real.rpow (r a) (1 + B) + (D / B) * Real.rpow (r b) B) /
        Real.rpow (r b) (1 + B) := by
    apply (le_div_iff₀ hpb).mpr
    simpa only [Real.rpow_eq_pow, mul_comm] using hraw
  have hid : (Real.rpow (r a) (1 + B) + (D / B) * Real.rpow (r b) B) /
      Real.rpow (r b) (1 + B) =
      Real.rpow (r a) (1 + B) / Real.rpow (r b) (1 + B) + D / (B * r b) := by
    rw [add_div]
    congr 1
    simp only [Real.rpow_eq_pow]
    have hpB : 0 < (r b) ^ B := Real.rpow_pos_of_pos (hr b hb) _
    rw [show 1 + B = B + 1 by ring, Real.rpow_add (hr b hb), Real.rpow_one]
    field_simp [ne_of_gt hB, ne_of_gt (hr b hb), ne_of_gt hpB] <;> ring
  exact hquot.trans_eq hid

end RepulsiveCoulomb
