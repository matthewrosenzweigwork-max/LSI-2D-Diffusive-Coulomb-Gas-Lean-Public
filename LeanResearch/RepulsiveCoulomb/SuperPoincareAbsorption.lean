module

public import LeanResearch.RepulsiveCoulomb.SuperPoincareCoefficients

@[expose] public section

/-! Scalar cutoff absorption and the extension from small to all parameters. -/
noncomputable section
namespace RepulsiveCoulomb

theorem spi_cutoff_absorption {M Mg Mh E Eg Eh s D β Z : ℝ}
    (hM : 0 ≤ M) (hs : 0 < s) (hcut : s * D ^ 2 ≤ 1)
    (hsplit : M ≤ 2 * Mg + 2 * Mh)
    (hlocal : Mg ≤ (s / 16) * Eg + β * Z)
    (houter : Mh ≤ (s / 16) * Eh)
    (hpair : Eg + Eh ≤ 2 * E + 4 * D ^ 2 * M) :
    M ≤ (s / 2) * E + 4 * β * Z := by
  have hsum : M ≤ (s / 8) * (Eg + Eh) + 2 * β * Z := by nlinarith only [hsplit, hlocal, houter]
  have henergy := mul_le_mul_of_nonneg_left hpair (show 0 ≤ s / 8 by positivity)
  have hmass := mul_le_mul_of_nonneg_right hcut hM
  nlinarith only [hsum, henergy, hmass]

theorem spi_small_to_all {A B : ℝ} (hA : 0 < A) (hB : 0 < B)
    {M E Z : ℝ} (hE : 0 ≤ E) (hZ : 0 ≤ Z)
    (hsmall : ∀ s : ℝ, 0 < s → s ≤ 1 → M ≤ s * E + A * Real.exp (B / s) * Z)
    {s : ℝ} (hs : 0 < s) :
    M ≤ s * E + (A * Real.exp B) * Real.exp (B / s) * Z := by
  have heB : 1 ≤ Real.exp B := Real.one_le_exp_iff.mpr hB.le
  have heS : 1 ≤ Real.exp (B / s) := Real.one_le_exp_iff.mpr (div_pos hB hs).le
  by_cases hs1 : s ≤ 1
  · have hA' : A ≤ A * Real.exp B := by nlinarith
    exact (hsmall s hs hs1).trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA' (Real.exp_pos _).le) hZ))
  · have h := hsmall 1 zero_lt_one le_rfl
    simp only [one_mul, div_one] at h
    have he := mul_le_mul_of_nonneg_right (show 1 ≤ s by linarith) hE
    have hb := mul_le_mul_of_nonneg_left heS (mul_nonneg hA.le (Real.exp_pos B).le)
    have hz := mul_le_mul_of_nonneg_right hb hZ
    nlinarith only [h, he, hz]

end RepulsiveCoulomb
