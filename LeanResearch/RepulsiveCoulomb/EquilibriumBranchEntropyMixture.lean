import LeanResearch.RepulsiveCoulomb.EquilibriumBranchEntropyNegative

/-! Exact disjoint-support entropy mixtures and the strict one-sided decrease
used to prove positivity of an attained minimizer. The decisive binary-entropy
term is explicit; no infinite derivative or positivity hypothesis is assumed. -/
noncomputable section
open MeasureTheory Real Set Filter
namespace RepulsiveCoulomb

theorem equilibrium_mul_log_scale {t r : ℝ} (ht : 0 < t) (hr : 0 ≤ r) :
    (t * r) * Real.log (t * r) = t * (r * Real.log r) + (t * Real.log t) * r := by
  by_cases hr0 : r = 0
  · simp only [hr0, mul_zero, Real.log_zero, zero_mul, add_zero]
  · rw [Real.log_mul ht.ne' hr0]
    ring

theorem equilibrium_disjoint_entropy_mixture {r s ε : ℝ}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r * s = 0) (hε0 : 0 < ε) (hε1 : ε < 1) :
    ((1 - ε) * r + ε * s) * Real.log ((1 - ε) * r + ε * s) =
      (1 - ε) * (r * Real.log r) + ε * (s * Real.log s) +
        ((1 - ε) * Real.log (1 - ε)) * r + (ε * Real.log ε) * s := by
  rcases mul_eq_zero.mp hrs with hr0 | hs0
  · subst r
    simp only [mul_zero, zero_mul, zero_add, add_zero]
    exact equilibrium_mul_log_scale hε0 hs
  · subst s
    simp only [mul_zero, zero_mul, zero_add, add_zero]
    exact equilibrium_mul_log_scale (sub_pos.mpr hε1) hr

/-- The perturbed entropy is actually integrable on disjoint supports. -/
theorem equilibrium_disjoint_mixture_entropy_integrable {ρ ψ : ℂ → ℝ} {ε : ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hdisj : ∀ᵐ x : ℂ, ρ x * ψ x = 0)
    (hρi : Integrable ρ) (hψi : Integrable ψ)
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hψH : Integrable (fun x : ℂ => ψ x * Real.log (ψ x)))
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    Integrable (fun x : ℂ => ((1 - ε) * ρ x + ε * ψ x) *
      Real.log ((1 - ε) * ρ x + ε * ψ x)) := by
  have hi := (((hρH.const_mul (1 - ε)).add (hψH.const_mul ε)).add
    (hρi.const_mul ((1 - ε) * Real.log (1 - ε)))).add (hψi.const_mul (ε * Real.log ε))
  apply hi.congr
  exact hdisj.mono (fun x hx => (equilibrium_disjoint_entropy_mixture
    (hρ0 x) (hψ0 x) hx hε0 hε1).symm)

/-- Exact entropy identity under the actual planar integral. -/
theorem integral_equilibrium_disjoint_entropy_mixture {ρ ψ : ℂ → ℝ} {ε : ℝ}
    (hρ0 : ∀ x, 0 ≤ ρ x) (hψ0 : ∀ x, 0 ≤ ψ x)
    (hdisj : ∀ᵐ x : ℂ, ρ x * ψ x = 0)
    (hρi : Integrable ρ) (hψi : Integrable ψ)
    (hρmass : (∫ x : ℂ, ρ x) = 1) (hψmass : (∫ x : ℂ, ψ x) = 1)
    (hρH : Integrable (fun x : ℂ => ρ x * Real.log (ρ x)))
    (hψH : Integrable (fun x : ℂ => ψ x * Real.log (ψ x)))
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    (∫ x : ℂ, ((1 - ε) * ρ x + ε * ψ x) * Real.log ((1 - ε) * ρ x + ε * ψ x)) =
      (1 - ε) * (∫ x : ℂ, ρ x * Real.log (ρ x)) +
        ε * (∫ x : ℂ, ψ x * Real.log (ψ x)) +
        (1 - ε) * Real.log (1 - ε) + ε * Real.log ε := by
  have he : (fun x : ℂ => ((1 - ε) * ρ x + ε * ψ x) * Real.log ((1 - ε) * ρ x + ε * ψ x)) =ᵐ[volume]
      (fun x : ℂ => ((1 - ε) * (ρ x * Real.log (ρ x)) + ε * (ψ x * Real.log (ψ x)) +
        ((1 - ε) * Real.log (1 - ε)) * ρ x) + (ε * Real.log ε) * ψ x) :=
    hdisj.mono (fun x hx => equilibrium_disjoint_entropy_mixture (hρ0 x) (hψ0 x) hx hε0 hε1)
  have hi1 := (hρH.const_mul (1 - ε)).add (hψH.const_mul ε)
  have hi2 := hi1.add (hρi.const_mul ((1 - ε) * Real.log (1 - ε)))
  have hs3 := integral_add
    (f := fun x : ℂ => (1 - ε) * (ρ x * Real.log (ρ x)) + ε * (ψ x * Real.log (ψ x)) +
      ((1 - ε) * Real.log (1 - ε)) * ρ x)
    (g := fun x : ℂ => (ε * Real.log ε) * ψ x) hi2 (hψi.const_mul (ε * Real.log ε))
  have hs2 := integral_add
    (f := fun x : ℂ => (1 - ε) * (ρ x * Real.log (ρ x)) + ε * (ψ x * Real.log (ψ x)))
    (g := fun x : ℂ => ((1 - ε) * Real.log (1 - ε)) * ρ x)
    hi1 (hρi.const_mul ((1 - ε) * Real.log (1 - ε)))
  have hs1 := integral_add (hρH.const_mul (1 - ε)) (hψH.const_mul ε)
  rw [integral_congr_ae he, hs3, hs2, hs1]
  simp only [integral_const_mul, hρmass, hψmass, mul_one]

/-- Every finite linear/quadratic energy cost is beaten by the exact binary
entropy gain at an explicit sufficiently small positive exponential scale. -/
theorem equilibrium_binary_entropy_strict_decrease {β : ℝ} (hβ : 0 < β) (B D : ℝ) :
    ∃ ε : ℝ, ε ∈ Ioo 0 1 ∧
      ε * B + ε ^ 2 * D + β⁻¹ * ((1 - ε) * Real.log (1 - ε) + ε * Real.log ε) < 0 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (β * (|B| + |D|) + 1)
  have hn0 : 0 < (n : ℝ) := by
    have hnonneg := mul_nonneg hβ.le (add_nonneg (abs_nonneg B) (abs_nonneg D))
    linarith
  let ε : ℝ := Real.exp (-(n : ℝ))
  have hε0 : 0 < ε := Real.exp_pos _
  have hε1 : ε < 1 := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hn0)
  have hlog : Real.log ε = -(n : ℝ) := Real.log_exp _
  have hbinary : (1 - ε) * Real.log (1 - ε) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sub_pos.mpr hε1).le
      (Real.log_nonpos (by linarith : 0 ≤ 1 - ε) (by linarith : 1 - ε ≤ 1))
  have hlinear := mul_le_mul_of_nonneg_left (le_abs_self B) hε0.le
  have hquad : ε ^ 2 * D ≤ ε * |D| := by
    have hd := mul_le_mul_of_nonneg_left (le_abs_self D) (sq_nonneg ε)
    have hs : ε ^ 2 ≤ ε := by nlinarith
    have h := mul_le_mul_of_nonneg_right hs (abs_nonneg D)
    exact hd.trans h
  have hi : 0 < β⁻¹ := inv_pos.mpr hβ
  have hcoef : |B| + |D| < β⁻¹ * (n : ℝ) := by
    rw [← div_eq_inv_mul, lt_div_iff₀ hβ]
    nlinarith
  have hstrict := mul_neg_of_pos_of_neg hε0 (sub_neg.mpr hcoef)
  have hbin := mul_le_mul_of_nonneg_left hbinary hi.le
  refine ⟨ε, ⟨hε0, hε1⟩, ?_⟩
  rw [hlog]
  nlinarith

end RepulsiveCoulomb
