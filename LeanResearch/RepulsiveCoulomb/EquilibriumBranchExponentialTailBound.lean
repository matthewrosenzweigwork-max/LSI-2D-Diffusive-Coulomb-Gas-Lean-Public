import LeanResearch.RepulsiveCoulomb.EquilibriumBranchNelsonIntegrals

/-! Exponential integration of an actual cutoff and tail probability bound.
This is the analytic layer-cake adapter used after the centered correlation
estimate; it does not postulate a partition bound or treat an unproved moment
hypothesis as the finished partition theorem. -/
noncomputable section
open MeasureTheory Real Set Filter
open scoped ENNReal
namespace RepulsiveCoulomb

theorem equilibrium_exponential_cutoff_tail_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {X : α → ℝ} (hX : Measurable X)
    {A C L q : ℝ} (hC : 0 ≤ C) (hL : 0 ≤ L) (hq : 1 < q)
    (hcut : ∀ᵐ x ∂μ, X x ≤ A)
    (htail : ∀ u : ℝ, 1 ≤ u → μ {x : α | u < X x} ≤ ENNReal.ofReal (C * (L + Real.exp (-q * u)))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (X x)) ∂μ) ≤
      ENNReal.ofReal (Real.exp 1 *
        (1 + C * (L * Real.exp (A - 1) + Real.exp (-q) / (q - 1)))) := by
  let g₁ : ℝ → ℝ≥0∞ := (Iic (A - 1)).indicator (fun s => ENNReal.ofReal (Real.exp s))
  let g₂ : ℝ → ℝ≥0∞ := fun s => ENNReal.ofReal (Real.exp ((1 - q) * s))
  have hg₁ : Measurable g₁ := Real.measurable_exp.ennreal_ofReal.indicator measurableSet_Iic
  have hg₂ : Measurable g₂ := ((measurable_const.mul measurable_id).exp).ennreal_ofReal
  have hpoint (s : ℝ) (hs : s ∈ Ioi 0) :
      μ {x : α | s + 1 < X x} * ENNReal.ofReal (Real.exp s) ≤
        ENNReal.ofReal C * (ENNReal.ofReal L * g₁ s + ENNReal.ofReal (Real.exp (-q)) * g₂ s) := by
    change (0 : ℝ) < s at hs
    by_cases hsd : s ≤ A - 1
    · have h := mul_le_mul_left (htail (s + 1) (by linarith)) (ENNReal.ofReal (Real.exp s))
      rw [ENNReal.ofReal_mul hC, ENNReal.ofReal_add hL (Real.exp_pos _).le] at h
      have he : ENNReal.ofReal (Real.exp (-q * (s + 1))) * ENNReal.ofReal (Real.exp s) =
          ENNReal.ofReal (Real.exp (-q)) * ENNReal.ofReal (Real.exp ((1 - q) * s)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (Real.exp_pos _).le]
        congr 1
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      dsimp only [g₁, g₂]
      have hsdSet : s ∈ Iic (A - 1) := hsd
      rw [indicator_of_mem hsdSet]
      apply h.trans_eq
      calc
        ENNReal.ofReal C * (ENNReal.ofReal L + ENNReal.ofReal (Real.exp (-q * (s + 1)))) *
            ENNReal.ofReal (Real.exp s) =
          ENNReal.ofReal C * (ENNReal.ofReal L * ENNReal.ofReal (Real.exp s) +
            ENNReal.ofReal (Real.exp (-q * (s + 1))) * ENNReal.ofReal (Real.exp s)) := by ring
        _ = _ := by rw [he]
    · have hzero : μ {x : α | s + 1 < X x} = 0 := by
        have hn : ∀ᵐ x ∂μ, ¬ s + 1 < X x := hcut.mono (fun x hx => by linarith)
        rw [ae_iff] at hn
        simpa only [not_not] using hn
      rw [hzero, zero_mul]
      exact bot_le
  have hi := setLIntegral_mono' (μ := (volume : Measure ℝ)) measurableSet_Ioi hpoint
  rw [lintegral_const_mul (ENNReal.ofReal C)
    (f := fun s => ENNReal.ofReal L * g₁ s + ENNReal.ofReal (Real.exp (-q)) * g₂ s)
    ((measurable_const.mul hg₁).add (measurable_const.mul hg₂)),
    lintegral_add_left (f := fun s => ENNReal.ofReal L * g₁ s) (measurable_const.mul hg₁),
    lintegral_const_mul (ENNReal.ofReal L) hg₁,
    lintegral_const_mul (ENNReal.ofReal (Real.exp (-q))) hg₂] at hi
  have h₁ : (∫⁻ s : ℝ in Ioi 0, g₁ s) ≤ ENNReal.ofReal (Real.exp (A - 1)) :=
    equilibrium_lintegral_truncated_exp_le (A - 1)
  have h₂ : (∫⁻ s : ℝ in Ioi 0, g₂ s) = ENNReal.ofReal (1 / (q - 1)) :=
    equilibrium_lintegral_exp_decay hq
  rw [h₂] at hi
  have htailIntegral : (∫⁻ s : ℝ in Ioi 0,
      μ {x : α | s + 1 < X x} * ENNReal.ofReal (Real.exp s)) ≤
      ENNReal.ofReal C * (ENNReal.ofReal L * ENNReal.ofReal (Real.exp (A - 1)) +
        ENNReal.ofReal (Real.exp (-q)) * ENNReal.ofReal (1 / (q - 1))) :=
    hi.trans (mul_le_mul_right (add_le_add (mul_le_mul_right h₁ (ENNReal.ofReal L)) le_rfl) (ENNReal.ofReal C))
  have h := (equilibrium_exponential_layercake_le hX).trans
    (mul_le_mul_right (add_le_add le_rfl htailIntegral) (ENNReal.ofReal (Real.exp 1)))
  have hq0 : 0 < q - 1 := by linarith
  have hprod₁ : 0 ≤ L * Real.exp (A - 1) := mul_nonneg hL (Real.exp_pos _).le
  have hprod₂ : 0 ≤ Real.exp (-q) * (1 / (q - 1)) :=
    mul_nonneg (Real.exp_pos _).le (div_nonneg zero_le_one hq0.le)
  have hcomb : 0 ≤ C * (L * Real.exp (A - 1) + Real.exp (-q) * (1 / (q - 1))) :=
    mul_nonneg hC (add_nonneg hprod₁ hprod₂)
  apply h.trans_eq
  rw [← ENNReal.ofReal_mul hL, ← ENNReal.ofReal_mul (Real.exp_pos (-q)).le,
    ← ENNReal.ofReal_add hprod₁ hprod₂, ← ENNReal.ofReal_mul hC,
    ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one hcomb,
    ← ENNReal.ofReal_mul (Real.exp_pos 1).le]
  congr 1
  ring

/-- Uniform exponential integrability from the actual log-N cutoff and the
moment-derived tail shape. Every constant is explicit and independent of n. -/
theorem equilibrium_exponential_log_cutoff_bound {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsProbabilityMeasure μ] {X : α → ℝ} (hX : Measurable X)
    {n a r b q C : ℝ} (hn : 1 ≤ n) (har : a ≤ r) (hq : 1 < q) (hC : 0 ≤ C)
    (hcut : ∀ᵐ x ∂μ, X x ≤ a * Real.log n + b)
    (htail : ∀ u : ℝ, 1 ≤ u → μ {x : α | u < X x} ≤
      ENNReal.ofReal (C * (n ^ (-r) + Real.exp (-q * u)))) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (X x)) ∂μ) ≤
      ENNReal.ofReal (Real.exp 1 + C * Real.exp b + C / (q - 1)) := by
  have hL : 0 ≤ n ^ (-r) := Real.rpow_nonneg (by linarith) _
  exact (equilibrium_exponential_cutoff_tail_bound hX hC hL hq hcut htail).trans
    (ENNReal.ofReal_le_ofReal (equilibrium_nelson_integrated_constant hn har hq hC))

end RepulsiveCoulomb
