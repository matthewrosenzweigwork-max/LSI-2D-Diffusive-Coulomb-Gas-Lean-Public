module

public import LeanResearch.RepulsiveCoulomb.CoulombCenterRelativePositiveEntropy

@[expose] public section

/-! The native full-relative-domain optimum is finite for every N≥2, proved
using the actual positive-entropy core witness. The REAL supremum is only used
after its nonempty boundedness proof, and is identified with the extended one. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RepulsiveCoulomb

variable {n : ℕ}

def coulombCenterRelativeOptimalRateReal (e : CoulombCenterRotation n)
    (he : CoulombCenterAxis e) {β : ℝ} (hβ : 0 < β) : ℝ :=
  sSup (coulombCenterRelativeRates e he hβ)

theorem coulombCenterRelativeOptimalRateReal_nonneg (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) : 0 ≤ coulombCenterRelativeOptimalRateReal e he hβ :=
  le_csSup (coulombCenterRelativeRates_bddAbove m e he hβ) (Or.inl rfl)

theorem coulombCenterRelativeOptimalRate_lt_top (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) : coulombCenterRelativeOptimalRate e he hβ < ∞ := by
  obtain ⟨B, hB⟩ := coulombCenterRelativeRates_bddAbove m e he hβ
  have hb : coulombCenterRelativeOptimalRate e he hβ ≤ ENNReal.ofReal B := by
    apply sSup_le
    rintro x ⟨r, hr, rfl⟩
    exact ENNReal.ofReal_le_ofReal (hB hr)
  exact hb.trans_lt ENNReal.ofReal_lt_top

/-- Exact identification of the extended optimum with the genuine finite real
supremum, retaining the original closed-domain admissible set. -/
theorem coulombCenterRelativeOptimalRate_eq_ofReal (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) :
    coulombCenterRelativeOptimalRate e he hβ =
      ENNReal.ofReal (coulombCenterRelativeOptimalRateReal e he hβ) := by
  have hb := coulombCenterRelativeRates_bddAbove m e he hβ
  apply le_antisymm
  · apply sSup_le
    rintro x ⟨r, hr, rfl⟩
    exact ENNReal.ofReal_le_ofReal (le_csSup hb hr)
  · apply ENNReal.ofReal_le_of_le_toReal
    apply csSup_le (show (coulombCenterRelativeRates e he hβ).Nonempty from ⟨0, Or.inl rfl⟩)
    intro r hr
    have h := ENNReal.toReal_mono (coulombCenterRelativeOptimalRate_lt_top m e he hβ).ne
      (show ENNReal.ofReal r ≤ coulombCenterRelativeOptimalRate e he hβ from le_sSup ⟨r, hr, rfl⟩)
    simpa only [ENNReal.toReal_ofReal (coulombCenterRelativeRates_nonneg e he hβ hr)] using h

theorem coulombCenterRelativeOptimalRate_toReal (m : ℕ)
    (e : CoulombCenterRotation (m + 1)) (he : CoulombCenterAxis e)
    {β : ℝ} (hβ : 0 < β) :
    (coulombCenterRelativeOptimalRate e he hβ).toReal =
      coulombCenterRelativeOptimalRateReal e he hβ := by
  rw [coulombCenterRelativeOptimalRate_eq_ofReal m e he hβ,
    ENNReal.toReal_ofReal (coulombCenterRelativeOptimalRateReal_nonneg m e he hβ)]

end RepulsiveCoulomb
