module

public import LeanResearch.RepulsiveCoulomb.EquilibriumBranchExtendedIntegral

@[expose] public section

/-! Exact extended-real algebra for the nonnegative free-energy decomposition.
Both entropy and positive interaction may independently be infinite. The
finite normalization constant is retained, and no infinity-minus-infinity
operation is introduced by the identity. -/
noncomputable section
open scoped ENNReal
namespace RepulsiveCoulomb

/-- The exact beta/4 Gaussian decomposition, including every infinite branch. -/
theorem equilibriumFreeEnergy_extended_algebra {β : ℝ} (hβ : 0 < β)
    (A B : ℝ≥0∞) (r l c : ℝ) :
    ((r / 2 : ℝ) : EReal) + ((1 / 2 : ℝ) : EReal) * ((B : EReal) - ((2 * l : ℝ) : EReal)) +
      ((β⁻¹ : ℝ) : EReal) * ((A : EReal) - ((β / 4 * r - c : ℝ) : EReal)) =
    ((β⁻¹ : ℝ) : EReal) * (A : EReal) + ((1 / 2 : ℝ) : EReal) * (B : EReal) +
      ((r / 4 - l + 1 : ℝ) : EReal) - ((1 : ℝ) : EReal) + ((c / β : ℝ) : EReal) := by
  have hi : 0 < β⁻¹ := inv_pos.mpr hβ
  have hh : (0 : ℝ) < 1 / 2 := by norm_num
  by_cases hA : A = ∞
  · by_cases hB : B = ∞
    · subst A
      subst B
      simp only [EReal.coe_ennreal_top, EReal.top_sub_coe,
        EReal.coe_mul_top_of_pos hi, EReal.coe_mul_top_of_pos hh,
        EReal.coe_add_top, EReal.top_add_top, EReal.top_add_coe]
    · rw [hA, ← EReal.coe_ennreal_toReal hB]
      simp only [EReal.coe_ennreal_top, EReal.top_sub_coe,
        EReal.coe_mul_top_of_pos hi, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_add_top, EReal.top_add_coe]
  · by_cases hB : B = ∞
    · rw [hB, ← EReal.coe_ennreal_toReal hA]
      simp only [EReal.coe_ennreal_top, EReal.top_sub_coe,
        EReal.coe_mul_top_of_pos hh, ← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add,
        EReal.coe_add_top, EReal.top_add_coe]
    · rw [← EReal.coe_ennreal_toReal hA, ← EReal.coe_ennreal_toReal hB]
      simp only [← EReal.coe_sub, ← EReal.coe_mul, ← EReal.coe_add]
      congr 1
      field_simp [hβ.ne'] <;> ring

end RepulsiveCoulomb
