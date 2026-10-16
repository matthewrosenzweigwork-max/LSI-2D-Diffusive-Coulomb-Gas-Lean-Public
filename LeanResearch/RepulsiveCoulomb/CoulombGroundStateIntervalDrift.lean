import LeanResearch.RepulsiveCoulomb.CoulombGroundStateTemperature
import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCoercivity
import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals

/-! RECORDS-ONLY UNCHECKED DRAFT. A common drift-energy bound for original
core ground states on a positive compact temperature interval. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombGroundState_core_interval_drift {N : ℕ} {a b β : ℝ}
    (ha : 0 < a) (hβa : a ≤ β) (hβb : β ≤ b) (R : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (hφ : ‖coulombFormCore (ha.trans_le hβa) φ‖ ≤ R) :
    (∫ z : CoulombConfig N, ‖gradient (coulombPotential (1 : ℝ)) z‖ ^ 2 *
      (coulombGroundStateCore (ha.trans_le hβa) φ z) ^ 2) ≤
      4 * (1 + (N : ℝ) * b) * (|R| + 1) ^ 2 / a ^ 2 := by
  have hβ : 0 < β := ha.trans_le hβa
  have hb : 0 < b := hβ.trans_le hβb
  have h := coulombInverseGroundState_drift_energy_bound hβ (coulombGroundStateCore hβ φ)
  rw [coulombInverseGroundState_core, coulombGroundState_mass_identity] at h
  have hn := coulombFormCore_norm_sq_eq_integrals hβ φ
  have hm0 : 0 ≤ ∫ z, φ z ^ 2 ∂coulombMeasure N β := integral_nonneg fun z => sq_nonneg _
  have he0 : 0 ≤ ∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2
      ∂coulombMeasure N β := integral_nonneg fun z => sq_nonneg _
  have hnB : ‖coulombFormCore hβ φ‖ ^ 2 ≤ (|R| + 1) ^ 2 := by
    nlinarith [norm_nonneg (coulombFormCore hβ φ), le_abs_self R, abs_nonneg R]
  have hm : (∫ z, φ z ^ 2 ∂coulombMeasure N β) ≤ (|R| + 1) ^ 2 := by
    linarith only [hn, hnB, he0]
  have he : (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2
      ∂coulombMeasure N β) ≤ (|R| + 1) ^ 2 := by
    linarith only [hn, hnB, hm0]
  have hp := mul_le_mul_of_nonneg_left (mul_le_mul hβb hm hm0 hb.le) (Nat.cast_nonneg N)
  have hnum : 4 * ((∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2
      ∂coulombMeasure N β) + (N : ℝ) * β * (∫ z, φ z ^ 2 ∂coulombMeasure N β)) ≤
      4 * (1 + (N : ℝ) * b) * (|R| + 1) ^ 2 := by
    nlinarith only [he, hp]
  exact h.trans (div_le_div₀ (by positivity) hnum (sq_pos_of_pos ha)
    (by nlinarith [sq_nonneg (β - a)]))

end RepulsiveCoulomb
