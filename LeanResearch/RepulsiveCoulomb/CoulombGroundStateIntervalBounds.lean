module

public import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCoreBounds

@[expose] public section

/-! RECORDS-ONLY UNCHECKED DRAFT. Uniform ground-state bounds for a compact
positive temperature interval, on the actual original smooth core. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombGroundStateShift_mono (N : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    coulombGroundStateShift N a ≤ coulombGroundStateShift N b := by
  have hb : 0 ≤ b := ha.trans hab
  have hlinear : (N : ℝ) * a ≤ (N : ℝ) * b :=
    mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg N)
  have hdiv : a / (N : ℝ) ≤ b / (N : ℝ) :=
    div_le_div_of_nonneg_right hab (Nat.cast_nonneg N)
  have hquad : a * (a / (N : ℝ)) ≤ b * (b / (N : ℝ)) :=
    mul_le_mul hab hdiv (by positivity) hb
  have hterm := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hquad
      (show 0 ≤ ((coulombPairs N).card : ℝ) by positivity))
    (show (0 : ℝ) ≤ 2 by norm_num)
  exact add_le_add hlinear hterm

theorem coulombGroundStateBallBound_mono (N : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (R : ℝ) :
    coulombGroundStateBallBound N a R ≤ coulombGroundStateBallBound N b R := by
  exact mul_le_mul_of_nonneg_right
    (show coulombGroundStateShift N a + 1 ≤ coulombGroundStateShift N b + 1 by
      linarith [coulombGroundStateShift_mono N ha hab]) (sq_nonneg _)

theorem coulombGroundState_core_interval_bounds {N : ℕ} {a b β : ℝ}
    (ha : 0 < a) (hβa : a ≤ β) (hβb : β ≤ b) (R : ℝ)
    (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (hφ : ‖coulombFormCore (ha.trans_le hβa) φ‖ ≤ R) :
    (∫ z : CoulombConfig N, (coulombGroundStateCore (ha.trans_le hβa) φ z) ^ 2) ≤
      coulombGroundStateBallBound N b R ∧
    (∫ z : CoulombConfig N, ‖gradient
      (coulombGroundStateCore (ha.trans_le hβa) φ : CoulombConfig N → ℝ) z‖ ^ 2) ≤
      coulombGroundStateBallBound N b R ∧
    (∫ z : CoulombConfig N, ‖z‖ ^ 2 *
      (coulombGroundStateCore (ha.trans_le hβa) φ z) ^ 2) ≤
      4 * coulombGroundStateBallBound N b R / a ^ 2 := by
  have hβ : 0 < β := ha.trans_le hβa
  have hb := coulombGroundState_core_three_bounds hβ R φ hφ
  have hA := coulombGroundStateBallBound_mono N hβ.le hβb R
  refine ⟨hb.1.trans hA, hb.2.1.trans hA, hb.2.2.trans ?_⟩
  have hpos := coulombGroundStateBallBound_pos N (hβ.trans_le hβb) R
  apply div_le_div₀ (by positivity : 0 ≤ 4 * coulombGroundStateBallBound N b R)
    (mul_le_mul_of_nonneg_left hA (by norm_num)) (sq_pos_of_pos ha)
  nlinarith [sq_nonneg (β - a)]

end RepulsiveCoulomb
