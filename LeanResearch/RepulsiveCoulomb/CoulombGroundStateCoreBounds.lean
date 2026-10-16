import LeanResearch.RepulsiveCoulomb.CoulombGroundStateCoercivity
import LeanResearch.RepulsiveCoulomb.CoulombFormIntegrals

/-! Simultaneous actual mass, gradient and moment bounds for a form-bounded
family of original-core functions after the normalized ground-state transform. -/
noncomputable section
open Set MeasureTheory Filter InnerProductSpace
namespace RepulsiveCoulomb

def coulombGroundStateBallBound (N : ℕ) (β R : ℝ) : ℝ :=
  (coulombGroundStateShift N β + 1) * (|R| + 1) ^ 2

theorem coulombGroundStateBallBound_pos (N : ℕ) {β : ℝ} (hβ : 0 < β) (R : ℝ) :
    0 < coulombGroundStateBallBound N β R := by
  have hs := coulombGroundStateShift_nonneg N hβ.le
  unfold coulombGroundStateBallBound
  positivity

theorem coulombGroundState_core_combined_bound {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (R : ℝ) (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (hφ : ‖coulombFormCore hβ φ‖ ≤ R) :
    (∫ z : CoulombConfig N, ‖gradient (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) z‖ ^ 2) +
      (β ^ 2 / 4) * (∫ z : CoulombConfig N, ‖z‖ ^ 2 * (coulombGroundStateCore hβ φ z) ^ 2) +
      (∫ z : CoulombConfig N, (coulombGroundStateCore hβ φ z) ^ 2) ≤
      coulombGroundStateBallBound N β R := by
  have hc := coulombGroundState_core_coercivity hβ φ
  have hn := coulombFormCore_norm_sq_eq_integrals hβ φ
  have hs := coulombGroundStateShift_nonneg N hβ.le
  have hm : 0 ≤ ∫ z, φ z ^ 2 ∂coulombMeasure N β := integral_nonneg fun z => sq_nonneg _
  have he : 0 ≤ ∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β :=
    integral_nonneg fun z => sq_nonneg _
  have hnorm : ‖coulombFormCore hβ φ‖ ^ 2 ≤ (|R| + 1) ^ 2 := by
    nlinarith [norm_nonneg (coulombFormCore hβ φ), le_abs_self R, abs_nonneg R]
  have hh : (∫ z, ‖gradient (φ : CoulombConfig N → ℝ) z‖ ^ 2 ∂coulombMeasure N β) +
      (coulombGroundStateShift N β + 1) * (∫ z, φ z ^ 2 ∂coulombMeasure N β) ≤
      (coulombGroundStateShift N β + 1) * ‖coulombFormCore hβ φ‖ ^ 2 := by
    rw [hn]
    nlinarith only [mul_nonneg hs he]
  exact hc.trans (hh.trans (mul_le_mul_of_nonneg_left hnorm (by linarith)))

theorem coulombGroundState_core_three_bounds {N : ℕ} {β : ℝ} (hβ : 0 < β)
    (R : ℝ) (φ : TestFunction (coulombDomain N) ℝ ⊤)
    (hφ : ‖coulombFormCore hβ φ‖ ≤ R) :
    (∫ z : CoulombConfig N, (coulombGroundStateCore hβ φ z) ^ 2) ≤ coulombGroundStateBallBound N β R ∧
    (∫ z : CoulombConfig N, ‖gradient (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) z‖ ^ 2) ≤
      coulombGroundStateBallBound N β R ∧
    (∫ z : CoulombConfig N, ‖z‖ ^ 2 * (coulombGroundStateCore hβ φ z) ^ 2) ≤
      4 * coulombGroundStateBallBound N β R / β ^ 2 := by
  have hc := coulombGroundState_core_combined_bound hβ R φ hφ
  have hm : 0 ≤ ∫ z : CoulombConfig N, (coulombGroundStateCore hβ φ z) ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  have he : 0 ≤ ∫ z : CoulombConfig N,
      ‖gradient (coulombGroundStateCore hβ φ : CoulombConfig N → ℝ) z‖ ^ 2 :=
    integral_nonneg fun z => sq_nonneg _
  have hq : 0 ≤ ∫ z : CoulombConfig N, ‖z‖ ^ 2 * (coulombGroundStateCore hβ φ z) ^ 2 :=
    integral_nonneg fun z => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have ht : 0 ≤ (β ^ 2 / 4) * (∫ z : CoulombConfig N, ‖z‖ ^ 2 * (coulombGroundStateCore hβ φ z) ^ 2) :=
    mul_nonneg (by positivity) hq
  refine ⟨by linarith, by linarith, ?_⟩
  apply (le_div_iff₀ (sq_pos_of_pos hβ)).mpr
  nlinarith only [hc, hm, he]

end RepulsiveCoulomb
