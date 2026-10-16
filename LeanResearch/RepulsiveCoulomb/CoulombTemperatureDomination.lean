module

public import LeanResearch.RepulsiveCoulomb.CoulombPotentialWeight
public import LeanResearch.RepulsiveCoulomb.LabeledCoulombNormalization

@[expose] public section

/-! A single integrable Gaussian majorant on any positive compact temperature
interval. The constants may depend on particle number and the interval. -/
noncomputable section
open Set MeasureTheory Filter
namespace RepulsiveCoulomb

theorem coulombRadialExponent_nonneg (N : ℕ) {β : ℝ} (hβ : 0 ≤ β) :
    0 ≤ coulombRadialExponent N β := by
  unfold coulombRadialExponent
  exact Finset.sum_nonneg fun p hp => by positivity

theorem coulombRadialExponent_mono (N : ℕ) {β γ : ℝ} (h : β ≤ γ) :
    coulombRadialExponent N β ≤ coulombRadialExponent N γ := by
  unfold coulombRadialExponent
  apply Finset.sum_le_sum
  intro p hp
  exact mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h (Nat.cast_nonneg N)) (by norm_num)

def coulombTemperatureMajorant (N : ℕ) (a b : ℝ) (z : CoulombConfig N) : ℝ :=
  Real.exp ((coulombRadialExponent N b) ^ 2 / a) * Real.exp (-(a / 4) * ‖z‖ ^ 2)

theorem coulombTemperatureMajorant_integrable (N : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Integrable (coulombTemperatureMajorant N a b) :=
  (integrable_coulomb_gaussian N (by positivity : 0 < a / 4)).const_mul _

theorem coulombWeight_le_temperatureMajorant {N : ℕ} {a b β : ℝ}
    (ha : 0 < a) (hlo : a ≤ β) (hhi : β ≤ b) (z : CoulombConfig N) :
    coulombWeight β z ≤ coulombTemperatureMajorant N a b z := by
  have hβ : 0 < β := ha.trans_le hlo
  have hexp : (coulombRadialExponent N β) ^ 2 / β ≤
      (coulombRadialExponent N b) ^ 2 / a := by
    have hsq : (coulombRadialExponent N β) ^ 2 ≤ (coulombRadialExponent N b) ^ 2 := by
      nlinarith [coulombRadialExponent_nonneg N hβ.le, coulombRadialExponent_mono N hhi]
    exact (div_le_div_of_nonneg_right hsq hβ.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg _) ha hlo)
  have hgauss : Real.exp (-(β / 4) * ‖z‖ ^ 2) ≤ Real.exp (-(a / 4) * ‖z‖ ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ‖z‖]
  exact (coulombWeight_le_gaussian hβ z).trans
    (mul_le_mul (Real.exp_le_exp.mpr hexp) hgauss (Real.exp_pos _).le (Real.exp_pos _).le)

end RepulsiveCoulomb
