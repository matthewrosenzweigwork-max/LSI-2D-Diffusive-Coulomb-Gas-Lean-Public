module

public import LeanResearch.RepulsiveCoulomb.PointDilationBranchUniform

@[expose] public section

/-! RECORDS-ONLY UNCOMPILED. One pair of unit-Gaussian constants is selected
for each Q, once and for all. Every named weighted constant below uses this
same pair. Exact original full-domain inequalities and Gaussian scaling are
retained; the choices are admissible witnesses, never called optimal. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open PeriodicAttractiveLogGas
open scoped BigOperators
namespace RepulsiveCoulomb

def pointDilationBranchP1 (Q : ℝ) : ℝ :=
  Classical.choose (pointDilationBranch_uniform_full_domain Q)

def pointDilationBranchK1 (Q : ℝ) : ℝ :=
  Classical.choose (Classical.choose_spec (pointDilationBranch_uniform_full_domain Q))

theorem pointDilationBranch_named_spec (Q : ℝ) :
    0 < pointDilationBranchP1 Q ∧ 0 < pointDilationBranchK1 Q ∧
      ∀ (γ : ℝ) (hγ : 0 < γ) (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
        (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
      variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
        (pointDilationBranchP1 Q / γ) * pointFormEnergy hγ ha y u ∧
      entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
        (((pointDilationBranchK1 Q / γ) * pointFormEnergy hγ ha y u : ℝ) : EReal) :=
  Classical.choose_spec (Classical.choose_spec (pointDilationBranch_uniform_full_domain Q))

theorem pointDilationBranchP1_pos (Q : ℝ) : 0 < pointDilationBranchP1 Q :=
  (pointDilationBranch_named_spec Q).1

theorem pointDilationBranchK1_pos (Q : ℝ) : 0 < pointDilationBranchK1 Q :=
  (pointDilationBranch_named_spec Q).2.1

def pointDilationBranchCwt (γ Q : ℝ) : ℝ := pointDilationBranchP1 Q / γ

def pointDilationBranchRhoWt (γ Q : ℝ) : ℝ := 2 * γ / pointDilationBranchK1 Q

theorem pointDilationBranchCwt_pos {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) :
    0 < pointDilationBranchCwt γ Q := div_pos (pointDilationBranchP1_pos Q) hγ

theorem pointDilationBranchRhoWt_pos {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) :
    0 < pointDilationBranchRhoWt γ Q :=
  div_pos (mul_pos (by norm_num) hγ) (pointDilationBranchK1_pos Q)

theorem pointDilationBranchCwt_scaling (γ Q : ℝ) :
    pointDilationBranchCwt γ Q = pointDilationBranchCwt 1 Q / γ := by
  simp only [pointDilationBranchCwt, div_one]

theorem pointDilationBranchRhoWt_scaling (γ Q : ℝ) :
    pointDilationBranchRhoWt γ Q = γ * pointDilationBranchRhoWt 1 Q := by
  unfold pointDilationBranchRhoWt
  ring

theorem pointDilationBranch_two_div_RhoWt {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) :
    2 / pointDilationBranchRhoWt γ Q = pointDilationBranchK1 Q / γ := by
  unfold pointDilationBranchRhoWt
  field_simp [hγ.ne', (pointDilationBranchK1_pos Q).ne'] <;> ring

theorem pointDilationBranch_named_weighted_inequalities (Q : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (u : PointFormDomain hγ ha y) :
    variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
      pointDilationBranchCwt γ Q * pointFormEnergy hγ ha y u ∧
    entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
      (((2 / pointDilationBranchRhoWt γ Q) * pointFormEnergy hγ ha y u : ℝ) : EReal) := by
  rw [pointDilationBranch_two_div_RhoWt hγ Q]
  exact (pointDilationBranch_named_spec Q).2.2 γ hγ m a ha y hQ u

theorem pointDilationBranch_named_core (Q : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    variance (φ : ℂ → ℝ) (pointMeasure γ a y) ≤
      (pointDilationBranchP1 Q / γ) * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) ∧
    entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
      (((pointDilationBranchK1 Q / γ) *
        (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  have h := (pointDilationBranch_named_spec Q).2.2 γ hγ m a ha y hQ (pointFormCore hγ ha y φ)
  have hsq : (fun x => (pointFormValueL hγ ha y (pointFormCore hγ ha y φ) x) ^ 2)
      =ᵐ[pointMeasure γ a y] (fun x => φ x ^ 2) := by
    filter_upwards [pointFormCore_value hγ ha y φ] with x hx
    rw [hx]
  rw [pointFormCore_variance, pointFormCore_energy_eq_integral, entropy_congr_ae hsq] at h
  exact h

theorem pointDilationBranch_named_full_above (Q : ℝ) {γ₀ γ : ℝ}
    (hγ₀ : 0 < γ₀) (hγ : 0 < γ) (hγle : γ₀ ≤ γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (u : PointFormDomain hγ ha y) :
    variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
      pointDilationBranchCwt γ₀ Q * pointFormEnergy hγ ha y u ∧
    entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
      (((2 / pointDilationBranchRhoWt γ₀ Q) * pointFormEnergy hγ ha y u : ℝ) : EReal) := by
  obtain ⟨hp, hk⟩ := (pointDilationBranch_named_spec Q).2.2 γ hγ m a ha y hQ u
  have hE := pointFormEnergy_nonneg hγ ha y u
  have hP := div_le_div_of_nonneg_left (pointDilationBranchP1_pos Q).le hγ₀ hγle
  have hK := div_le_div_of_nonneg_left (pointDilationBranchK1_pos Q).le hγ₀ hγle
  refine ⟨hp.trans (mul_le_mul_of_nonneg_right hP hE), ?_⟩
  rw [pointDilationBranch_two_div_RhoWt hγ₀ Q]
  exact hk.trans (by exact_mod_cast mul_le_mul_of_nonneg_right hK hE)


theorem pointDilationBranch_named_core_above (Q : ℝ) {γ₀ γ : ℝ}
    (hγ₀ : 0 < γ₀) (hγ : 0 < γ) (hγle : γ₀ ≤ γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    variance (φ : ℂ → ℝ) (pointMeasure γ a y) ≤
      pointDilationBranchCwt γ₀ Q * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) ∧
    entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
      (((pointDilationBranchK1 Q / γ₀) *
        (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  have h := pointDilationBranch_named_full_above Q hγ₀ hγ hγle m a ha y hQ (pointFormCore hγ ha y φ)
  have hsq : (fun x => (pointFormValueL hγ ha y (pointFormCore hγ ha y φ) x) ^ 2)
      =ᵐ[pointMeasure γ a y] (fun x => φ x ^ 2) := by
    filter_upwards [pointFormCore_value hγ ha y φ] with x hx
    rw [hx]
  rw [pointFormCore_variance, pointFormCore_energy_eq_integral,
    pointDilationBranch_two_div_RhoWt hγ₀ Q, entropy_congr_ae hsq] at h
  exact h

end RepulsiveCoulomb
