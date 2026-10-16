module

public import LeanResearch.RepulsiveCoulomb.PaperRoute.OriginalGaussianLocalGeometry
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianDiskHalfMass
public import LeanResearch.RepulsiveCoulomb.PaperRoute.GaussianDilationRoute
public import LeanResearch.RepulsiveCoulomb.PaperRoute.AtomicFormMoment

@[expose] public section

/-! Additive experimental source. Original finite-point data feed the new
same-map geometry, generic-doubling Sobolev, literal disk/Jensen normalization,
and finite-atomic-maximal confinement producers. Global PI/SPI, the concrete
Wang specialization, entropy closure, Rothaus and Gaussian dilation select
new route-owned constants. Compilation and validation are recorded separately. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
open PeriodicAttractiveLogGas
open scoped BigOperators
namespace RepulsiveCoulomb.PaperRoute

theorem original_weighted_full_domain_of_moment {Q U : ℝ} (hQ0 : 0 ≤ Q)
    (hU : 0 < U) (hMoment : UniformFormMomentBound (by norm_num : (0 : ℝ) < 1) Q U) :
    ∃ P K : ℝ, 0 < P ∧ 0 < K ∧
      ∀ (γ : ℝ) (hγ : 0 < γ) (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
        (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
      variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
        (P / γ) * pointFormEnergy hγ ha y u ∧
      entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
        (((K / γ) * pointFormEnergy hγ ha y u : ℝ) : EReal) := by
  obtain ⟨R₀, hR₀, hHalf⟩ := disk_half_mass_ball (γ := 1) (by norm_num) hQ0
  exact dilation_uniform_full_domain_of_raw_sobolev (originalGaussianKappa_gt_one Q)
    (originalRawSobolevConstant_pos hQ0) (original_uniform_raw_strong_sobolev Q)
    hU hMoment hR₀ hHalf

/-- The original weighted full-domain PI/LSI conclusion, with every local,
half-mass and moment premise discharged by the new paper-route producers. -/
theorem original_weighted_full_domain (Q : ℝ) :
    ∃ P K : ℝ, 0 < P ∧ 0 < K ∧
      ∀ (γ : ℝ) (hγ : 0 < γ) (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
        (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
      variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
        (P / γ) * pointFormEnergy hγ ha y u ∧
      entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
        (((K / γ) * pointFormEnergy hγ ha y u : ℝ) : EReal) := by
  by_cases hQ0 : 0 ≤ Q
  · obtain ⟨U, hU, hMoment⟩ := atomic_pointForm_weighted_moment_bound (γ := 1) (Q := Q) (by norm_num)
    exact original_weighted_full_domain_of_moment hQ0 hU hMoment
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro γ hγ m a ha y hQ u
    exact (hQ0 ((Finset.sum_nonneg (fun j _ => ha j)).trans hQ)).elim

def paperWeightedP1 (Q : ℝ) : ℝ :=
  Classical.choose (original_weighted_full_domain Q)

def paperWeightedK1 (Q : ℝ) : ℝ :=
  Classical.choose (Classical.choose_spec (original_weighted_full_domain Q))

theorem paper_weighted_named_spec (Q : ℝ) :
    0 < paperWeightedP1 Q ∧ 0 < paperWeightedK1 Q ∧
      ∀ (γ : ℝ) (hγ : 0 < γ) (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j)
        (y : Fin m → ℂ), (∑ j, a j ≤ Q) → ∀ u : PointFormDomain hγ ha y,
      variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
        (paperWeightedP1 Q / γ) * pointFormEnergy hγ ha y u ∧
      entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
        (((paperWeightedK1 Q / γ) * pointFormEnergy hγ ha y u : ℝ) : EReal) :=
  Classical.choose_spec (Classical.choose_spec (original_weighted_full_domain Q))

theorem paperWeightedP1_pos (Q : ℝ) : 0 < paperWeightedP1 Q :=
  (paper_weighted_named_spec Q).1

theorem paperWeightedK1_pos (Q : ℝ) : 0 < paperWeightedK1 Q :=
  (paper_weighted_named_spec Q).2.1

def paperCwt (γ Q : ℝ) : ℝ := paperWeightedP1 Q / γ

def paperRhoWt (γ Q : ℝ) : ℝ := 2 * γ / paperWeightedK1 Q

theorem paperCwt_pos {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) :
    0 < paperCwt γ Q := div_pos (paperWeightedP1_pos Q) hγ

theorem paperRhoWt_pos {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) :
    0 < paperRhoWt γ Q :=
  div_pos (mul_pos (by norm_num) hγ) (paperWeightedK1_pos Q)

theorem paperCwt_scaling (γ Q : ℝ) :
    paperCwt γ Q = paperCwt 1 Q / γ := by
  simp only [paperCwt, div_one]

theorem paperRhoWt_scaling (γ Q : ℝ) :
    paperRhoWt γ Q = γ * paperRhoWt 1 Q := by
  unfold paperRhoWt
  ring

theorem paper_two_div_RhoWt {γ : ℝ} (hγ : 0 < γ) (Q : ℝ) :
    2 / paperRhoWt γ Q = paperWeightedK1 Q / γ := by
  unfold paperRhoWt
  field_simp [hγ.ne', (paperWeightedK1_pos Q).ne']

theorem paper_weighted_named_inequalities (Q : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (u : PointFormDomain hγ ha y) :
    variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
      paperCwt γ Q * pointFormEnergy hγ ha y u ∧
    entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
      (((2 / paperRhoWt γ Q) * pointFormEnergy hγ ha y u : ℝ) : EReal) := by
  rw [paper_two_div_RhoWt hγ Q]
  exact (paper_weighted_named_spec Q).2.2 γ hγ m a ha y hQ u

theorem paper_weighted_named_core (Q : ℝ) {γ : ℝ} (hγ : 0 < γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    variance (φ : ℂ → ℝ) (pointMeasure γ a y) ≤
      (paperWeightedP1 Q / γ) * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) ∧
    entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
      (((paperWeightedK1 Q / γ) *
        (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  have h := (paper_weighted_named_spec Q).2.2 γ hγ m a ha y hQ (pointFormCore hγ ha y φ)
  have hsq : (fun x => (pointFormValueL hγ ha y (pointFormCore hγ ha y φ) x) ^ 2)
      =ᵐ[pointMeasure γ a y] (fun x => φ x ^ 2) := by
    filter_upwards [pointFormCore_value hγ ha y φ] with x hx
    rw [hx]
  rw [pointFormCore_variance, pointFormCore_energy_eq_integral, entropy_congr_ae hsq] at h
  exact h

theorem paper_weighted_named_full_above (Q : ℝ) {γ₀ γ : ℝ}
    (hγ₀ : 0 < γ₀) (hγ : 0 < γ) (hγle : γ₀ ≤ γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (u : PointFormDomain hγ ha y) :
    variance (pointFormValueL hγ ha y u : ℂ → ℝ) (pointMeasure γ a y) ≤
      paperCwt γ₀ Q * pointFormEnergy hγ ha y u ∧
    entropy (pointMeasure γ a y) (fun x => (pointFormValueL hγ ha y u x) ^ 2) ≤
      (((2 / paperRhoWt γ₀ Q) * pointFormEnergy hγ ha y u : ℝ) : EReal) := by
  obtain ⟨hp, hk⟩ := (paper_weighted_named_spec Q).2.2 γ hγ m a ha y hQ u
  have hE := pointFormEnergy_nonneg hγ ha y u
  have hP := div_le_div_of_nonneg_left (paperWeightedP1_pos Q).le hγ₀ hγle
  have hK := div_le_div_of_nonneg_left (paperWeightedK1_pos Q).le hγ₀ hγle
  refine ⟨hp.trans (mul_le_mul_of_nonneg_right hP hE), ?_⟩
  rw [paper_two_div_RhoWt hγ₀ Q]
  exact hk.trans (by exact_mod_cast mul_le_mul_of_nonneg_right hK hE)


theorem paper_weighted_named_core_above (Q : ℝ) {γ₀ γ : ℝ}
    (hγ₀ : 0 < γ₀) (hγ : 0 < γ) (hγle : γ₀ ≤ γ)
    (m : ℕ) (a : Fin m → ℝ) (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (hQ : ∑ j, a j ≤ Q) (φ : TestFunction (pointDomain a y) ℝ ⊤) :
    variance (φ : ℂ → ℝ) (pointMeasure γ a y) ≤
      paperCwt γ₀ Q * (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) ∧
    entropy (pointMeasure γ a y) (fun x => φ x ^ 2) ≤
      (((paperWeightedK1 Q / γ₀) *
        (∫ x, ‖gradient (φ : ℂ → ℝ) x‖ ^ 2 ∂pointMeasure γ a y) : ℝ) : EReal) := by
  have h := paper_weighted_named_full_above Q hγ₀ hγ hγle m a ha y hQ (pointFormCore hγ ha y φ)
  have hsq : (fun x => (pointFormValueL hγ ha y (pointFormCore hγ ha y φ) x) ^ 2)
      =ᵐ[pointMeasure γ a y] (fun x => φ x ^ 2) := by
    filter_upwards [pointFormCore_value hγ ha y φ] with x hx
    rw [hx]
  rw [pointFormCore_variance, pointFormCore_energy_eq_integral,
    paper_two_div_RhoWt hγ₀ Q, entropy_congr_ae hsq] at h
  exact h

end RepulsiveCoulomb.PaperRoute
