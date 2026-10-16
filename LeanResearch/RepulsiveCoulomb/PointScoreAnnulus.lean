module

public import LeanResearch.RepulsiveCoulomb.PointWeightScore

@[expose] public section

/-! Actual bad-score annuli and their configuration-uniform area control. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem pointScore_measurable {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) :
    Measurable (pointScore γ a y) := by
  unfold pointScore pointLogForce
  fun_prop

def pointScoreBadAnnulus {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ) (R : ℝ) : Set ℂ :=
  {z | R ≤ ‖z‖ ∧ ‖z‖ < 2 * R ∧ ‖pointScore γ a y z‖ < γ * R / 2}

def pointScoreBadAreaConstant (γ Q : ℝ) : ℝ := 32 * Real.pi * Q ^ 2 / γ ^ 2

theorem pointScoreBadAreaConstant_nonneg (γ Q : ℝ) : 0 ≤ pointScoreBadAreaConstant γ Q := by
  unfold pointScoreBadAreaConstant
  positivity

theorem pointScoreBadAnnulus_measurable {m : ℕ} (γ : ℝ) (a : Fin m → ℝ)
    (y : Fin m → ℂ) (R : ℝ) : MeasurableSet (pointScoreBadAnnulus γ a y R) :=
  (measurableSet_le measurable_const continuous_norm.measurable).inter
    ((measurableSet_lt continuous_norm.measurable measurable_const).inter
      (measurableSet_lt (pointScore_measurable γ a y).norm measurable_const))

theorem pointScoreBadAnnulus_volume_le {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q) :
    volume (pointScoreBadAnnulus γ a y R) ≤ ENNReal.ofReal (pointScoreBadAreaConstant γ Q / R ^ 2) := by
  have hsub : pointScoreBadAnnulus γ a y R ⊆
      {z : ℂ | R ≤ ‖z‖ ∧ ‖pointScore γ a y z‖ < γ * R / 2} := fun z hz => ⟨hz.1, hz.2.2⟩
  have h := (measure_mono hsub).trans (pointScore_small_region_measure hγ hR ha y hQ)
  convert h using 1
  congr 1
  unfold pointScoreBadAreaConstant
  ring

theorem pointScoreBadAnnulus_volume_ne_top {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q) :
    volume (pointScoreBadAnnulus γ a y R) ≠ ⊤ :=
  ((pointScoreBadAnnulus_volume_le hγ hR ha y hQ).trans_lt ENNReal.ofReal_lt_top).ne

theorem pointScoreBadAnnulus_real_volume_le {m : ℕ} {γ Q R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (hQ : ∑ j, a j ≤ Q) :
    volume.real (pointScoreBadAnnulus γ a y R) ≤ pointScoreBadAreaConstant γ Q / R ^ 2 :=
  ENNReal.toReal_le_of_le_ofReal (div_nonneg (pointScoreBadAreaConstant_nonneg γ Q) (sq_nonneg R))
    (pointScoreBadAnnulus_volume_le hγ hR ha y hQ)

theorem pointScore_good_quadratic_bound {m : ℕ} {γ R : ℝ} (hγ : 0 < γ) (hR : 0 < R)
    (a : Fin m → ℝ) (y : Fin m → ℂ) (z : ℂ) (u : ℝ)
    (hscore : γ * R / 2 ≤ ‖pointScore γ a y z‖) :
    R ^ 2 * u ^ 2 ≤ (4 / γ ^ 2) * ‖pointScore γ a y z‖ ^ 2 * u ^ 2 := by
  have hbase : R ^ 2 ≤ (4 / γ ^ 2) * ‖pointScore γ a y z‖ ^ 2 := by
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ (sq_pos_of_pos hγ)).mpr
    have hpos : 0 ≤ γ * R / 2 := by positivity
    nlinarith [sq_nonneg (‖pointScore γ a y z‖ - γ * R / 2)]
  exact mul_le_mul_of_nonneg_right hbase (sq_nonneg u)

end RepulsiveCoulomb
