module

public import LeanResearch.RepulsiveCoulomb.CoulombCoordinateSplit

@[expose] public section

/-! Jointly measurable actual point measures and nonnegative integral formulae. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal BigOperators
namespace RepulsiveCoulomb

theorem pointWeight_joint_continuous {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) :
    Continuous (fun p : CoulombConfig m × ℂ => pointWeight γ a (fun j => p.1 j) p.2) := by
  unfold pointWeight
  apply Continuous.mul
  · fun_prop
  · apply continuous_finsetProd
    intro j hj
    exact (Real.continuous_rpow_const (ha j)).comp
      ((continuous_snd.sub ((coulombCoordinate j).continuous.comp continuous_fst)).norm)

theorem pointPartition_measurable_config {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) :
    Measurable (fun y : CoulombConfig m => pointPartition γ a (fun j => y j)) := by
  exact ((pointWeight_joint_continuous γ ha).measurable.ennreal_ofReal).lintegral_prod_right'

theorem pointMeasure_lintegral {m : ℕ} (γ : ℝ) (a : Fin m → ℝ) (y : Fin m → ℂ)
    {F : ℂ → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ w, F w ∂pointMeasure γ a y) = (pointPartition γ a y)⁻¹ *
      ∫⁻ w, ENNReal.ofReal (pointWeight γ a y w) * F w := by
  rw [pointMeasure, lintegral_smul_measure,
    lintegral_withDensity_eq_lintegral_mul volume (pointWeight_measurable γ a y).ennreal_ofReal hF]
  rfl

theorem pointMeasure_lintegral_parameter {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) {F : CoulombConfig m × ℂ → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun y : CoulombConfig m => ∫⁻ w, F (y, w) ∂pointMeasure γ a (fun j => y j)) := by
  have he : (fun y : CoulombConfig m => ∫⁻ w, F (y, w) ∂pointMeasure γ a (fun j => y j)) =
      fun y => (pointPartition γ a (fun j => y j))⁻¹ *
        ∫⁻ w, ENNReal.ofReal (pointWeight γ a (fun j => y j) w) * F (y, w) := by
    funext y
    exact pointMeasure_lintegral γ a (fun j => y j) (hF.comp measurable_prodMk_left)
  rw [he]
  exact (pointPartition_measurable_config γ ha).inv.mul
    (((pointWeight_joint_continuous γ ha).measurable.ennreal_ofReal.mul hF).lintegral_prod_right')

theorem pointMeasure_measurable_config {m : ℕ} (γ : ℝ) {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) :
    Measurable (fun y : CoulombConfig m => pointMeasure γ a (fun j => y j)) := by
  have he : (fun y : CoulombConfig m => pointMeasure γ a (fun j => y j)) =
      fun y => volume.withDensity (fun w : ℂ =>
        (pointPartition γ a (fun j => y j))⁻¹ * ENNReal.ofReal (pointWeight γ a (fun j => y j) w)) := by
    funext y
    rw [pointMeasure, ← withDensity_smul _ (pointWeight_measurable γ a (fun j => y j)).ennreal_ofReal]
    rfl
  rw [he]
  apply measurable_withDensity
  exact ((pointPartition_measurable_config γ ha).inv.comp measurable_fst).mul
    (pointWeight_joint_continuous γ ha).measurable.ennreal_ofReal

theorem coulombWeightAtExponent_nonneg {N : ℕ} (γ α : ℝ) (z : CoulombConfig N) :
    0 ≤ coulombWeightAtExponent γ α z :=
  mul_nonneg (Real.exp_pos _).le (Finset.prod_nonneg (fun p _ => Real.rpow_nonneg (norm_nonneg _) _))

theorem coulombWeightAtExponent_continuous {N : ℕ} (γ : ℝ) {α : ℝ} (hα : 0 ≤ α) :
    Continuous (coulombWeightAtExponent (N := N) γ α) := by
  unfold coulombWeightAtExponent coulombInteraction
  apply Continuous.mul
  · fun_prop
  · apply continuous_finsetProd
    intro p hp
    exact (Real.continuous_rpow_const hα).comp
      (((coulombCoordinate p.1).continuous.sub (coulombCoordinate p.2).continuous).norm)

end RepulsiveCoulomb
