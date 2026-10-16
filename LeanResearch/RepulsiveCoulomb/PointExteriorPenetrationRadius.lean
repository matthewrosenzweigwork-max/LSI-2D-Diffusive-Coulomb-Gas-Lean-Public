import LeanResearch.RepulsiveCoulomb.PointGeodesicFixedDiskPenetration
import Mathlib.Tactic

/-! Uncompiled additive successor. An explicit finite-configuration radius
satisfies every quantitative visibility threshold. The final theorem chooses
this one fixed disk for all actual minimizing segments with opposite endpoints. -/
noncomputable section
open Set
open scoped BigOperators
namespace RepulsiveCoulomb

def pointExteriorPenetrationRadius {n : ℕ} (a : Fin n → ℝ) (y : Fin n → ℂ) : ℝ :=
  1 + 2 * ∑ j, ‖y j‖ + pointExteriorMoment a y / (1 + pointExteriorHalfMass a) +
    (2 * pointExteriorMoment a y) / (Real.pi * pointExteriorHalfMass a)

theorem pointExteriorPenetrationRadius_bounds
    {n : ℕ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin n → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    let A := pointExteriorPenetrationRadius a y
    0 < A ∧ (∀ j, 2 * ‖y j‖ ≤ A) ∧
      pointExteriorMoment a y < (1 + pointExteriorHalfMass a) * A ∧
      2 * (pointExteriorMoment a y / A) < Real.pi * pointExteriorHalfMass a := by
  let B := pointExteriorHalfMass a
  let D := pointExteriorMoment a y
  let Y := ∑ j, ‖y j‖
  let A := pointExteriorPenetrationRadius a y
  have hD : 0 ≤ D := pointExteriorMoment_nonneg ha y
  have hY : 0 ≤ Y := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hp : 0 < 1 + B := by dsimp [B]; linarith
  have hπB : 0 < Real.pi * B := mul_pos Real.pi_pos hB
  have hq : 0 ≤ D / (1 + B) := div_nonneg hD hp.le
  have hr : 0 ≤ (2 * D) / (Real.pi * B) := div_nonneg (mul_nonneg (by norm_num) hD) hπB.le
  have hAeq : A = 1 + 2 * Y + D / (1 + B) + (2 * D) / (Real.pi * B) := rfl
  have hA : 0 < A := by rw [hAeq]; linarith
  have hyA : ∀ j, 2 * ‖y j‖ ≤ A := by
    intro j
    have hj : ‖y j‖ ≤ Y :=
      Finset.single_le_sum (fun k _ => norm_nonneg (y k)) (Finset.mem_univ j)
    rw [hAeq]
    linarith
  have hDA : D / (1 + B) < A := by rw [hAeq]; linarith
  have hDthreshold : D < (1 + B) * A := by
    have h := (div_lt_iff₀ hp).mp hDA
    nlinarith
  have hRA : (2 * D) / (Real.pi * B) < A := by rw [hAeq]; linarith
  have hgap : 2 * (D / A) < Real.pi * B := by
    rw [← mul_div_assoc]
    apply (div_lt_iff₀ hA).mpr
    have h := (div_lt_iff₀ hπB).mp hRA
    nlinarith
  exact ⟨hA, hyA, hDthreshold, hgap⟩

theorem exists_pointConformal_opposite_penetration_radius
    {n : ℕ} {a : Fin n → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin n → ℂ)
    (hB : 0 < pointExteriorHalfMass a) :
    ∃ A : ℝ, 0 < A ∧ ∀ (γ : ℝ → ℂ), Continuous γ → ∀ L : ℝ, 0 < L →
      (∀ s ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        (pointSmoothConformalEDist a y (γ s) (γ u)).toReal = |u - s| * L) →
      γ 1 = -γ 0 → ∃ t ∈ Icc (0 : ℝ) 1, ‖γ t‖ ≤ A := by
  obtain ⟨hA, hyA, hD, hgap⟩ := pointExteriorPenetrationRadius_bounds ha y hB
  refine ⟨pointExteriorPenetrationRadius a y, hA, ?_⟩
  intro γ hc L hL hgeo hopposite
  exact pointConformal_geodesic_opposite_fixed_disk_penetration
    ha y γ hc L hL hgeo hA hyA hB hD hgap hopposite

end RepulsiveCoulomb
