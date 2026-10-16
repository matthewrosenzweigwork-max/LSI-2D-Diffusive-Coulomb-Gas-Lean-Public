module

public import LeanResearch.RepulsiveCoulomb.PointConformalDensity
public import LeanResearch.RepulsiveCoulomb.RadialProductScaling

@[expose] public section

/-! Literal radial lower densities for the planar conformal density. -/
noncomputable section
open Set MeasureTheory Real
open scoped BigOperators
namespace RepulsiveCoulomb

def pointRadialDensity {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (c : ℂ) (t : ℝ) : ℝ :=
  ∏ j, |t - ‖y j - c‖| ^ (a j / 2)

theorem pointConformalDensity_eq_prod_half {m : ℕ} (a : Fin m → ℝ)
    (y : Fin m → ℂ) (z : ℂ) :
    pointConformalDensity a y z = ∏ j, ‖z - y j‖ ^ (a j / 2) := by
  unfold pointConformalDensity rawPointWeight
  rw [Real.sqrt_prod Finset.univ (fun j _ => Real.rpow_nonneg (norm_nonneg _) _)]
  apply Finset.prod_congr rfl
  intro j _
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (norm_nonneg _)]
  congr 1
  ring

theorem pointRadialDensity_nonneg {m : ℕ} (a : Fin m → ℝ) (y : Fin m → ℂ) (c : ℂ) (t : ℝ) :
    0 ≤ pointRadialDensity a y c t := by
  unfold pointRadialDensity
  positivity

theorem pointRadialDensity_continuous {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) : Continuous (pointRadialDensity a y c) := by
  apply continuous_finsetProd
  intro j _
  exact (Real.continuous_rpow_const (div_nonneg (ha j) (by norm_num))).comp (by fun_prop)

theorem pointRadialDensity_le {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c z : ℂ) :
    pointRadialDensity a y c ‖z - c‖ ≤ pointConformalDensity a y z := by
  rw [pointConformalDensity_eq_prod_half]
  apply Finset.prod_le_prod₀ (fun j _ => Real.rpow_nonneg (abs_nonneg _) _)
  intro j _
  apply Real.rpow_le_rpow (abs_nonneg _) _ (div_nonneg (ha j) (by norm_num))
  simpa only [sub_sub_sub_cancel_right] using abs_norm_sub_norm_le (z - c) (y j - c)

theorem pointRadialDensity_integral_lower {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ) {r : ℝ} (hr : 0 < r) :
    Real.exp (-2 * ∑ j, a j) * r * (∏ j, (r + ‖y j - c‖) ^ (a j / 2)) ≤
      ∫ t in (0 : ℝ)..r, pointRadialDensity a y c t := by
  have h := radial_product_integral_lower
    (fun j => div_nonneg (ha j) (by norm_num : (0 : ℝ) ≤ 2))
    (fun j => ‖y j - c‖) (fun j => norm_nonneg _) hr
  have he : -4 * (∑ j, a j / 2) = -2 * ∑ j, a j := by
    rw [← Finset.sum_div]
    ring
  simpa only [he, pointRadialDensity] using h

end RepulsiveCoulomb
