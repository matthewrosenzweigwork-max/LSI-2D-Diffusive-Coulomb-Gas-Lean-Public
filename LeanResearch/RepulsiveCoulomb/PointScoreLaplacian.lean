module

public import LeanResearch.RepulsiveCoulomb.PointConformalDensity
public import LeanResearch.RepulsiveCoulomb.PointGroundStateGradient
public import Mathlib.Analysis.InnerProductSpace.Laplacian

@[expose] public section

/-! Actual Laplacian of the logarithmic Gaussian weight off positive punctures. -/
noncomputable section
open Set MeasureTheory Metric Filter InnerProductSpace
open scoped Topology BigOperators
namespace RepulsiveCoulomb

theorem complex_laplacian_norm_sq (z : ℂ) :
    Laplacian.laplacian (fun x : ℂ => ‖x‖ ^ 2) z = 4 := by
  have hfirst : fderiv ℝ (fun w : ℂ => ‖w‖ ^ 2) =
      (fun w => innerSL ℝ w + innerSL ℝ w) := by
    funext w
    simp only [fderiv_norm_sq_apply, two_smul]
  have hd (x : ℂ) : fderiv ℝ (fderiv ℝ (fun w : ℂ => ‖w‖ ^ 2)) x =
      innerSL ℝ + innerSL ℝ := by
    rw [hfirst]
    exact ((innerSL ℝ (E := ℂ)).hasFDerivAt.add (innerSL ℝ (E := ℂ)).hasFDerivAt).fderiv
  rw [laplacian_eq_iteratedFDeriv_complexPlane]
  simp only [iteratedFDeriv_two_apply, hd]
  change (inner ℝ (1 : ℂ) 1 + inner ℝ (1 : ℂ) 1) +
    (inner ℝ Complex.I Complex.I + inner ℝ Complex.I Complex.I) = 4
  norm_num [real_inner_self_eq_norm_sq]

theorem pointLogWeight_eq_gaussian_add_conformal {m : ℕ} (γ : ℝ)
    (a : Fin m → ℝ) (y : Fin m → ℂ) :
    pointLogWeight γ a y = (-γ / 2) • (fun x : ℂ => ‖x‖ ^ 2) + (2 : ℝ) • pointConformalLog a y := by
  funext z
  simp only [pointLogWeight, pointConformalLog, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem pointLogWeight_contDiffAt_two {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) : ContDiffAt ℝ 2 (pointLogWeight γ a y) z := by
  rw [pointLogWeight_eq_gaussian_add_conformal]
  exact ((contDiff_norm_sq ℝ).contDiffAt.const_smul (-γ / 2)).add
    ((pointConformalLog_harmonicAt ha y hz).1.const_smul (2 : ℝ))

theorem pointLogWeight_laplacian {m : ℕ} (γ : ℝ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {z : ℂ}
    (hz : z ∉ pointPunctures a y) :
    Laplacian.laplacian (pointLogWeight γ a y) z = -2 * γ := by
  have hbase : ContDiffAt ℝ 2 (fun x : ℂ => ‖x‖ ^ 2) z := (contDiff_norm_sq ℝ).contDiffAt
  have hh := pointConformalLog_harmonicAt ha y hz
  have hzlap : Laplacian.laplacian (pointConformalLog a y) z = 0 := hh.2.self_of_nhds
  have hg : ContDiffAt ℝ 2 ((-γ / 2) • (fun x : ℂ => ‖x‖ ^ 2)) z := by
    convert! hbase.const_smul (-γ / 2) using 1
  have hc : ContDiffAt ℝ 2 ((2 : ℝ) • pointConformalLog a y) z := by
    convert! hh.1.const_smul (2 : ℝ) using 1
  rw [pointLogWeight_eq_gaussian_add_conformal, hg.laplacian_add hc,
    laplacian_smul (-γ / 2) hbase, laplacian_smul (2 : ℝ) hh.1,
    complex_laplacian_norm_sq, hzlap]
  simp only [smul_eq_mul]
  ring

end RepulsiveCoulomb
