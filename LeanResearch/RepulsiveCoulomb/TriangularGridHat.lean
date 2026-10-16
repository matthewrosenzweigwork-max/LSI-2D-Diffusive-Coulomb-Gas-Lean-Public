module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Tactic

@[expose] public section

/-! A literal compactly supported nodal hat for the regular diagonal triangular
lattice. Its Lipschitz and support bounds are proved before using it in approximation. -/
noncomputable section
open Set Metric
open scoped NNReal
namespace RepulsiveCoulomb

def triangularGridHat (z : ℂ) : ℝ :=
  max 0 (1 - max |z.re| (max |z.im| |z.re - z.im|))

theorem triangularGridHat_nonneg (z : ℂ) : 0 ≤ triangularGridHat z := le_max_left _ _

theorem triangularGridHat_le_one (z : ℂ) : triangularGridHat z ≤ 1 := by
  unfold triangularGridHat
  apply max_le (by norm_num)
  have h := (abs_nonneg z.re).trans (le_max_left |z.re| (max |z.im| |z.re - z.im|))
  linarith

theorem complex_re_lipschitz : LipschitzWith 1 (Complex.re : ℂ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [Real.dist_eq, Complex.dist_eq, Complex.sub_re, NNReal.coe_one, one_mul] using
    Complex.abs_re_le_norm (z - w)

theorem complex_im_lipschitz : LipschitzWith 1 (Complex.im : ℂ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro z w
  simpa only [Real.dist_eq, Complex.dist_eq, Complex.sub_im, NNReal.coe_one, one_mul] using
    Complex.abs_im_le_norm (z - w)

theorem triangularGridHat_lipschitz : LipschitzWith 2 triangularGridHat := by
  have habs : LipschitzWith 1 (fun x : ℝ => |x|) := by
    simpa only [Real.dist_eq, sub_zero] using LipschitzWith.dist_left (0 : ℝ)
  have hr : LipschitzWith 1 (fun z : ℂ => |z.re|) := by
    simpa only [one_mul, Function.comp_def] using habs.comp complex_re_lipschitz
  have hi : LipschitzWith 1 (fun z : ℂ => |z.im|) := by
    simpa only [one_mul, Function.comp_def] using habs.comp complex_im_lipschitz
  have hd : LipschitzWith 2 (fun z : ℂ => |z.re - z.im|) := by
    simpa only [one_mul, Function.comp_def, show (1 : ℝ≥0) + 1 = 2 by norm_num] using habs.comp (complex_re_lipschitz.sub complex_im_lipschitz)
  have hm := hr.max (hi.max hd)
  have hh := ((LipschitzWith.const (1 : ℝ)).sub hm).const_max 0
  change LipschitzWith 2 (fun z : ℂ => max 0 (1 - max |z.re| (max |z.im| |z.re - z.im|)))
  convert hh using 1 <;> norm_num

theorem triangularGridHat_hasCompactSupport : HasCompactSupport triangularGridHat := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : ℂ) 2)
  intro z hz
  have hm : max |z.re| (max |z.im| |z.re - z.im|) < 1 := by
    by_contra h
    have hh : 1 - max |z.re| (max |z.im| |z.re - z.im|) ≤ 0 := by linarith
    exact hz (max_eq_left hh)
  have hr : |z.re| < 1 := (le_max_left _ _).trans_lt hm
  have hi : |z.im| < 1 := (le_max_left _ _).trans (le_max_right _ _) |>.trans_lt hm
  rw [mem_closedBall, dist_zero_right]
  have hn := Complex.norm_le_abs_re_add_abs_im z
  linarith

theorem triangularGridHat_zero : triangularGridHat 0 = 1 := by norm_num [triangularGridHat]

end RepulsiveCoulomb
