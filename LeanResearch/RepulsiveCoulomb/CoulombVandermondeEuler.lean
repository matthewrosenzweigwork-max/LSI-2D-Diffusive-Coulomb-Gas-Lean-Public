import LeanResearch.RepulsiveCoulomb.CoulombPotentialWeight
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Data.Finset.Prod

/-! Actual homogeneity and physical radial Euler identity for the collision
Vandermonde. No separation or bound on the collision exponent is imposed. -/
noncomputable section
open Set Filter InnerProductSpace
open scoped BigOperators Topology
namespace RepulsiveCoulomb

theorem coulombVandermonde_real_homogeneous {N : ℕ} (t : ℝ) (z : CoulombConfig N) :
    coulombVandermonde (t • z) = t ^ (coulombPairs N).card • coulombVandermonde z := by
  simp only [coulombVandermonde, PiLp.smul_apply, smul_sub, Complex.real_smul, ← mul_sub,
    Finset.prod_mul_distrib, Finset.prod_const, Complex.ofReal_pow]

theorem coulombPairs_card (N : ℕ) : (coulombPairs N).card = N.choose 2 := by
  simpa [coulombPairs] using (Finset.card_product_filter_lt (s := (Finset.univ : Finset (Fin N))))

theorem coulombVandermonde_norm_euler {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    fderiv ℝ (fun x : CoulombConfig N => ‖coulombVandermonde x‖) z z =
      ((coulombPairs N).card : ℝ) * ‖coulombVandermonde z‖ := by
  have hd := ((coulombVandermonde_contDiff_real N).contDiffAt.norm ℂ hz).differentiableAt (by simp)
  have hh : (fun t : ℝ => ‖coulombVandermonde (t • z)‖) =ᶠ[𝓝 1]
      fun t => t ^ (coulombPairs N).card • ‖coulombVandermonde z‖ := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    rw [coulombVandermonde_real_homogeneous, norm_smul]
    simp [Real.norm_eq_abs, abs_of_pos ht, abs_of_nonneg (pow_nonneg ht.le _), smul_eq_mul]
  have h := hd.hasFDerivAt.apply_self_eq_smul_of_eventuallyEq
    (hasDerivAt_pow (coulombPairs N).card (1 : ℝ)) hh
  simpa only [one_pow, mul_one, smul_eq_mul] using h

theorem coulombVandermonde_log_radial_gradient {N : ℕ} {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    inner ℝ (gradient (fun x : CoulombConfig N => Real.log ‖coulombVandermonde x‖) z) z =
      ((coulombPairs N).card : ℝ) := by
  have hd := ((coulombVandermonde_contDiff_real N).contDiffAt.norm ℂ hz).differentiableAt (by simp)
  have hn : ‖coulombVandermonde z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  rw [inner_gradient_left, (hd.hasFDerivAt.log hn).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul,
    coulombVandermonde_norm_euler hz]
  field_simp

end RepulsiveCoulomb
