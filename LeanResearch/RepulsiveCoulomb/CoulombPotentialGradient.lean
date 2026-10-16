module

public import LeanResearch.RepulsiveCoulomb.CoulombVandermondeEuler

@[expose] public section

/-! The actual potential's radial coercivity, before integration by parts. -/
noncomputable section
open Set InnerProductSpace
namespace RepulsiveCoulomb

theorem coulombPotential_gradient {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    gradient (coulombPotential β) z = β • z - (β / (N : ℝ)) •
      gradient (fun x : CoulombConfig N => Real.log ‖coulombVandermonde x‖) z := by
  have hn : DifferentiableAt ℝ (fun x : CoulombConfig N => ‖x‖ ^ 2) z :=
    (contDiff_norm_sq ℝ (E := CoulombConfig N) (n := 1)).differentiable (by norm_num) z
  have hl := (((coulombVandermonde_contDiff_real N).contDiffAt.norm ℂ hz).log
    (norm_ne_zero_iff.mpr hz)).differentiableAt (by simp)
  apply (InnerProductSpace.toDual ℝ (CoulombConfig N)).injective
  rw [map_sub, map_smul, map_smul, toDual_gradient, toDual_gradient]
  change fderiv ℝ (fun x : CoulombConfig N => (β / 2) * ‖x‖ ^ 2 -
    (β / (N : ℝ)) * Real.log ‖coulombVandermonde x‖) z = _
  rw [fderiv_fun_sub (hn.const_mul _) (hl.const_mul _),
    fderiv_const_mul hn, fderiv_const_mul hl, fderiv_norm_sq_apply]
  ext v
  simp only [two_smul, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.add_apply, smul_eq_mul]
  change (β / 2) * (inner ℝ z v + inner ℝ z v) -
    (β / (N : ℝ)) * fderiv ℝ (fun x : CoulombConfig N => Real.log ‖coulombVandermonde x‖) z v =
    β * inner ℝ z v - (β / (N : ℝ)) *
      fderiv ℝ (fun x : CoulombConfig N => Real.log ‖coulombVandermonde x‖) z v
  ring

theorem coulombPotential_gradient_sq_lower {N : ℕ} (β : ℝ) {z : CoulombConfig N}
    (hz : z ∈ coulombDomain N) :
    β ^ 2 * ‖z‖ ^ 2 - 2 * β * (β / (N : ℝ)) * ((coulombPairs N).card : ℝ) ≤
      ‖gradient (coulombPotential β) z‖ ^ 2 := by
  rw [coulombPotential_gradient β hz, norm_sub_sq_real]
  have he := coulombVandermonde_log_radial_gradient hz
  rw [real_inner_comm] at he
  simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    inner_smul_left, inner_smul_right, smul_eq_mul, starRingEnd_apply, star_trivial, he]
  nlinarith [sq_nonneg (β / (N : ℝ)), sq_nonneg
    ‖gradient (fun x : CoulombConfig N => Real.log ‖coulombVandermonde x‖) z‖,
    mul_nonneg (sq_nonneg (β / (N : ℝ))) (sq_nonneg
      ‖gradient (fun x : CoulombConfig N => Real.log ‖coulombVandermonde x‖) z‖)]

end RepulsiveCoulomb
