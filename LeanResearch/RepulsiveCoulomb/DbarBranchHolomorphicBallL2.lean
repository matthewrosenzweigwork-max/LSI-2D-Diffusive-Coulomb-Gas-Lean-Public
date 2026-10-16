module

public import LeanResearch.RepulsiveCoulomb.DbarBranchHolomorphicBallMean
public import Mathlib.MeasureTheory.Function.L2Space

@[expose] public section

/-! Local holomorphic L2 point evaluation in the actual finite-dimensional
configuration space, obtained from the proved ball mean value and Hilbert
Cauchy-Schwarz. This is an auxiliary local bound, not the weighted dbar estimate. -/
noncomputable section
open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem dbarComplexLp_norm_sq_eq_integral {X : Type*} [MeasurableSpace X] {μ : Measure X}
    (f : Lp ℂ 2 μ) : ‖f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => real_inner_self_eq_norm_sq (f x)

theorem dbarFiniteMeasure_integral_norm_sq_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} [IsFiniteMeasure μ] {f : X → ℂ} (hf : MemLp f 2 μ) :
    ‖∫ x, f x ∂μ‖ ^ 2 ≤ μ.real univ * (∫ x, ‖f x‖ ^ 2 ∂μ) := by
  let oneL : Lp ℂ 2 μ := (memLp_const (p := 2) (μ := μ) (1 : ℂ)).toLp (fun _ => (1 : ℂ))
  let fL : Lp ℂ 2 μ := hf.toLp f
  have hone : oneL =ᵐ[μ] fun _ => (1 : ℂ) := MemLp.coeFn_toLp _
  have hfl : fL =ᵐ[μ] f := hf.coeFn_toLp
  have hinner : inner ℂ oneL fL = ∫ x, f x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hone, hfl] with x h1 hx
    simp only [h1, hx, RCLike.inner_apply', map_one, one_mul]
  have h1norm : ‖oneL‖ ^ 2 = μ.real univ := by
    rw [dbarComplexLp_norm_sq_eq_integral]
    calc
      _ = ∫ _x : X, (1 : ℝ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hone] with x hx
        simp [hx]
      _ = _ := by simp
  have hfnorm : ‖fL‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
    rw [dbarComplexLp_norm_sq_eq_integral]
    exact integral_congr_ae (hfl.fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  have hcs := pow_le_pow_left₀ (norm_nonneg (inner ℂ oneL fL)) (norm_inner_le_norm oneL fL) 2
  rwa [hinner, mul_pow, h1norm, hfnorm] at hcs

theorem coulomb_holomorphic_ball_L2_mass_bound {N : ℕ} {f : CoulombConfig N → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hc : Continuous f)
    (hf : DifferentiableOn ℂ f (ball (0 : CoulombConfig N) R))
    (hL2 : MemLp f 2 (volume.restrict (ball (0 : CoulombConfig N) r))) :
    volume.real (ball (0 : CoulombConfig N) r) * ‖f 0‖ ^ 2 ≤
      ∫ z in ball (0 : CoulombConfig N) r, ‖f z‖ ^ 2 := by
  have hfin : volume (ball (0 : CoulombConfig N) r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : CoulombConfig N) r).measure_lt_top
  letI : IsFiniteMeasure (volume.restrict (ball (0 : CoulombConfig N) r)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hfin⟩
  have hm : 0 < volume.real (ball (0 : CoulombConfig N) r) :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume (0 : CoulombConfig N) hr)) hfin.ne
  have hmean := coulomb_holomorphic_ball_integral hrR hc hf (MemLp.integrable (by norm_num) hL2)
  have hcs := dbarFiniteMeasure_integral_norm_sq_le hL2
  rw [hmean, norm_smul, Real.norm_eq_abs, abs_of_pos hm, mul_pow, measureReal_restrict_apply_univ] at hcs
  apply (mul_le_mul_iff_right₀ hm).mp
  nlinarith only [hcs]

theorem coulomb_holomorphic_ball_L2_bound {N : ℕ} {f : CoulombConfig N → ℂ} {r R : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hc : Continuous f)
    (hf : DifferentiableOn ℂ f (ball (0 : CoulombConfig N) R))
    (hL2 : MemLp f 2 (volume.restrict (ball (0 : CoulombConfig N) r))) :
    ‖f 0‖ ^ 2 ≤ (volume.real (ball (0 : CoulombConfig N) r))⁻¹ *
      (∫ z in ball (0 : CoulombConfig N) r, ‖f z‖ ^ 2) := by
  have hfin : volume (ball (0 : CoulombConfig N) r) < ⊤ :=
    (measure_mono ball_subset_closedBall).trans_lt (isCompact_closedBall (0 : CoulombConfig N) r).measure_lt_top
  have hm : 0 < volume.real (ball (0 : CoulombConfig N) r) :=
    ENNReal.toReal_pos (ne_of_gt (measure_ball_pos volume (0 : CoulombConfig N) hr)) hfin.ne
  rw [← div_eq_inv_mul, le_div_iff₀ hm, mul_comm]
  exact coulomb_holomorphic_ball_L2_mass_bound hr hrR hc hf hL2

end RepulsiveCoulomb
