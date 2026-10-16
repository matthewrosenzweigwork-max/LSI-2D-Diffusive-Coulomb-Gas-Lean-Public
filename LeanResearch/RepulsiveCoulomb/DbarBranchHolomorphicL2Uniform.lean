module

public import LeanResearch.RepulsiveCoulomb.DbarBranchHolomorphicBallL2
public import LeanResearch.RepulsiveCoulomb.DbarBranchHolomorphicLimits
public import Mathlib.MeasureTheory.Group.Integral

@[expose] public section

/-! Local uniform control of genuinely holomorphic functions by their actual
Lebesgue L2 classes. The constant is the reciprocal square root of the volume
of a fixed interior ball, not an assumed evaluation estimate. -/
noncomputable section
open Set MeasureTheory Filter Metric InnerProductSpace
open scoped Topology
namespace RepulsiveCoulomb

theorem dbar_add_mem_ball {N : ℕ} {c x y : CoulombConfig N} {r ρ R : ℝ}
    (hx : x ∈ ball c r) (hy : y ∈ ball (0 : CoulombConfig N) ρ) (h : r + ρ ≤ R) :
    x + y ∈ ball c R := by
  have hy' : ‖y‖ < ρ := by simpa only [mem_ball, dist_zero_right] using hy
  rw [mem_ball] at hx ⊢
  calc
    dist (x + y) c ≤ dist (x + y) x + dist x c := dist_triangle _ _ _
    _ = ‖y‖ + dist x c := by simp [dist_eq_norm]
    _ < R := by linarith

theorem coulomb_holomorphic_inner_ball_L2_sq_bound {N : ℕ}
    {f : CoulombConfig N → ℂ} {c x : CoulombConfig N} {r ρ R : ℝ}
    (hρ : 0 < ρ) (hmargin : r + ρ ≤ R) (hx : x ∈ ball c r)
    (hc : Continuous f) (hf : DifferentiableOn ℂ f (ball c R)) (hL2 : MemLp f 2 volume) :
    ‖f x‖ ^ 2 ≤ (volume.real (ball (0 : CoulombConfig N) ρ))⁻¹ * (∫ z, ‖f z‖ ^ 2) := by
  let g : CoulombConfig N → ℂ := fun y => f (x + y)
  have hgL2 : MemLp g 2 volume := hL2.comp_measurePreserving (measurePreserving_add_left volume x)
  have hgc : Continuous g := hc.comp (continuous_const.add continuous_id)
  have hgd : DifferentiableOn ℂ g (ball (0 : CoulombConfig N) ρ) :=
    hf.comp ((differentiableOn_const x).add differentiableOn_id)
      (fun y hy => dbar_add_mem_ball hx hy hmargin)
  have hb := coulomb_holomorphic_ball_L2_bound hρ le_rfl hgc hgd (hgL2.restrict (ball (0 : CoulombConfig N) ρ))
  have hi : Integrable (fun y => ‖g y‖ ^ 2) volume := hgL2.integrable_norm_pow (by norm_num)
  have hmono := setIntegral_le_integral (s := ball (0 : CoulombConfig N) ρ) hi
    (Eventually.of_forall fun y => sq_nonneg ‖g y‖)
  have he : (∫ y, ‖g y‖ ^ 2) = ∫ y, ‖f y‖ ^ 2 :=
    integral_add_left_eq_self (fun y => ‖f y‖ ^ 2) x
  simpa only [g, add_zero] using hb.trans
    ((mul_le_mul_of_nonneg_left hmono (inv_nonneg.mpr ENNReal.toReal_nonneg)).trans_eq
      (congrArg (fun a => (volume.real (ball (0 : CoulombConfig N) ρ))⁻¹ * a) he))

theorem coulomb_holomorphic_inner_ball_L2_norm_bound {N : ℕ}
    {f : CoulombConfig N → ℂ} (fL : Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hrep : fL =ᵐ[volume] f) {c x : CoulombConfig N} {r ρ R : ℝ}
    (hρ : 0 < ρ) (hmargin : r + ρ ≤ R) (hx : x ∈ ball c r)
    (hc : Continuous f) (hf : DifferentiableOn ℂ f (ball c R)) :
    ‖f x‖ ≤ Real.sqrt ((volume.real (ball (0 : CoulombConfig N) ρ))⁻¹) * ‖fL‖ := by
  have he : ‖fL‖ ^ 2 = ∫ z, ‖f z‖ ^ 2 := by
    rw [dbarComplexLp_norm_sq_eq_integral]
    exact integral_congr_ae (hrep.fun_comp (fun z : ℂ => ‖z‖ ^ 2))
  have hb := coulomb_holomorphic_inner_ball_L2_sq_bound hρ hmargin hx hc hf ((Lp.memLp fL).ae_eq hrep)
  rw [← he] at hb
  have hmass : 0 ≤ (volume.real (ball (0 : CoulombConfig N) ρ))⁻¹ :=
    inv_nonneg.mpr ENNReal.toReal_nonneg
  have hs := Real.sqrt_le_sqrt hb
  rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_mul hmass, Real.sqrt_sq (norm_nonneg _)] at hs
  exact hs

theorem coulomb_holomorphic_L2_uniformCauchy {N : ℕ}
    {f : ℕ → CoulombConfig N → ℂ}
    (fL : ℕ → Lp ℂ 2 (volume : Measure (CoulombConfig N)))
    (hrep : ∀ n, fL n =ᵐ[volume] f n) {c : CoulombConfig N} {r ρ R : ℝ}
    (hρ : 0 < ρ) (hmargin : r + ρ ≤ R)
    (hc : ∀ n, Continuous (f n)) (hf : ∀ n, DifferentiableOn ℂ (f n) (ball c R))
    (hL : CauchySeq fL) : UniformCauchySeqOn f atTop (ball c r) := by
  let C : ℝ := Real.sqrt ((volume.real (ball (0 : CoulombConfig N) ρ))⁻¹)
  have hC : 0 ≤ C := Real.sqrt_nonneg _
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro ε hε
  have hCp : 0 < C + 1 := by positivity
  have hδ : 0 < ε / (C + 1) := div_pos hε hCp
  obtain ⟨n0, hn0⟩ := Metric.cauchySeq_iff.mp hL (ε / (C + 1)) hδ
  refine ⟨n0, ?_⟩
  intro n hn m hm x hx
  have hnm : fL n - fL m =ᵐ[volume] f n - f m :=
    (Lp.coeFn_sub _ _).trans ((hrep n).sub (hrep m))
  have hb := coulomb_holomorphic_inner_ball_L2_norm_bound (fL n - fL m) hnm
    hρ hmargin hx ((hc n).sub (hc m)) ((hf n).sub (hf m))
  have hd := hn0 n hn m hm
  rw [dist_eq_norm] at hd ⊢
  calc
    ‖f n x - f m x‖ ≤ C * ‖fL n - fL m‖ := hb
    _ ≤ (C + 1) * ‖fL n - fL m‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
    _ < (C + 1) * (ε / (C + 1)) := mul_lt_mul_of_pos_left hd hCp
    _ = ε := by field_simp

end RepulsiveCoulomb
