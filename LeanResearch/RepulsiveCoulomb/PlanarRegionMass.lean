module

public import LeanResearch.RepulsiveCoulomb.PlanarLpIntegralIdentities

@[expose] public section

/-! Actual small-region mass control by Holder and planar Ladyzhenskaya. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem planar_region_mass_le_l4 {v : ℂ → ℝ} (hv : Continuous v) (hc : HasCompactSupport v)
    (S : Set ℂ) (hS : volume S ≠ ⊤) :
    (∫ x in S, v x ^ 2) ≤ Real.sqrt (volume.real S) * lpNorm v 4 volume ^ 2 := by
  let μ := volume.restrict S
  letI : IsFiniteMeasure μ := ⟨by simpa only [μ, Measure.restrict_apply_univ] using hS.lt_top⟩
  have hc2 : HasCompactSupport (fun x => v x ^ 2) := by
    convert hc.mul_right (f' := v) using 1
    ext x
    change v x ^ 2 = v x * v x
    ring
  have hc4 : HasCompactSupport (fun x => v x ^ 4) := by
    convert hc.mul_right (f' := fun x => v x ^ 3) using 1
    ext x
    change v x ^ 4 = v x * v x ^ 3
    ring
  have hg : MemLp (fun x => v x ^ 2) (ENNReal.ofReal 2) μ :=
    ((hv.pow 2).memLp_of_hasCompactSupport hc2).restrict S
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := μ)
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    (f := fun _ : ℂ => 1) (g := fun x => v x ^ 2)
    (Eventually.of_forall (fun _ => zero_le_one))
    (Eventually.of_forall (fun x => sq_nonneg (v x))) (memLp_const 1) hg
  simp only [one_mul, Real.rpow_two, one_pow, integral_const, smul_eq_mul, mul_one,
    Measure.real, μ, Measure.restrict_apply_univ] at h
  have he (x : ℂ) : (v x ^ 2) ^ 2 = v x ^ 4 := by ring
  simp only [he, ← Real.sqrt_eq_rpow] at h
  have hi : (∫ x in S, v x ^ 4) ≤ ∫ x : ℂ, v x ^ 4 :=
    integral_mono_measure Measure.restrict_le_self (Eventually.of_forall (fun x => by positivity))
      ((hv.pow 4).integrable_of_hasCompactSupport hc4)
  have hn : lpNorm v 4 volume ^ 2 = Real.sqrt (∫ x : ℂ, v x ^ 4) := by
    simpa only [real_norm_fourth] using lpNorm_four_sq_eq_sqrt_integral volume hv.aestronglyMeasurable
  rw [hn]
  exact h.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hi) (Real.sqrt_nonneg _))

theorem planar_region_mass_ladyzhenskaya {v : ℂ → ℝ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) (S : Set ℂ) (hS : volume S ≠ ⊤) :
    (∫ x in S, v x ^ 2) ≤ Real.sqrt (volume.real S) * (planarLadyzhenskayaConstant : ℝ) *
      Real.sqrt (∫ x : ℂ, v x ^ 2) * Real.sqrt (∫ x : ℂ, ‖gradient v x‖ ^ 2) := by
  have h := (planar_region_mass_le_l4 hv.continuous hc S hS).trans
    (mul_le_mul_of_nonneg_left (planar_ladyzhenskaya hv hc) (Real.sqrt_nonneg _))
  have hg : Continuous (gradient v) :=
    (InnerProductSpace.toDual ℝ ℂ).symm.continuous.comp (hv.continuous_fderiv one_ne_zero)
  rw [lpNorm_two_eq_sqrt_integral volume hv.continuous.aestronglyMeasurable,
    lpNorm_two_eq_sqrt_integral volume hg.aestronglyMeasurable] at h
  simp only [Real.norm_eq_abs, sq_abs] at h
  simpa only [mul_assoc] using h

end RepulsiveCoulomb
