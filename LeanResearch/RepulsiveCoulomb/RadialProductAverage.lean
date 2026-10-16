module

public import LeanResearch.RepulsiveCoulomb.RadialLogAverage
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

@[expose] public section

/-! Uniform lower averages for arbitrary finite products of positive powers of
one-dimensional distances. The constant depends on the sum of powers only,
including coincident locations and zero powers. -/
noncomputable section
open Set MeasureTheory Filter Real
open scoped BigOperators ENNReal Topology
namespace RepulsiveCoulomb

theorem radial_log_intervalIntegrable (d : ℝ) :
    IntervalIntegrable (fun t : ℝ => Real.log |t - d|) volume 0 1 := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := -d) (b := 1 - d)).comp_sub_right d
  simpa only [neg_add_cancel, sub_add_cancel, Real.log_abs] using h

theorem radial_product_average_lower {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (d : Fin m → ℝ) (hd : ∀ j, 0 ≤ d j) :
    Real.exp (-4 * ∑ j, a j) * (∏ j, (1 + d j) ^ a j) ≤
      ∫ t in (0 : ℝ)..1, ∏ j, |t - d j| ^ a j := by
  let μ : Measure ℝ := volume.restrict (Ioc (0 : ℝ) 1)
  letI : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  let f : ℝ → ℝ := fun t => ∑ j, a j * Real.log |t - d j|
  let g : ℝ → ℝ := fun t => ∏ j, |t - d j| ^ a j
  have hj (j : Fin m) : IntervalIntegrable (fun t : ℝ => a j * Real.log |t - d j|) volume 0 1 :=
    (radial_log_intervalIntegrable (d j)).const_mul (a j)
  have hf : IntervalIntegrable f volume 0 1 := by
    convert IntervalIntegrable.sum Finset.univ (fun j _ => hj j) using 1
    ext t
    simp [f]
  have hgc : Continuous g := by
    apply continuous_finsetProd
    intro j _
    exact (continuous_id.sub continuous_const).abs.rpow_const (fun _ => Or.inr (ha j))
  have hg : Integrable g μ := hgc.intervalIntegrable 0 1 |>.1
  have hnot : ∀ᵐ t ∂μ, t ∉ Set.range d := by
    rw [ae_iff]
    simpa only [not_not, Set.ofPred_mem_eq] using (Set.finite_range d).measure_zero μ
  have heq : (Real.exp ∘ f) =ᵐ[μ] g := by
    filter_upwards [hnot] with t ht
    change Real.exp (∑ j, a j * Real.log |t - d j|) = ∏ j, |t - d j| ^ a j
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    have hp : 0 < |t - d j| := abs_pos.mpr (sub_ne_zero.mpr (fun h => ht ⟨j, h.symm⟩))
    rw [Real.rpow_def_of_pos hp]
    congr 1
    ring
  have he : Integrable (Real.exp ∘ f) μ := hg.congr heq.symm
  have hJ := convexOn_exp.map_integral_le (μ := μ) (f := f)
    Real.continuous_exp.continuousOn isClosed_univ (Eventually.of_forall (fun _ => mem_univ _)) hf.1 he
  have hlow : -4 * ∑ j, a j + ∑ j, a j * Real.log (1 + d j) ≤ ∫ t, f t ∂μ := by
    have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
      mul_le_mul_of_nonneg_left (interval_log_distance_uniform_lower (hd j)) (ha j))
    simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul] at h
    rw [show (∫ t, f t ∂μ) = ∫ t in (0 : ℝ)..1, f t from
      (intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)).symm]
    rw [intervalIntegral.integral_finsetSum (fun j _ => hj j)]
    simp_rw [intervalIntegral.integral_const_mul]
    linarith
  have hprod : Real.exp (∑ j, a j * Real.log (1 + d j)) = ∏ j, (1 + d j) ^ a j := by
    rw [Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    rw [Real.rpow_def_of_pos (by have := hd j; positivity)]
    congr 1
    ring
  calc
    _ = Real.exp (-4 * ∑ j, a j + ∑ j, a j * Real.log (1 + d j)) := by rw [Real.exp_add, hprod]
    _ ≤ Real.exp (∫ t, f t ∂μ) := Real.exp_le_exp.mpr hlow
    _ ≤ ∫ t, Real.exp (f t) ∂μ := hJ
    _ = ∫ t, g t ∂μ := integral_congr_ae heq
    _ = _ := (intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)).symm

end RepulsiveCoulomb
