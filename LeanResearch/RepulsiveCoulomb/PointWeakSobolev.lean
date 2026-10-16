module

public import LeanResearch.RepulsiveCoulomb.WeakPowerDistribution

@[expose] public section

/-! Actual weak local Sobolev distribution control, conditional on the
explicit weak(1,2) Poincare input. This is not the strong Sobolev upgrade. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem rawPointMeasure_weak_sobolev_of_poincare {m : ℕ} {Q P : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (hP : 0 < P) (y : Fin m → ℂ)
    (f g : ℂ → ℝ) (hf : Continuous f) (hg : Continuous g) (hgn : ∀ z, 0 ≤ g z)
    (hPI : ∀ z : ℂ, ∀ r : ℝ, 0 < r →
      (⨍ v in ball z r, ‖f v - (⨍ w in ball z r, f w ∂rawPointMeasure a y)‖ ∂rawPointMeasure a y) ≤
        P * r * Real.sqrt (⨍ w in ball z (5 * r), g w ∂rawPointMeasure a y))
    (c : ℂ) {R L : ℝ} (hR : 0 < R) (hL : 0 < L) :
    ENNReal.ofReal (L ^ (2 * pointSobolevKappa Q)) * rawPointMeasure a y
      {x | x ∈ ball c R ∧ L < ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖} ≤
    ENNReal.ofReal ((pointHedbergConstant Q P * R *
        (pointLocalEnergy Q a y c R g) ^ pointSobolevGain Q) ^ (2 * pointSobolevKappa Q)) *
      (ENNReal.ofReal (rawPointFourfoldConstant Q) *
        ∫⁻ z in ball c (11 * R), ENNReal.ofReal (g z) ∂rawPointMeasure a y) := by
  have hQ0 : 0 ≤ Q := (Finset.sum_nonneg (fun j _ => ha j)).trans hQ
  by_cases hE : pointLocalEnergy Q a y c R g = 0
  · have hzero (x : ℂ) (hx : x ∈ ball c R) :
        ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖ = 0 := by
      have h := rawPointMeasure_oscillation_le_series ha hQ hP.le y f g hf hPI c hR hx
      rw [pointPoincareSeries_zero_of_energy_zero ha hQ y hR hx g hg hgn hE, mul_zero] at h
      exact le_antisymm (ENNReal.ofReal_eq_zero.mp (le_antisymm h bot_le)) (norm_nonneg _)
    have hs : {x | x ∈ ball c R ∧ L < ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt_of_ge hL.le) (by simpa only [hzero x hx.1] using hx.2)
    rw [hs, measure_empty, mul_zero]
    exact bot_le
  have hEp : 0 < pointLocalEnergy Q a y c R g :=
    lt_of_le_of_ne (pointLocalEnergy_nonneg Q a y c R g hgn) (Ne.symm hE)
  apply weak_distribution_of_power_bound (rawPointMeasure a y) (ball c R)
    (fun x => ‖f x - (⨍ z in ball c R, f z ∂rawPointMeasure a y)‖)
    (pointLocalMaximalEnergy a y c R g)
    (α := pointSobolevMaximalExponent Q)
    (mul_pos (mul_pos (pointHedbergConstant_pos Q hP) hR) (Real.rpow_pos_of_pos hEp _))
    (mul_pos (by norm_num) (lt_trans zero_lt_one (pointSobolevKappa_gt_one hQ0)))
    (pointSobolevMaximalExponent_times_q hQ0)
    (fun x _ => (pointLocalMaximalEnergy_lt_top ha y c hR hg x).ne) ?_ ?_ hL
  · intro x hx
    have h := rawPointMeasure_hedberg_oscillation ha hQ hP y f g hf hg hgn hPI c hR hx
    convert h using 1
    ring
  · intro t
    exact rawPoint_local_dyadic_maximal_weak_bound ha hQ y c hR (fun z => ENNReal.ofReal (g z)) t

end RepulsiveCoulomb
