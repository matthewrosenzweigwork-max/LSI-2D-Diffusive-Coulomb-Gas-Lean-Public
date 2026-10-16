module

public import LeanResearch.RepulsiveCoulomb.PointPunctureCapacity
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Vanishing value errors for point cutoffs and finite-puncture preparation.
All measures are the literal normalized weighted Gaussian. -/
noncomputable section
open MeasureTheory Set Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

theorem pointCutoff_tendsto_zero_off_center (c z : ℂ) (hz : z ≠ c)
    {ι : Type*} {l : Filter ι} (ε : ι → ℝ) (hε : ∀ t, 0 < ε t)
    (hlim : Tendsto ε l (𝓝 0)) :
    Tendsto (fun t ↦ pointCutoffBump c (ε t) (hε t) z) l (𝓝 0) := by
  have hd : 0 < dist z c / 2 := div_pos (dist_pos.mpr hz) (by norm_num)
  have he : ∀ᶠ t in l, pointCutoffBump c (ε t) (hε t) z = 0 := by
    filter_upwards [hlim.eventually_le_const hd] with t ht
    apply (pointCutoffBump c (ε t) (hε t)).zero_of_le_dist
    change 2 * ε t ≤ dist z c
    linarith
  exact tendsto_const_nhds.congr' (he.mono fun t ht ↦ ht.symm)

/-- The squared L2 mass of a point bump vanishes for every positive scale sequence. -/
theorem pointCutoff_L2_tendsto_zero {m : ℕ} {γ : ℝ} (hγ : 0 < γ)
    {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (c : ℂ)
    (ε : ℕ → ℝ) (hε : ∀ n, 0 < ε n) (hlim : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ ∫ z, (pointCutoffBump c (ε n) (hε n) z) ^ 2
      ∂pointMeasure γ a y) atTop (𝓝 0) := by
  let _ := pointMeasure_isProbability hγ ha y
  have hzero : ∀ᵐ z ∂pointMeasure γ a y, z ≠ c := by
    apply (pointMeasure_ae_iff hγ ha y).mpr
    exact volume.ae_ne c
  have h := tendsto_integral_of_dominated_convergence (μ := pointMeasure γ a y)
    (F := fun n z ↦ (pointCutoffBump c (ε n) (hε n) z) ^ 2)
    (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ (1 : ℝ))
    (fun n ↦ ((pointCutoffBump_contDiff c (ε n) (hε n)).continuous.pow 2).aestronglyMeasurable)
    (integrable_const 1) ?_ ?_
  · simpa only [integral_zero] using h
  · intro n
    exact Eventually.of_forall fun z ↦ by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h0 := (pointCutoffBump c (ε n) (hε n)).nonneg (x := z)
      have h1 := (pointCutoffBump c (ε n) (hε n)).le_one (x := z)
      nlinarith
  · filter_upwards [hzero] with z hz
    simpa using (pointCutoff_tendsto_zero_off_center c z hz ε hε hlim).pow 2

end RepulsiveCoulomb
