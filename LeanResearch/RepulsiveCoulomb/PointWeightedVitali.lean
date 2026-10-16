/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license; see Imported/TauCeti/LICENSE.
Authors of the original covering argument: The Tau Ceti contributors

The Vitali selection argument below is adapted from the frozen attributed
Imported/TauCeti/MeasureTheory/Integral/MaximalFunction.lean,
TauCeti.mul_measure_le_of_forall_exists_ball. The new campaign proof replaces
Haar scaling by the proved raw-point-weight growth bound. The upstream Haar
hypothesis is neither erased nor applied to a non-Haar measure; its frozen
source and PROVENANCE.json remain unchanged.
-/
import LeanResearch.RepulsiveCoulomb.PointBallMassComparison
import Mathlib.MeasureTheory.Covering.Vitali

/-! Actual weighted weak-type covering control, uniformly in the configuration. -/
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal Topology BigOperators
namespace RepulsiveCoulomb

def rawPointFourfoldConstant (Q : ℝ) : ℝ := rawPointGrowthConstant Q * (4 : ℝ) ^ (Q + 2)

theorem rawPointFourfoldConstant_pos (Q : ℝ) : 0 < rawPointFourfoldConstant Q :=
  mul_pos (rawPointGrowthConstant_pos Q) (Real.rpow_pos_of_pos (by norm_num) _)

theorem rawPointMeasure_fourfold_growth {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    (x : ℂ) {r : ℝ} (hr : 0 < r) :
    rawPointMeasure a y (closedBall x (4 * r)) ≤
      ENNReal.ofReal (rawPointFourfoldConstant Q) * rawPointMeasure a y (ball x r) := by
  simpa only [rawPointFourfoldConstant, rawPointMeasure_closedBall_eq_ball] using
    rawPointMeasure_volume_growth ha hQ y x hr (by norm_num : (1 : ℝ) ≤ 4)

theorem rawPointMeasure_vitali_weak_bound {m : ℕ} {Q : ℝ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (hQ : ∑ j, a j ≤ Q) (y : Fin m → ℂ)
    {S : Set ℂ} {R : ℝ} {g : ℂ → ℝ≥0∞} {t : ℝ≥0∞}
    (hS : ∀ x ∈ S, ∃ r ∈ Ioc (0 : ℝ) R,
      t * rawPointMeasure a y (ball x r) ≤ ∫⁻ z in ball x r, g z ∂rawPointMeasure a y) :
    t * rawPointMeasure a y S ≤
      ENNReal.ofReal (rawPointFourfoldConstant Q) * ∫⁻ z, g z ∂rawPointMeasure a y := by
  classical
  let μ := rawPointMeasure a y
  choose! r hr hle using hS
  obtain ⟨u, hu, hdisj, hcov⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall S id r R
      (fun x hx => (hr x hx).2) 4 (by norm_num)
  simp only [id_eq] at hdisj hcov
  have hcount : u.Countable :=
    hdisj.countable_of_nonempty_interior fun x hx =>
      ⟨x, ball_subset_interior_closedBall (mem_ball_self (hr x (hu hx)).1)⟩
  letI : Countable u := hcount.to_subtype
  have hsub : S ⊆ ⋃ b ∈ u, closedBall b (4 * r b) := fun x hx => by
    obtain ⟨b, hb, hball⟩ := hcov x hx
    exact mem_biUnion hb (hball (mem_closedBall_self (hr x hx).1.le))
  have hdisj' : Pairwise (Function.onFun Disjoint fun b : u => ball (b : ℂ) (r b)) :=
    fun b b' hbb' =>
      (hdisj b.2 b'.2 (Subtype.coe_injective.ne hbb')).mono ball_subset_closedBall ball_subset_closedBall
  calc
    t * μ S ≤ t * ∑' b : u, μ (closedBall (b : ℂ) (4 * r b)) := by
      apply mul_le_mul' le_rfl
      exact (measure_mono hsub).trans (measure_biUnion_le μ hcount _)
    _ = ∑' b : u, t * μ (closedBall (b : ℂ) (4 * r b)) := ENNReal.tsum_mul_left.symm
    _ ≤ ∑' b : u, ENNReal.ofReal (rawPointFourfoldConstant Q) * ∫⁻ z in ball (b : ℂ) (r b), g z ∂μ := by
      apply ENNReal.tsum_le_tsum
      intro b
      calc
        _ ≤ t * (ENNReal.ofReal (rawPointFourfoldConstant Q) * μ (ball (b : ℂ) (r b))) :=
          mul_le_mul' le_rfl (rawPointMeasure_fourfold_growth ha hQ y b (hr b (hu b.2)).1)
        _ = ENNReal.ofReal (rawPointFourfoldConstant Q) * (t * μ (ball (b : ℂ) (r b))) := by ac_rfl
        _ ≤ _ := mul_le_mul' le_rfl (hle b (hu b.2))
    _ = ENNReal.ofReal (rawPointFourfoldConstant Q) * ∑' b : u, ∫⁻ z in ball (b : ℂ) (r b), g z ∂μ :=
      ENNReal.tsum_mul_left
    _ = ENNReal.ofReal (rawPointFourfoldConstant Q) * ∫⁻ z in ⋃ b : u, ball (b : ℂ) (r b), g z ∂μ := by
      rw [lintegral_iUnion (fun b => measurableSet_ball) hdisj']
    _ ≤ _ := mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

end RepulsiveCoulomb
