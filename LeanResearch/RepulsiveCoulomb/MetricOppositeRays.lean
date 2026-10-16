import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Tactic.Linarith

/-! Join actual opposite unit-speed rays into a complete unit-speed line.
The cross-distance equality is explicit. No assertion that a merely local
angle condition implies that equality is hidden in this elementary assembly. -/
noncomputable section
namespace RepulsiveCoulomb

def metricOppositeRaysJoin {X : Type*} (f g : NNReal → X) : ℝ → X :=
  fun t ↦ if 0 ≤ t then f t.toNNReal else g (-t).toNNReal

theorem metricOppositeRaysJoin_nonneg {X : Type*} (f g : NNReal → X) (t : NNReal) :
    metricOppositeRaysJoin f g t = f t := by
  simp [metricOppositeRaysJoin, t.2]

theorem metricOppositeRaysJoin_nonpos {X : Type*} (f g : NNReal → X)
    (h0 : f 0 = g 0) (t : NNReal) : metricOppositeRaysJoin f g (-(t : ℝ)) = g t := by
  by_cases ht : t = 0
  · subst t
    simpa [metricOppositeRaysJoin] using h0
  · have ht' : 0 < (t : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr ht : 0 < t)
    simp [metricOppositeRaysJoin, not_le.mpr (by linarith : -(t : ℝ) < 0)]

/-- Exact cross-ray distances produce an actual isometric complete line. -/
theorem metricOppositeRaysJoin_isometry {X : Type*} [MetricSpace X]
    (f g : NNReal → X) (hf : Isometry f) (hg : Isometry g)
    (hcross : ∀ s t : NNReal, dist (f s) (g t) = (s : ℝ) + t) :
    Isometry (metricOppositeRaysJoin f g) := by
  apply Isometry.of_dist_eq
  intro s t
  by_cases hs : 0 ≤ s
  · by_cases ht : 0 ≤ t
    · simp only [metricOppositeRaysJoin, if_pos hs, if_pos ht, hf.dist_eq,
        NNReal.dist_eq, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht, Real.dist_eq]
    · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
      simp only [metricOppositeRaysJoin, if_pos hs, if_neg ht, hcross,
        Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht', Real.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr ((le_of_not_ge ht).trans hs))]
      rw [sub_eq_add_neg]
  · have hs' : 0 ≤ -s := neg_nonneg.mpr (le_of_not_ge hs)
    by_cases ht : 0 ≤ t
    · simp only [metricOppositeRaysJoin, if_neg hs, if_pos ht]
      rw [dist_comm, hcross, Real.coe_toNNReal _ ht, Real.coe_toNNReal _ hs',
        Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr ((le_of_not_ge hs).trans ht)), neg_sub]
      rw [sub_eq_add_neg]
    · have ht' : 0 ≤ -t := neg_nonneg.mpr (le_of_not_ge ht)
      simp only [metricOppositeRaysJoin, if_neg hs, if_neg ht, hg.dist_eq,
        NNReal.dist_eq, Real.coe_toNNReal _ hs', Real.coe_toNNReal _ ht', Real.dist_eq]
      rw [neg_sub_neg, abs_sub_comm]

end RepulsiveCoulomb
