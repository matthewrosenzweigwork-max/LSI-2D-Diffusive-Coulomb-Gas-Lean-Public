import LeanResearch.RepulsiveCoulomb.MetricOpenRayPrefix
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Literal concatenation of two exact metric segments when the outer endpoint
triangle inequality is an equality. This uses elementary metric inequalities,
not nonbranching, local-to-global continuation, or ambient isometric gluing. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

theorem metricSegments_cross_distance_of_endpoint_add {X : Type*} [MetricSpace X]
    (A B : NNReal) (f g : NNReal → X)
    (hf : ∀ s ≤ A, ∀ t ≤ A, dist (f s) (f t) = dist s t)
    (hg : ∀ s ≤ B, ∀ t ≤ B, dist (g s) (g t) = dist s t)
    (hjoin : f A = g 0) (hfull : dist (f 0) (g B) = (A : ℝ) + B)
    (s : NNReal) (hs : s ≤ A) (t : NNReal) (ht : t ≤ B) :
    dist (f s) (g t) = ((A : ℝ) - s) + t := by
  have h0s : dist (f 0) (f s) = (s : ℝ) := by
    rw [hf 0 (show (0 : NNReal) ≤ A from zero_le) s hs]
    change |(0 : ℝ) - (s : ℝ)| = (s : ℝ)
    rw [zero_sub, abs_neg, abs_of_nonneg (a := (s : ℝ)) (by positivity)]
  have hsA : dist (f s) (f A) = (A : ℝ) - s := by
    simpa only [NNReal.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ A from hs)), neg_sub]
      using hf s hs A le_rfl
  have h0t : dist (g 0) (g t) = (t : ℝ) := by
    rw [hg 0 (show (0 : NNReal) ≤ B from zero_le) t ht]
    change |(0 : ℝ) - (t : ℝ)| = (t : ℝ)
    rw [zero_sub, abs_neg, abs_of_nonneg (a := (t : ℝ)) (by positivity)]
  have htB : dist (g t) (g B) = (B : ℝ) - t := by
    simpa only [NNReal.dist_eq,
      abs_of_nonpos (sub_nonpos.mpr (show (t : ℝ) ≤ B from ht)), neg_sub]
      using hg t ht B le_rfl
  have hu := dist_triangle (f s) (f A) (g t)
  rw [hsA, hjoin, h0t] at hu
  have hl₁ := dist_triangle (f 0) (f s) (g B)
  have hl₂ := dist_triangle (f s) (g t) (g B)
  rw [hfull, h0s] at hl₁
  rw [htB] at hl₂
  linarith

def metricSegmentJoin {X : Type*} (A : NNReal) (f g : NNReal → X) : NNReal → X :=
  fun t ↦ if t ≤ A then f t else g (t - A)

theorem metricSegmentJoin_distance {X : Type*} [MetricSpace X]
    (A B : NNReal) (f g : NNReal → X)
    (hf : ∀ s ≤ A, ∀ t ≤ A, dist (f s) (f t) = dist s t)
    (hg : ∀ s ≤ B, ∀ t ≤ B, dist (g s) (g t) = dist s t)
    (hjoin : f A = g 0) (hfull : dist (f 0) (g B) = (A : ℝ) + B)
    (s : NNReal) (hs : s ≤ A + B) (t : NNReal) (ht : t ≤ A + B) :
    dist (metricSegmentJoin A f g s) (metricSegmentJoin A f g t) = dist s t := by
  classical
  have hc := metricSegments_cross_distance_of_endpoint_add A B f g hf hg hjoin hfull
  have hsub (u : NNReal) (hu : u ≤ A + B) : u - A ≤ B := by
    apply tsub_le_iff_right.mpr
    simpa only [add_comm] using hu
  by_cases hsA : s ≤ A
  · by_cases htA : t ≤ A
    · simp only [metricSegmentJoin, if_pos hsA, if_pos htA]
      exact hf s hsA t htA
    · have hAt : A < t := lt_of_not_ge htA
      simp only [metricSegmentJoin, if_pos hsA, if_neg htA]
      rw [hc s hsA (t - A) (hsub t ht), NNReal.coe_sub hAt.le, NNReal.dist_eq,
        abs_of_nonpos (sub_nonpos.mpr (show (s : ℝ) ≤ t from hsA.trans hAt.le)), neg_sub]
      ring
  · have hAs : A < s := lt_of_not_ge hsA
    by_cases htA : t ≤ A
    · simp only [metricSegmentJoin, if_neg hsA, if_pos htA]
      rw [dist_comm, hc t htA (s - A) (hsub s hs), NNReal.coe_sub hAs.le, NNReal.dist_eq,
        abs_of_nonneg (sub_nonneg.mpr (show (t : ℝ) ≤ s from htA.trans hAs.le))]
      ring
    · have hAt : A < t := lt_of_not_ge htA
      simp only [metricSegmentJoin, if_neg hsA, if_neg htA]
      rw [hg (s - A) (hsub s hs) (t - A) (hsub t ht), NNReal.dist_eq, NNReal.dist_eq,
        NNReal.coe_sub hAs.le, NNReal.coe_sub hAt.le]
      congr 1
      ring

/-- The additive endpoint condition gives a strictly longer literal open
prefix; its length increase is the positive length of the appended segment. -/
theorem exists_metricOpenRayPrefix_strict_extension {X : Type*} [MetricSpace X]
    (p : MetricOpenRayPrefix X) (A B : NNReal) (hA : p.duration = (A : ℝ≥0∞))
    (hB : 0 < B) (f g : NNReal → X)
    (hfold : ∀ t : NNReal, (t : ℝ≥0∞) < p.duration → f t = p.curve t)
    (hf : ∀ s ≤ A, ∀ t ≤ A, dist (f s) (f t) = dist s t)
    (hg : ∀ s ≤ B, ∀ t ≤ B, dist (g s) (g t) = dist s t)
    (hjoin : f A = g 0) (hfull : dist (f 0) (g B) = (A : ℝ) + B) :
    ∃ q : MetricOpenRayPrefix X, p ≤ q ∧ p.duration < q.duration := by
  let q : MetricOpenRayPrefix X :=
    { duration := (A + B : NNReal)
      curve := metricSegmentJoin A f g
      metric := fun s t hs ht ↦ metricSegmentJoin_distance A B f g hf hg hjoin hfull s
        (ENNReal.coe_lt_coe.mp hs).le t (ENNReal.coe_lt_coe.mp ht).le }
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · rw [hA]
    exact ENNReal.coe_le_coe.mpr (le_add_of_nonneg_right (show (0 : NNReal) ≤ B from zero_le))
  · intro t ht
    have htA : t ≤ A := (ENNReal.coe_lt_coe.mp (hA ▸ ht)).le
    change p.curve t = metricSegmentJoin A f g t
    rw [metricSegmentJoin, if_pos htA, hfold t ht]
  · rw [hA]
    exact ENNReal.coe_lt_coe.mpr (lt_add_of_pos_right A hB)

end RepulsiveCoulomb
