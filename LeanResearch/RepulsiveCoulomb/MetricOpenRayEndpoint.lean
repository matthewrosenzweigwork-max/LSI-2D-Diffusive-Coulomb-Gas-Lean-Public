import LeanResearch.RepulsiveCoulomb.MetricOpenRayPrefix
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.MetricSpace.Cauchy

/-! A finite open isometric ray prefix in a complete metric space has its actual
Cauchy endpoint. Adding that endpoint preserves every pairwise distance. This
does not extend past the endpoint and does not assume nonbranching. -/
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace RepulsiveCoulomb

theorem exists_metricOpenRayPrefix_endpoint {X : Type*} [MetricSpace X] [CompleteSpace X]
    (p : MetricOpenRayPrefix X) (hp : 0 < p.duration) (hfin : p.duration ≠ ∞) :
    ∃ q : X, ∀ t : NNReal, (t : ℝ≥0∞) < p.duration →
      dist (p.curve t) q = dist t p.duration.toNNReal := by
  have hr : 0 < p.duration.toNNReal := ENNReal.toNNReal_pos hp.ne' hfin
  obtain ⟨u, _, hu, hlim⟩ := exists_seq_strictMono_tendsto' hr
  have hud (n : ℕ) : (u n : ℝ≥0∞) < p.duration := by
    rw [← ENNReal.coe_toNNReal hfin]
    exact ENNReal.coe_lt_coe.mpr (hu n).2
  have hc : CauchySeq (fun n ↦ p.curve (u n)) := by
    apply cauchySeq_iff_tendsto_dist_atTop_0.mpr
    have heq : (fun n : ℕ × ℕ ↦ dist (p.curve (u n.1)) (p.curve (u n.2))) =
        (fun n : ℕ × ℕ ↦ dist (u n.1) (u n.2)) :=
      funext (fun n ↦ p.metric _ _ (hud n.1) (hud n.2))
    rw [heq]
    exact cauchySeq_iff_tendsto_dist_atTop_0.mp hlim.cauchySeq
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hc
  refine ⟨q, ?_⟩
  intro t ht
  have hleft : Tendsto (fun n ↦ dist (p.curve t) (p.curve (u n))) atTop
      (𝓝 (dist (p.curve t) q)) := tendsto_const_nhds.dist hq
  have heq : (fun n ↦ dist (p.curve t) (p.curve (u n))) =
      (fun n ↦ dist t (u n)) := funext (fun n ↦ p.metric _ _ ht (hud n))
  rw [heq] at hleft
  exact tendsto_nhds_unique hleft (tendsto_const_nhds.dist hlim)

/-- Complete the same literal prefix to the closed interval, without choosing
or identifying any continuation beyond its endpoint. -/
theorem exists_metricOpenRayPrefix_closed_extension {X : Type*} [MetricSpace X] [CompleteSpace X]
    (p : MetricOpenRayPrefix X) (hp : 0 < p.duration) (hfin : p.duration ≠ ∞) :
    ∃ f : NNReal → X,
      (∀ t : NNReal, (t : ℝ≥0∞) < p.duration → f t = p.curve t) ∧
      ∀ s ≤ p.duration.toNNReal, ∀ t ≤ p.duration.toNNReal,
        dist (f s) (f t) = dist s t := by
  classical
  obtain ⟨q, hq⟩ := exists_metricOpenRayPrefix_endpoint p hp hfin
  let r := p.duration.toNNReal
  let f : NNReal → X := fun t ↦ if t < r then p.curve t else q
  have hlt (t : NNReal) : (t : ℝ≥0∞) < p.duration ↔ t < r := by
    rw [← ENNReal.coe_toNNReal hfin]
    exact ENNReal.coe_lt_coe
  refine ⟨f, fun t ht ↦ if_pos ((hlt t).mp ht), ?_⟩
  intro s hs t ht
  by_cases hsr : s < r
  · by_cases htr : t < r
    · simp only [f, if_pos hsr, if_pos htr]
      exact p.metric s t ((hlt s).mpr hsr) ((hlt t).mpr htr)
    · have he : t = r := le_antisymm ht (le_of_not_gt htr)
      simp only [f, if_pos hsr, if_neg htr]
      rw [he]
      exact hq s ((hlt s).mpr hsr)
  · have he : s = r := le_antisymm hs (le_of_not_gt hsr)
    by_cases htr : t < r
    · simp only [f, if_neg hsr, if_pos htr]
      rw [dist_comm, hq t ((hlt t).mpr htr), he, dist_comm]
    · have he' : t = r := le_antisymm ht (le_of_not_gt htr)
      simp only [f, if_neg hsr, if_neg htr, he, he', dist_self]

end RepulsiveCoulomb
