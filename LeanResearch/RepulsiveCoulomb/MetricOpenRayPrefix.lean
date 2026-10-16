import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Data.ENNReal.Real
import Mathlib.Order.Zorn

/-! Literal compatible extensions of open metric-ray prefixes. Curves may branch
after the same initial germ, so only an actual extension chain is glued. The
result is a maximal prefix, which can still have finite duration in a general
metric space. No geodesic-completeness or global-continuation conclusion is
assumed or asserted here. -/
noncomputable section
open Set
open scoped ENNReal
namespace RepulsiveCoulomb

/-- An isometric ray on the open initial time domain `t < duration`. Values of
the total curve outside that domain are ignored by the extension preorder. -/
structure MetricOpenRayPrefix (X : Type*) [MetricSpace X] where
  duration : ℝ≥0∞
  curve : NNReal → X
  metric : ∀ s t : NNReal, (s : ℝ≥0∞) < duration → (t : ℝ≥0∞) < duration →
    dist (curve s) (curve t) = dist s t

instance metricOpenRayPrefix_preorder {X : Type*} [MetricSpace X] :
    Preorder (MetricOpenRayPrefix X) where
  le p q := p.duration ≤ q.duration ∧
    ∀ t : NNReal, (t : ℝ≥0∞) < p.duration → p.curve t = q.curve t
  le_refl p := ⟨le_rfl, fun _ _ ↦ rfl⟩
  le_trans p q r hpq hqr :=
    ⟨hpq.1.trans hqr.1, fun t ht ↦ (hpq.2 t ht).trans (hqr.2 t (ht.trans_le hpq.1))⟩

/-- A nonempty chain has its actual compatible union, with duration the
supremum of its durations. No equality between unrelated extensions is used. -/
theorem exists_metricOpenRayPrefix_chain_upperBound {X : Type*} [MetricSpace X]
    (C : Set (MetricOpenRayPrefix X)) (hC : IsChain (· ≤ ·) C) (hne : C.Nonempty) :
    ∃ p : MetricOpenRayPrefix X, p.duration = ⨆ q : C, q.1.duration ∧ ∀ q ∈ C, q ≤ p := by
  classical
  let f : NNReal → X := fun t ↦
    if ht : ∃ q : C, (t : ℝ≥0∞) < q.1.duration then
      (Classical.choose ht).1.curve t else hne.some.curve 0
  have hf (p : MetricOpenRayPrefix X) (hp : p ∈ C) (t : NNReal)
      (ht : (t : ℝ≥0∞) < p.duration) : f t = p.curve t := by
    have hex : ∃ q : C, (t : ℝ≥0∞) < q.1.duration := ⟨⟨p, hp⟩, ht⟩
    dsimp only [f]
    rw [dif_pos hex]
    have hq := Classical.choose_spec hex
    rcases hC.total hp (Classical.choose hex).2 with hpq | hqp
    · exact (hpq.2 t ht).symm
    · exact hqp.2 t hq
  have hmetric : ∀ s t : NNReal,
      (s : ℝ≥0∞) < ⨆ q : C, q.1.duration →
      (t : ℝ≥0∞) < ⨆ q : C, q.1.duration → dist (f s) (f t) = dist s t := by
    intro s t hs ht
    obtain ⟨p, hp⟩ := lt_iSup_iff.mp hs
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp ht
    rcases hC.total p.2 q.2 with hpq | hqp
    · rw [hf q.1 q.2 s (hp.trans_le hpq.1), hf q.1 q.2 t hq]
      exact q.1.metric s t (hp.trans_le hpq.1) hq
    · rw [hf p.1 p.2 s hp, hf p.1 p.2 t (hq.trans_le hqp.1)]
      exact p.1.metric s t hp (hq.trans_le hqp.1)
  refine ⟨⟨⨆ q : C, q.1.duration, f, hmetric⟩, rfl, ?_⟩
  intro p hp
  exact ⟨le_iSup (fun q : C ↦ q.1.duration) ⟨p, hp⟩,
    fun t ht ↦ (hf p hp t ht).symm⟩

/-- Every supplied prefix has a maximal literal extension. This result alone
does not rule out finite duration. -/
theorem exists_maximal_metricOpenRayPrefix {X : Type*} [MetricSpace X]
    (seed : MetricOpenRayPrefix X) :
    ∃ p : MetricOpenRayPrefix X, seed ≤ p ∧ IsMax p := by
  apply zorn_le_nonempty_Ici₀ seed _ seed le_rfl
  intro C _ hC q hq
  obtain ⟨p, _, hp⟩ := exists_metricOpenRayPrefix_chain_upperBound C hC ⟨q, hq⟩
  exact ⟨p, hp⟩

theorem metricOpenRayPrefix_isometry_of_duration_top {X : Type*} [MetricSpace X]
    (p : MetricOpenRayPrefix X) (hp : p.duration = ∞) : Isometry p.curve := by
  apply Isometry.of_dist_eq
  intro s t
  exact p.metric s t (by rw [hp]; exact ENNReal.coe_lt_top) (by rw [hp]; exact ENNReal.coe_lt_top)

end RepulsiveCoulomb
