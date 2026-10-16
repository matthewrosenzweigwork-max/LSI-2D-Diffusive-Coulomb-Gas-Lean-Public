import LeanResearch.RepulsiveCoulomb.DevelopedPathMetric
import LeanResearch.RepulsiveCoulomb.MetricMidpointGeodesic
import Mathlib.Topology.MetricSpace.ProperSpace

/-! SOURCE-ONLY, UNCOMPILED. Topology, properness, completeness, and NEW
minimizing segments are derived for the actual developed path infimum.
No one of these conclusions is an input. -/
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RepulsiveCoulomb
variable {X : Type*} [MetricSpace X]
variable (D : X → ℂ) (hD : Continuous D) (c : ℝ≥0) (hc : 0 < c)
  (hsegment : HasMinimizingSegments X)
  (hlower : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ u ∈ U, ∀ v ∈ U, (c : ℝ≥0∞) * edist u v ≤ edist (D u) (D v))
  (hupper : ∀ x, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
    ∀ u ∈ U, ∀ v ∈ U, dist (D u) (D v) ≤ dist u v)

include hsegment hupper in
 theorem developedPathEDist_ne_top (x z : X) : developedPathEDist D x z ≠ ⊤ :=
  ne_top_of_le_ne_top (edist_ne_top x z) (developedPathEDist_le_edist D hsegment hupper x z)

include hsegment hlower hupper in
 theorem developedPathEDist_toReal_bounds (x z : X) :
    (c : ℝ) * dist x z ≤ (developedPathEDist D x z).toReal ∧
      (developedPathEDist D x z).toReal ≤ dist x z := by
  constructor
  · have h := ENNReal.toReal_mono (developedPathEDist_ne_top D hsegment hupper x z)
      (local_lower_le_developedPathEDist D c hlower x z)
    simpa only [ENNReal.toReal_mul, ENNReal.coe_toReal, ← dist_edist] using h
  · simpa only [← dist_edist] using ENNReal.toReal_mono (edist_ne_top x z)
      (developedPathEDist_le_edist D hsegment hupper x z)

theorem developedPathMetricSpace_topology :
    (developedPathMetricSpace D hD c hc hsegment hlower hupper).toUniformSpace.toTopologicalSpace =
      (inferInstance : TopologicalSpace X) := by
  let oldMetric : MetricSpace X := inferInstance
  let d := @developedPathMetricSpace X oldMetric D hD c hc hsegment hlower hupper
  letI : MetricSpace X := oldMetric
  have hcR : 0 < (c : ℝ) := hc
  have hforward : @Continuous X X d.toUniformSpace.toTopologicalSpace
      oldMetric.toUniformSpace.toTopologicalSpace id := by
    apply (@Metric.continuous_iff X X d.toPseudoMetricSpace oldMetric.toPseudoMetricSpace id).mpr
    intro x ε hε
    refine ⟨(c : ℝ) * ε, mul_pos hcR hε, ?_⟩
    intro z hz
    have hl := (developedPathEDist_toReal_bounds D c hsegment hlower hupper z x).1
    change (developedPathEDist D z x).toReal < (c : ℝ) * ε at hz
    change dist z x < ε
    nlinarith
  have hbackward : @Continuous X X oldMetric.toUniformSpace.toTopologicalSpace
      d.toUniformSpace.toTopologicalSpace id := by
    apply (@Metric.continuous_iff X X oldMetric.toPseudoMetricSpace d.toPseudoMetricSpace id).mpr
    intro x ε hε
    refine ⟨ε, hε, ?_⟩
    intro z hz
    exact (developedPathEDist_toReal_bounds D c hsegment hlower hupper z x).2.trans_lt hz
  exact le_antisymm (continuous_id_iff_le.mp hforward) (continuous_id_iff_le.mp hbackward)

theorem developedPathMetricSpace_proper [ProperSpace X] :
    @ProperSpace X (developedPathMetricSpace D hD c hc hsegment hlower hupper).toPseudoMetricSpace := by
  let oldMetric : MetricSpace X := inferInstance
  let d := @developedPathMetricSpace X oldMetric D hD c hc hsegment hlower hupper
  letI : MetricSpace X := oldMetric
  refine @ProperSpace.mk X d.toPseudoMetricSpace ?_
  intro x r
  let S := {z : X | (developedPathEDist D z x).toReal ≤ r}
  have hS : IsClosed S := by
    have h := @isClosed_closedBall X d.toPseudoMetricSpace x r
    change @IsClosed X
      (developedPathMetricSpace D hD c hc hsegment hlower hupper).toUniformSpace.toTopologicalSpace S at h
    rwa [developedPathMetricSpace_topology] at h
  change @IsCompact X
    (developedPathMetricSpace D hD c hc hsegment hlower hupper).toUniformSpace.toTopologicalSpace S
  rw [developedPathMetricSpace_topology]
  apply (isCompact_closedBall x (r / (c : ℝ))).of_isClosed_subset hS
  intro z hz
  rw [mem_closedBall]
  apply (le_div_iff₀ (show 0 < (c : ℝ) from hc)).mpr
  have hl := (developedPathEDist_toReal_bounds D c hsegment hlower hupper z x).1
  change (developedPathEDist D z x).toReal ≤ r at hz
  nlinarith

theorem developedPathMetricSpace_complete [ProperSpace X] :
    @CompleteSpace X (developedPathMetricSpace D hD c hc hsegment hlower hupper).toUniformSpace :=
  @complete_of_proper X
    (developedPathMetricSpace D hD c hc hsegment hlower hupper).toPseudoMetricSpace
    (developedPathMetricSpace_proper D hD c hc hsegment hlower hupper)

include hD hsegment hupper in
 theorem developedPathEDist_approximate_midpoint (x z : X) (r : ℝ)
    (hr : (developedPathEDist D x z).toReal / 2 < r) :
    ∃ p : X, (developedPathEDist D x p).toReal < r ∧
      (developedPathEDist D p z).toReal < r := by
  have hDfin := developedPathEDist_ne_top D hsegment hupper x z
  have hr0 : 0 < r := lt_of_le_of_lt (by positivity) hr
  have hDr : developedPathEDist D x z < ENNReal.ofReal (2 * r) := by
    rw [← ENNReal.ofReal_toReal hDfin]
    apply ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.mpr
    linarith
  obtain ⟨γ, hγ⟩ := iInf_lt_iff.mp hDr
  have hγfin : developedPathLength D γ ≠ ⊤ := ne_top_of_lt (hγ.trans_le le_top)
  have hγr : (developedPathLength D γ).toReal < 2 * r :=
    ((ENNReal.toReal_lt_toReal hγfin ENNReal.ofReal_ne_top).mpr hγ).trans_eq
      (ENNReal.toReal_ofReal (by positivity))
  obtain ⟨t, ht, hleft, hright⟩ := (γ.developed D hD).exists_length_bisection hγfin
  have hLfin : eVariationOn (D ∘ γ.toFun) (Icc (0 : ℝ) t) ≠ ⊤ :=
    ne_top_of_le_ne_top hγfin (eVariationOn.mono _ (Icc_subset_Icc le_rfl ht.2))
  have hRfin : eVariationOn (D ∘ γ.toFun) (Icc t (1 : ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hγfin (eVariationOn.mono _ (Icc_subset_Icc ht.1 le_rfl))
  have hL := developedPathEDist_le_length D (γ.subpath 0 t (by norm_num) ht)
  rw [developedPathLength_subpath, uIcc_of_le ht.1, γ.source] at hL
  have hR := developedPathEDist_le_length D (γ.subpath t 1 ht (by norm_num))
  rw [developedPathLength_subpath, uIcc_of_le ht.2, γ.target] at hR
  have hL' := ENNReal.toReal_mono hLfin hL
  have hR' := ENNReal.toReal_mono hRfin hR
  change (eVariationOn (D ∘ γ.toFun) (Icc 0 t)).toReal =
    (developedPathLength D γ).toReal / 2 at hleft
  change (eVariationOn (D ∘ γ.toFun) (Icc t 1)).toReal =
    (developedPathLength D γ).toReal / 2 at hright
  rw [hleft] at hL'
  rw [hright] at hR'
  exact ⟨γ.toFun t, by linarith, by linarith⟩

/-- Properness plus variation bisection produces actual minimizing segments
for the NEW metric. The old geodesics alone do not serve as new minimizers. -/
theorem developedPathMetricSpace_hasMinimizingSegments [ProperSpace X] :
    @HasMinimizingSegments X (developedPathMetricSpace D hD c hc hsegment hlower hupper) := by
  let oldMetric : MetricSpace X := inferInstance
  let d := @developedPathMetricSpace X oldMetric D hD c hc hsegment hlower hupper
  letI : MetricSpace X := oldMetric
  have hp := developedPathMetricSpace_proper D hD c hc hsegment hlower hupper
  have hcomplete := developedPathMetricSpace_complete D hD c hc hsegment hlower hupper
  have hmid : ∀ x z : X, ∃ p,
      @dist X d.toDist x p = @dist X d.toDist x z / 2 ∧
      @dist X d.toDist p z = @dist X d.toDist x z / 2 :=
    @proper_exists_midpoint_of_approximate X d hp
      (fun x z r hr ↦ developedPathEDist_approximate_midpoint D hD hsegment hupper x z r hr)
  exact @exists_geodesic_of_exact_midpoints X d hcomplete hmid

end RepulsiveCoulomb
