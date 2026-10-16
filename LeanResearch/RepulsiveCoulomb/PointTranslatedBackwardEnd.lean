module

public import LeanResearch.RepulsiveCoulomb.CompactEdgeRayJoin
public import LeanResearch.RepulsiveCoulomb.MetricTranslatedStageEdgeAvoidance
public import LeanResearch.RepulsiveCoulomb.PointMetricRaySegments

@[expose] public section

/-! SOURCE-ONLY ASSEMBLY. Construct the proper backward old end, its exact
carrier, the removed original positive corner, and avoidance by every positive
parallel-row point. All geometric inputs are original edges and one actual
finite flat rectangle. No whole strip or cap endpoint avoidance is assumed. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem point_exists_translated_backward_end
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {stripAngle R s : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi) (hR : 0 < R) (hs : 0 < s)
    (ρ : NNReal → P)
    (hρ : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (hρfront : ∀ t, (ρ t).1 ∈ frontier P)
    (edge : Icc (0 : ℝ) s → P)
    (hedge : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace edge)
    (hedgefront : ∀ u, (edge u).1 ∈ frontier P)
    (f : flatShearedRectangle (conePhase stripAngle) R s → P)
    (hf : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (hbottom : ∀ r : Icc (0 : ℝ) R, f (shearedBottomPoint hs.le r) = ρ ⟨r.1, r.2.1⟩)
    (hold : ∀ u : Icc (0 : ℝ) s, f (shearedCompactEdgePoint hR.le u) = edge u) :
    ∃ δ : NNReal → ℂ, IsClosedEmbedding δ ∧
      δ 0 = (edge ⟨s, hs.le, le_rfl⟩).1 ∧
      δ ⟨s, hs.le⟩ = (ρ 0).1 ∧
      range δ = range (fun u ↦ (edge u).1) ∪ range (fun t ↦ (ρ t).1) ∧
      (∀ t, δ t ∈ frontier P) ∧
      (∀ t : NNReal, ∀ ht : t.1 ≤ s,
        δ t = (edge ⟨s-t.1, sub_nonneg.mpr ht, sub_le_self _ t.2⟩).1) ∧
      ∀ r : Icc (0 : ℝ) R, 0 < r.1 →
        (f (shearedTopPoint (conePhase stripAngle) R s hs.le r)).1 ∉ range δ := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let e : Icc (0 : ℝ) s → ℂ := fun u ↦ (edge u).1
  let ray : NNReal → ℂ := fun t ↦ (ρ t).1
  have hecont : Continuous e := by
    have hc : @Continuous (Icc (0 : ℝ) s) P _ M.toUniformSpace.toTopologicalSpace edge := hedge.continuous
    change @Continuous (Icc (0 : ℝ) s) P _
      (pointRegionMetricSpace ha y P).toUniformSpace.toTopologicalSpace edge at hc
    rw [pointRegionMetricSpace_topology ha y P] at hc
    exact continuous_subtype_val.comp hc
  have hei : Function.Injective e := by
    intro u v h
    exact hedge.injective (Subtype.ext h)
  have hray : IsClosedEmbedding ray := pointMetricRay_isClosedEmbedding ha y ray
    (fun r t ↦ hρ.dist_eq r t)
  have hzero : edge ⟨0, le_rfl, hs.le⟩ = ρ 0 := by
    rw [← hold ⟨0, le_rfl, hs.le⟩]
    exact hbottom ⟨0, le_rfl, hR.le⟩
  have hzero' : e ⟨0, le_rfl, hs.le⟩ = ray 0 := congrArg Subtype.val hzero
  have hmeet : range e ∩ range ray = {ray 0} := by
    ext p
    constructor
    · rintro ⟨⟨u, hup⟩, ⟨t, htp⟩⟩
      by_cases hu : u.1 = 0
      · have hu0 : u = ⟨0, le_rfl, hs.le⟩ := Subtype.ext hu
        exact mem_singleton_iff.mpr (hup.symm.trans (by simpa only [hu0] using hzero'))
      · have hupos : 0 < u.1 := lt_of_le_of_ne u.2.1 (Ne.symm hu)
        have hno := metric_translated_stage_avoids_bottom stripAngle_pos stripAngle_lt_pi hR hs.le ρ hρ f hf hbottom
          (⟨0, le_rfl, hR.le⟩ : Icc (0 : ℝ) R) u hupos
        exfalso
        apply hno
        refine ⟨t, ?_⟩
        change ρ t = f (shearedCompactEdgePoint hR.le u)
        rw [hold]
        apply Subtype.ext
        exact htp.trans hup.symm
    · intro hp
      have heq := mem_singleton_iff.mp hp
      rw [heq]
      exact ⟨⟨⟨0, le_rfl, hs.le⟩, hzero'⟩, mem_range_self 0⟩
  let δ := compactEdgeRayJoin hs.le e ray
  have hδ := compactEdgeRayJoin_isClosedEmbedding hs.le hecont hei hray hzero' hmeet
  have hrange : range δ = range e ∪ range ray := by
    have hi := compactEdgeRayJoin_image hs.le e ray hzero' univ
    change compactEdgeRayJoin hs.le e ray '' univ = e '' univ ∪ ray '' univ at hi
    simpa only [δ, image_univ] using hi
  have hδ0 : δ 0 = e ⟨s, hs.le, le_rfl⟩ := by
    exact (compactEdgeRayJoin_before hs.le e ray 0 hs.le).trans
      (congrArg e (Subtype.ext (by change s - 0 = s; exact sub_zero s)))
  have hδs : δ ⟨s, hs.le⟩ = ray 0 := by
    exact (compactEdgeRayJoin_after hs.le e ray hzero' (⟨s, hs.le⟩ : NNReal) le_rfl).trans
      (congrArg ray (Subtype.ext (by change s - s = 0; exact sub_self s)))
  refine ⟨δ, hδ, hδ0, hδs, hrange, ?_, ?_, ?_⟩
  · intro t
    have ht : δ t ∈ range e ∪ range ray := hrange ▸ mem_range_self t
    rcases ht with ⟨u, hu⟩ | ⟨u, hu⟩
    · exact hu ▸ hedgefront u
    · exact hu ▸ hρfront u
  · exact fun t ht ↦ compactEdgeRayJoin_before hs.le e ray t ht
  · intro r hr
    rw [hrange]
    rintro (⟨u, hu⟩ | ⟨t, ht⟩)
    · have hno := metric_translated_stage_avoids_compact_edge stripAngle_pos stripAngle_lt_pi hR.le hs
        edge hedge f hf hold r hr (⟨s, hs.le, le_rfl⟩ : Icc (0 : ℝ) s)
      exact hno ⟨u, Subtype.ext hu⟩
    · have hno := metric_translated_stage_avoids_bottom stripAngle_pos stripAngle_lt_pi hR hs.le
        ρ hρ f hf hbottom r (⟨s, hs.le, le_rfl⟩ : Icc (0 : ℝ) s) hs
      exact hno ⟨t, Subtype.ext ht⟩

end RepulsiveCoulomb
