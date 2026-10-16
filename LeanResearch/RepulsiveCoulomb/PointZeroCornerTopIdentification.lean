import LeanResearch.RepulsiveCoulomb.PointCleanBoundaryRayNonbranching
import LeanResearch.RepulsiveCoulomb.PointTranslatedContactAngle

/-!
SOURCE-ONLY, UNCOMPILED. At a zero-residual corner, the actual top is the
actual clean forward old-boundary ray. The forward ray is geometric input
from the separate outermost-end constructor; its matching with the top is a
conclusion. No exact-contact or whole-region-exhaustion premise is used.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} {D : PointTranslatedRegularData a y ha P ν α}
  (T : D.FiniteWidthLimit)

/-- Opposite-end disjointness is literal boundary geometry: positive points
of the forward end are outside the old bottom and compact edge. Local fullness
at the attained origin forces their strip preimages onto the free top. Actual
distances identify their clocks, after which relative nonbranching gives the
whole-ray equality. -/
theorem top_eq_clean_forward_of_zero_corner
    (C : PointRetainedConeNeighborhood a y P
      (T.map (translatedStripTop T.positive.le 0)).1) (hC : C.Admissible)
    (hzero : C.flatPhysicalWidth = Real.pi - D.angle)
    (g : NNReal → P)
    (hg : @Isometry NNReal P inferInstance
      (pointRegionMetricSpace ha y P).toPseudoEMetricSpace g)
    (hg0 : g 0 = T.map (translatedStripTop T.positive.le 0))
    (hfront : ∀ t, (g t).1 ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {(g 0).1})
      (range (fun t ↦ (g t).1)))
    (hforward : ∀ t : NNReal, 0 < t →
      (g t).1 ∉ range (fun r ↦ (T.map (translatedStripBottom T.positive.le r)).1) ∪
        range (fun u ↦ (T.map (translatedStripEdge u)).1)) :
    (fun r ↦ T.map (translatedStripTop T.positive.le r)) = g := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let τ : NNReal → P := fun r ↦ T.map (translatedStripTop T.positive.le r)
  have hτ : Isometry τ := T.metric.comp (translatedStripTop_isometry T.positive.le)
  obtain ⟨ε, hε, hfill⟩ := (pointTranslatedStrip_corner_width_and_equality_fullness
    ha y D.angle_pos D.angle_lt_pi T.positive T.map
    (fun x z ↦ T.metric.dist_eq x z) T.edge_frontier C hC).2 hzero
  have hseed : ∀ t : NNReal, t.1 ≤ ε → τ t = g t := by
    intro t htε
    by_cases ht0 : t = 0
    · subst t
      exact hg0.symm
    · have ht : 0 < (t : ℝ) :=
        lt_of_le_of_ne t.2 (fun he ↦ ht0 (Subtype.ext he.symm))
      have hdist : (pointSmoothConformalEDist a y (g t).1
          (T.map (translatedStripTop T.positive.le 0)).1).toReal ≤ ε := by
        change dist (g t) (T.map (translatedStripTop T.positive.le 0)) ≤ ε
        rw [← hg0, hg.dist_eq]
        change |t.1 - 0| ≤ ε
        rw [sub_zero, abs_of_nonneg t.2]
        exact htε
      obtain ⟨q, hq⟩ := hfill (g t).1 (g t).2 hdist
      have hqsub : T.map q = g t := Subtype.ext hq
      obtain ⟨r, hr, u, hu, hqu⟩ := q.2
      have hrpos : 0 < r := by
        apply lt_of_le_of_ne hr
        intro he
        have hqe : q = translatedStripEdge (⟨u, hu⟩ : Icc (0 : ℝ) (sSup D.regularWidths)) := by
          apply Subtype.ext
          change q.1 = flatShearedPoint (conePhase D.angle) 0 u
          simpa only [← he] using hqu
        apply hforward t ht
        right
        exact ⟨⟨u, hu⟩, (congrArg (fun w ↦ (T.map w).1) hqe.symm).trans hq⟩
      have hupos : 0 < u := by
        apply lt_of_le_of_ne hu.1
        intro he
        have hqb : q = translatedStripBottom T.positive.le (⟨r, hr⟩ : NNReal) := by
          apply Subtype.ext
          change q.1 = flatShearedPoint (conePhase D.angle) r 0
          simpa only [← he] using hqu
        apply hforward t ht
        left
        exact ⟨⟨r, hr⟩, (congrArg (fun w ↦ (T.map w).1) hqb.symm).trans hq⟩
      have hub : u = sSup D.regularWidths := by
        by_contra hn
        have hlt : u < sSup D.regularWidths := lt_of_le_of_ne hu.2 hn
        have hqe : q = ⟨flatShearedPoint (conePhase D.angle) r u,
            r, hr, u, hu, rfl⟩ := Subtype.ext hqu
        have hi := T.below_positive_interior ⟨r, hr⟩ hrpos ⟨u, hu⟩ hupos hlt
        have hiq : (T.map q).1 ∈ interior P := hqe.symm ▸ hi
        exact (hfront t).2 (hq ▸ hiq)
      have hqt : q = translatedStripTop T.positive.le (⟨r, hr⟩ : NNReal) := by
        apply Subtype.ext
        change q.1 = flatShearedPoint (conePhase D.angle) r (sSup D.regularWidths)
        simpa only [hub] using hqu
      have he : τ (⟨r, hr⟩ : NNReal) = g t :=
        (congrArg T.map hqt.symm).trans hqsub
      have hrclock : (⟨r, hr⟩ : NNReal) = t := by
        apply Subtype.ext
        have hd : dist (⟨r, hr⟩ : NNReal) 0 = dist t 0 := by
          calc
            dist (⟨r, hr⟩ : NNReal) 0 = dist (τ ⟨r, hr⟩) (τ 0) :=
              (hτ.dist_eq _ _).symm
            _ = dist (g t) (g 0) := by rw [he, hg0]
            _ = dist t 0 := hg.dist_eq _ _
        change |r - 0| = |t.1 - 0| at hd
        rw [sub_zero, sub_zero, abs_of_nonneg hr, abs_of_nonneg t.2] at hd
        exact hd
      exact hrclock ▸ he
  exact pointCleanBoundaryRay_eq_of_positive_prefix ha y D.boundary_formula
    τ g hτ hg hfront hclean hε hseed

end RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
