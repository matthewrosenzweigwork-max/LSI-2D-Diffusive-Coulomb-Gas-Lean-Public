module

public import LeanResearch.RepulsiveCoulomb.PointZeroCornerTopIdentification
public import LeanResearch.RepulsiveCoulomb.PointTranslatedTopBoundaryFullness
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripRelativeFullness

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED. In the zero-corner case, an actual entire top on the
old frontier forces whole-region exhaustion. Relative openness below the top
comes from earlier actual regular stages; at the top it is derived from exact
local source sectors. Neither exhaustion nor image openness is assumed.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} {D : PointTranslatedRegularData a y ha P ν α}
  (T : D.FiniteWidthLimit)

theorem surjective_of_zero_corner_and_boundary_top
    (C : PointRetainedConeNeighborhood a y P
      (T.map (translatedStripTop T.positive.le 0)).1) (hC : C.Admissible)
    (hzero : C.flatPhysicalWidth = Real.pi - D.angle)
    (htop : ∀ r : NNReal, (T.map (translatedStripTop T.positive.le r)).1 ∈ frontier P) :
    Function.Surjective T.map := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  letI : UniformSpace P := M.toUniformSpace
  letI : TopologicalSpace P := M.toUniformSpace.toTopologicalSpace
  have hc : IsClosed (range T.map) :=
    (flatShearedStrip_isometry_closed_proper D.direction_im_ne_zero T.metric).1.isClosed_range
  have ho : IsOpen (range T.map) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro p ⟨q, rfl⟩
    obtain ⟨r, hr, u, hu, hqu⟩ := q.2
    by_cases hub : u < sSup D.regularWidths
    · obtain ⟨s, hs, hus⟩ := exists_lt_of_lt_csSup D.regularWidths_nonempty hub
      obtain ⟨U⟩ := hs
      have hsb : s ≤ sSup D.regularWidths := le_csSup T.bounded (show s ∈ D.regularWidths from ⟨U⟩)
      let qs : flatShearedStrip (conePhase D.angle) s :=
        ⟨flatShearedPoint (conePhase D.angle) r u, r, hr, u, ⟨hu.1, hus.le⟩, rfl⟩
      have hqeq : q = ⟨qs.1, flatShearedStrip_mono hsb qs.2⟩ := Subtype.ext hqu
      have hTq : T.map q = U.map qs := by
        rw [hqeq]
        exact T.extends_stage U qs
      let A : Set P := {p | p.1 ∈ range (fun w ↦ (U.map w).1) \
        range (fun t ↦ (U.map (translatedStripTop U.positive.le t)).1)}
      have hAo : IsOpen A := by
        change @IsOpen P M.toUniformSpace.toTopologicalSpace A
        rw [pointRegionMetricSpace_topology ha y P]
        apply pointTranslatedStrip_without_top_relatively_open ha y D.angle_pos D.angle_lt_pi
          U.positive U.map (fun x z ↦ U.metric.dist_eq x z) U.exact_contact
        · intro x hx
          obtain ⟨E, hE, _⟩ := D.boundary_coeff x hx
          exact ⟨E, hE⟩
        · intro x hxI hxS
          have hxp : x ≠ (D.ray 0).1 := fun he ↦ (D.ray_frontier 0).2 (he ▸ hxI)
          have hm : x ∉ pointSignedMarked ν α := by
            intro hm
            obtain ⟨w, hw⟩ := hxS.1
            change (U.map w).1 = x at hw
            apply U.unmarked w
            rw [hw]
            exact ⟨hm, hxp⟩
          by_contra hn
          exact hm (D.interior_marked x hxI hn)
      have hqA : T.map q ∈ A := by
        rw [hTq]
        refine ⟨mem_range_self qs, ?_⟩
        intro ht
        have he := (translatedStrip_image_mem_top_iff D.direction_im_ne_zero U.positive.le
          U.closed_proper.1.injective qs hr rfl).mp ht
        exact hus.ne he
      have hAT : A ⊆ range T.map := by
        intro x hx
        obtain ⟨w, hw⟩ := hx.1
        exact ⟨⟨w.1, flatShearedStrip_mono hsb w.2⟩,
          (T.extends_stage U w).trans (Subtype.ext hw)⟩
      exact Filter.mem_of_superset (hAo.mem_nhds hqA) hAT
    · have hueq : u = sSup D.regularWidths := le_antisymm hu.2 (le_of_not_gt hub)
      let t : NNReal := ⟨r, hr⟩
      have hqt : q = translatedStripTop T.positive.le t := by
        apply Subtype.ext
        change q.1 = flatShearedPoint (conePhase D.angle) r (sSup D.regularWidths)
        simpa only [hueq] using hqu
      have hfill : ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ P,
          (pointSmoothConformalEDist a y z (T.map q).1).toReal ≤ ε →
            z ∈ range (fun w ↦ (T.map w).1) := by
        rw [hqt]
        by_cases ht0 : t = 0
        · rw [ht0]
          exact (pointTranslatedStrip_corner_width_and_equality_fullness ha y
            D.angle_pos D.angle_lt_pi T.positive T.map (fun x z ↦ T.metric.dist_eq x z)
            T.edge_frontier C hC).2 hzero
        · have ht : 0 < t := lt_of_le_of_ne (show (0 : NNReal) ≤ t from t.2) (Ne.symm ht0)
          obtain ⟨E, hE, _⟩ := D.boundary_coeff _ (htop t)
          exact (pointTranslatedStrip_top_boundary_local_fullness ha y
            D.angle_pos D.angle_lt_pi T.positive T.map (fun x z ↦ T.metric.dist_eq x z)
            htop t ht E hE).2
      obtain ⟨ε, hε, hfill⟩ := hfill
      apply Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hε))
      intro x hx
      obtain ⟨w, hw⟩ := hfill x.1 x.2 (show dist x (T.map q) ≤ ε from hx.le)
      exact ⟨w, Subtype.ext hw⟩
  have hpre : @PreconnectedSpace P M.toUniformSpace.toTopologicalSpace := by
    rw [pointRegionMetricSpace_topology ha y P]
    exact isPreconnected_iff_preconnectedSpace.mp D.connected.isPreconnected
  letI : PreconnectedSpace P := hpre
  have hne : (range T.map).Nonempty :=
    ⟨T.map (translatedStripBottom T.positive.le 0), mem_range_self _⟩
  have hall : range T.map = univ := (show IsClopen (range T.map) from ⟨hc, ho⟩).eq_univ hne
  intro p
  exact (show p ∈ range T.map from by rw [hall]; trivial)

end RepulsiveCoulomb.PointTranslatedRegularData.FiniteWidthLimit
