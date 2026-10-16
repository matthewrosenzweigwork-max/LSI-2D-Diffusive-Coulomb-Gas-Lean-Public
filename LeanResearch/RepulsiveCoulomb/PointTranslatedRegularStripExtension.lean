module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedRegularStages
public import LeanResearch.RepulsiveCoulomb.PointTranslatedResidualFiniteBoundary
public import LeanResearch.RepulsiveCoulomb.PointTranslatedStripActualResidualGluing

@[expose] public section

/-! SOURCE ONLY, UNCOMPILED. A regular actual whole strip extends to a strictly
wider regular actual whole strip. The literal residual, its signed state, its
finite geodesic-piece frontier cover, its clean complete top ray and its
positive corner are constructed from the old stage. The next strip is produced
by the original positive-corner theorem and glued by the actual seam theorem.
There is no extension oracle, compatible development or new Stage premise.

The transferred marked set may contain the seam origin and lose the old apex.
The support argument below therefore transfers avoidance point by point; it
does not identify the old and new marked sets. All alpha data are unchanged.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- Support transfer used after the actual residual is built. The new apex is
allowed by the new strip, but was unmarked in the old state; the old apex is
absent from the literal residual. Away from both, curvature is unchanged. -/
theorem pointTransferredStrip_avoids_original_marks
    {X : Type*} {Q : Set ℂ} {ν α : ℂ →₀ ℝ} {p z : ℂ}
    (hpQ : p ∉ Q) (hνz : ν z = 0) (hαz : α z = 0)
    (G : X → Q)
    (hG : ∀ x, (G x).1 ∉
      (↑(pointSignedMarked (BoundaryPreparation.transfer ν p z) α) : Set ℂ) \ {z}) :
    ∀ x, (G x).1 ∉ pointSignedMarked ν α := by
  intro x hx
  by_cases hxz : (G x).1 = z
  · rcases (mem_pointSignedMarked ν α _).mp hx with hν | hα
    · exact hν (by simpa only [hxz] using hνz)
    · exact hα (by simpa only [hxz] using hαz)
  · have hxp : (G x).1 ≠ p := fun he ↦ hpQ (he ▸ (G x).2)
    have he := BoundaryPreparation.transfer_away ν hxp hxz
    apply hG x
    refine ⟨?_, hxz⟩
    rcases (mem_pointSignedMarked ν α _).mp hx with hν | hα
    · exact (mem_pointSignedMarked _ α _).mpr (Or.inl (by rwa [he]))
    · exact (mem_pointSignedMarked _ α _).mpr (Or.inr hα)

namespace PointTranslatedRegularData.Stage
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} {D : PointTranslatedRegularData a y ha P ν α}
  {s : ℝ}

/-- The complete old top, including its origin, is distinct from the old apex.
The proof uses the actual whole-strip isometry and literal source geometry. -/
theorem top_ne_apex (T : D.Stage s) (r : NNReal) :
    (T.map (translatedStripTop T.positive.le r)).1 ≠ (D.ray 0).1 := by
  intro he
  have hb := congrArg Subtype.val (T.bottom 0)
  exact translatedStrip_bottom_not_top D.direction_im_ne_zero T.positive
    T.closed_proper.1.injective 0 ⟨r, he.trans hb.symm⟩

/-- Regularity forbids both kinds of marks at every point of the old top.
No assumption that a residual top remains clean is used. -/
theorem top_coeff_zero (T : D.Stage s) (r : NNReal) :
    ν (T.map (translatedStripTop T.positive.le r)).1 = 0 ∧
      α (T.map (translatedStripTop T.positive.le r)).1 = 0 := by
  apply pointSigned_eq_zero_off_marked
  intro hm
  exact T.unmarked _ ⟨hm, T.top_ne_apex r⟩

/-- Actual residual geometry, the original uniform-strip producer, and actual
all-pairs seam gluing construct the extension and retain the entire old map. -/
theorem exists_wider_with_extension (T : D.Stage s) :
    ∃ h : ℝ, ∃ hh : 0 < h, ∃ U : D.Stage (s + h),
      ∀ q : flatShearedStrip (conePhase D.angle) s,
        U.map (translatedStripLowerInclusion hh.le q) = T.map q := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let S : Set ℂ := range (fun q ↦ (T.map q).1)
  let τ : NNReal → ℂ := fun r ↦ (T.map (translatedStripTop T.positive.le r)).1
  let Q : Set ℂ := closure (P \ S)
  let p : ℂ := (T.map (translatedStripBottom T.positive.le 0)).1
  let μ : ℂ →₀ ℝ := BoundaryPreparation.transfer ν p (τ 0)
  have hp : p = (D.ray 0).1 := congrArg Subtype.val (T.bottom 0)
  have hτnep (r : NNReal) : τ r ≠ p := by
    intro he
    exact T.top_ne_apex r (he.trans hp)
  have hτzero (r : NNReal) : ν (τ r) = 0 ∧ α (τ r) = 0 := T.top_coeff_zero r
  have hτ0front : τ 0 ∈ frontier P := by
    have he : translatedStripTop (v := conePhase D.angle) T.positive.le 0 =
        translatedStripEdge ⟨s, T.positive.le, le_rfl⟩ := Subtype.ext rfl
    change (T.map (translatedStripTop T.positive.le 0)).1 ∈ frontier P
    rw [he]
    exact T.edge_frontier ⟨s, T.positive.le, le_rfl⟩
  obtain ⟨Cz, hCz, hνz⟩ := D.boundary_coeff (τ 0) hτ0front
  have hCzwidth : Cz.flatPhysicalWidth = Real.pi := by
    have hz := (hτzero 0).1
    linarith
  have hremain : Real.pi - D.angle < Cz.flatPhysicalWidth := by
    rw [hCzwidth]
    linarith [D.angle_pos]
  have hαp : α p = 0 := by rw [hp]; exact D.apex_budget_zero
  have hclean : ∀ x ∈ S \ range τ, x ≠ p → ν x = 0 ∧ α x = 0 := by
    intro x hx hxp
    obtain ⟨q, rfl⟩ := hx.1
    apply pointSigned_eq_zero_off_marked
    intro hm
    exact T.unmarked q ⟨hm, fun he ↦ hxp (he.trans hp.symm)⟩
  have hF : ∀ x z, (pointSmoothConformalEDist a y (T.map x).1 (T.map z).1).toReal =
      dist x z := fun x z ↦ T.metric.dist_eq x z
  obtain ⟨⟨K⟩, hbottom_removed, hedge_removed⟩ :=
    pointTranslatedStrip_actual_iteration_output ha y D.ambient D.region_eq
      D.angle_pos D.angle_lt_pi T.positive T.map hF T.exact_contact ν α
      D.interior_coeff D.boundary_coeff D.exterior_coeff Cz hCz hνz hremain
      D.allocation_support hαp hclean
  -- K is the produced state of the literal closure(P \ range T.map).
  change PointTranslatedStripIterationOutput a y P S Q τ p ν μ α
    (Real.pi - D.angle) Cz at K
  obtain ⟨C, hchart, hwidth, hCadm, hμcorner⟩ := K.corner_chart
  have hCwidth : C.flatPhysicalWidth = D.angle := by
    rw [hwidth, hCzwidth]
    ring
  have hCpi : C.flatPhysicalWidth < Real.pi := by rw [hCwidth]; exact D.angle_lt_pi
  have hcorner_turn : μ (τ 0) = Real.pi - D.angle := by
    rw [hμcorner, hCwidth]
  have hcorner_turn_pos : 0 < μ (τ 0) := by
    rw [hcorner_turn]
    exact sub_pos.mpr D.angle_lt_pi
  have hbudget : PointSignedBudgetInvariant μ α := K.budget_invariant D.budget
  obtain ⟨pieces, hpieces⟩ := K.exists_finite_boundary_cover ha
    D.toPointRetainedSignedHalfplaneState.isClosed D.pieces D.boundary_cover
  let ρ : NNReal → Q := fun r ↦
    ⟨τ r, K.state.isClosed.frontier_subset (K.top_frontier (mem_range_self r))⟩
  have hρ : @Isometry NNReal Q inferInstance
      (pointRegionMetricSpace ha y Q).toPseudoEMetricSpace ρ := by
    let MQ := pointRegionMetricSpace ha y Q
    letI : MetricSpace Q := MQ
    letI : PseudoMetricSpace Q := MQ.toPseudoMetricSpace
    letI : PseudoEMetricSpace Q := MQ.toPseudoEMetricSpace
    exact Isometry.of_dist_eq K.top_metric
  have hρfront (r : NNReal) : (ρ r).1 ∈ frontier Q := K.top_frontier (mem_range_self r)
  have hρclean : Disjoint ((↑(pointSignedMarked μ α) : Set ℂ) \ {(ρ 0).1})
      (range (fun r ↦ (ρ r).1)) := by
    rw [disjoint_left]
    intro x hx hxray
    obtain ⟨r, rfl⟩ := hxray
    have hnz : τ r ≠ τ 0 := hx.2
    have hμzero : μ (τ r) = 0 :=
      (BoundaryPreparation.transfer_away ν (hτnep r) hnz).trans (hτzero r).1
    rcases (mem_pointSignedMarked μ α _).mp hx.1 with hμ | hα
    · exact hμ hμzero
    · exact hα (hτzero r).2
  have hνB : ∀ x ∈ frontier Q, ∃ B : PointRetainedConeNeighborhood a y Q x,
      μ x = Real.pi - (1 + coalescedPointExponent a y x / 2) * (B.hi - B.lo) := by
    intro x hx
    obtain ⟨B, _, he⟩ := K.state.boundary_coeff x hx
    refine ⟨B, ?_⟩
    simpa only [PointRetainedConeNeighborhood.flatPhysicalWidth,
      add_comm (coalescedPointExponent a y x / 2) 1] using he
  have hcurv : ∀ x ∈ interior Q, coalescedPointExponent a y x ≠ 0 →
      x ∈ pointSignedMarked μ α := by
    intro x hx he
    apply (mem_pointSignedMarked μ α x).mpr
    left
    rw [K.state.interior_coeff x hx]
    exact mul_ne_zero (neg_ne_zero.mpr Real.pi_ne_zero) he
  -- This is the genuine initial producer at the newly constructed positive
  -- corner; the output is an entire uniform infinite strip, not a local germ.
  have hnew := point_exists_positive_corner_uniform_translated_strip ha y
    K.state.ambient K.state.region_eq K.state.isClosed pieces hpieces hbudget
    hνB hcurv ρ hρ hρfront hρclean C hCadm hCpi
  rw [hCwidth] at hnew
  obtain ⟨h, hh, G, hG, hGbottom, hGmarks, hGinterior, hGclosed, hGproper, hGcontact⟩ := hnew
  have hseam (r : NNReal) : (G (translatedStripBottom hh.le r)).1 =
      (T.map (translatedStripTop T.positive.le r)).1 :=
    congrArg Subtype.val (hGbottom r)
  have hGedge (u : Icc (0 : ℝ) h) : (G (translatedStripEdge u)).1 ∈ frontier Q := by
    have hm : (G (translatedStripEdge u)).1 ∈ range (fun q ↦ (G q).1) ∩ frontier Q := by
      rw [hGcontact]
      exact Or.inr (mem_range_self u)
    exact hm.2
  have hGoriginal : ∀ x, (G x).1 ∉ pointSignedMarked ν α :=
    pointTransferredStrip_avoids_original_marks K.apex_removed
      (hτzero 0).1 (hτzero 0).2 G hGmarks
  obtain ⟨E, hEcontact⟩ := pointTranslatedStrip_glue_actual_residual ha y
    D.angle_pos D.angle_lt_pi T.positive.le hh.le T.map G hF hG
    (D.toPointRetainedSignedHalfplaneState.intrinsic_eq_and_geodesicallyConvex ha).1
    hseam T.exact_contact K hGedge hGinterior
  let U : D.Stage (s + h) :=
    { positive := add_pos T.positive hh
      map := E.map
      metric := Isometry.of_dist_eq E.metric
      bottom := fun r ↦ (E.bottom r).trans (T.bottom r)
      edge_frontier := by
        intro u
        have hm : (E.map (translatedStripEdge u)).1 ∈
            range (fun q ↦ (E.map q).1) ∩ frontier P := by
          rw [hEcontact]
          exact Or.inr (mem_range_self u)
        exact hm.2
      unmarked := by
        intro q hq
        have hqimage : (E.map q).1 ∈ range (fun w ↦ (E.map w).1) := mem_range_self q
        rw [E.image] at hqimage
        rcases hqimage with ⟨x, hx⟩ | ⟨x, hx⟩
        · apply T.unmarked x
          simpa only [hx] using hq
        · apply hGoriginal x
          change (G x).1 ∈ (↑(pointSignedMarked ν α) : Set ℂ)
          simpa only [hx] using hq.1
      positive_interior := by
        intro r hr u hu
        by_cases hus : u.1 ≤ s
        · let w : Icc (0 : ℝ) s := ⟨u.1, u.2.1, hus⟩
          have he : (⟨flatShearedPoint (conePhase D.angle) r.1 u.1,
              r.1, r.2, u.1, u.2, rfl⟩ : flatShearedStrip (conePhase D.angle) (s+h)) =
              translatedStripLowerInclusion hh.le
                ⟨flatShearedPoint (conePhase D.angle) r.1 w.1,
                  r.1, r.2, w.1, w.2, rfl⟩ := Subtype.ext rfl
          rw [he, E.lower]
          exact T.positive_interior r hr w hu
        · have hsu : s < u.1 := lt_of_not_ge hus
          let w : Icc (0 : ℝ) h :=
            ⟨u.1-s, (sub_pos.mpr hsu).le, by linarith [u.2.2]⟩
          have hw : 0 < w.1 := sub_pos.mpr hsu
          have he : (⟨flatShearedPoint (conePhase D.angle) r.1 u.1,
              r.1, r.2, u.1, u.2, rfl⟩ : flatShearedStrip (conePhase D.angle) (s+h)) =
              translatedStripUpperInclusion T.positive.le
                ⟨flatShearedPoint (conePhase D.angle) r.1 w.1,
                  r.1, r.2, w.1, w.2, rfl⟩ := by
            apply Subtype.ext
            dsimp [translatedStripUpperInclusion, flatShearedPoint, w]
            simp only [Complex.ofReal_sub]
            ring
          rw [he, E.upper]
          exact interior_mono K.subset_old (hGinterior r hr w hw) }
  exact ⟨h, hh, U, E.lower⟩

/-- No actual regular width is maximal. This conclusion is derived from the
original data and the supplied actual stage, rather than included in a family
or state certificate. -/
theorem exists_wider (T : D.Stage s) :
    ∃ t : ℝ, s < t ∧ Nonempty (D.Stage t) := by
  obtain ⟨h, hh, U, _⟩ := T.exists_wider_with_extension
  exact ⟨s+h, lt_add_of_pos_right s hh, ⟨U⟩⟩

end PointTranslatedRegularData.Stage
end RepulsiveCoulomb
