import LeanResearch.RepulsiveCoulomb.PointTranslatedBackwardEnd
import LeanResearch.RepulsiveCoulomb.PointTranslatedRowClock
import LeanResearch.RepulsiveCoulomb.TranslatedRelativePatchHalfDisk
import LeanResearch.RepulsiveCoulomb.PointParallelEdgeInterior

/-! SOURCE-ONLY ASSEMBLY. Actual finite translated rectangles have no old
boundary return along their positive top row. The backward end, two easy-edge
exclusions, local halfdisk, genuine source traces, complete ambient row clock,
first contact, cap angle, and signed-budget contradiction are all produced.
The source row is not bounded by alpha at the original positive corner.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

private theorem retained_flat_width_admissible
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hw : C.flatPhysicalWidth = Real.pi) : C.Admissible := by
  unfold PointRetainedConeNeighborhood.flatPhysicalWidth at hw
  unfold PointRetainedConeNeighborhood.Admissible
  have ha := coalescedPointExponent_nonneg a y p
  have hπ := Real.pi_pos
  nlinarith [mul_nonneg ha hπ.le]

theorem point_translated_top_row_mem_interior
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (HP : ℂ ≃ₜ ℂ) (hP : P = HP ⁻¹' planarClosedUpperHalfplane)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hν : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo))
    {stripAngle R s ell delta : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi)
    (hR : 0 < R) (hs : 0 < s) (hsell : s < ell) (hsdelta : s ≤ delta)
    (ρ : NNReal → P)
    (hρ : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (hρfront : ∀ t, (ρ t).1 ∈ frontier P)
    (hcorner : ν (ρ 0).1 = Real.pi - stripAngle)
    (hclear : ∀ z ∈ (↑(pointSignedMarked ν α) : Set ℂ) \ {(ρ 0).1}, ∀ r : NNReal,
      delta < (pointSmoothConformalEDist a y z (ρ r).1).toReal)
    (edge : Icc (0 : ℝ) ell → P)
    (hedge : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace edge)
    (hedgefront : ∀ u, (edge u).1 ∈ frontier P)
    (f : flatShearedRectangle (conePhase stripAngle) R s → P)
    (hf : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (hbottom : ∀ r : Icc (0 : ℝ) R, f (shearedBottomPoint hs.le r) = ρ ⟨r.1, r.2.1⟩)
    (hold : ∀ u : Icc (0 : ℝ) s,
      f (shearedCompactEdgePoint hR.le u) = edge ⟨u.1, u.2.1, u.2.2.trans hsell.le⟩) :
    ∀ t : Icc (0 : ℝ) R, 0 < t.1 →
      (f (shearedTopPoint (conePhase stripAngle) R s hs.le t)).1 ∈ interior P := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let q := shearedCompactEdgePoint (v := conePhase stripAngle) hR.le ⟨s, hs.le, le_rfl⟩
  have hqfront : (f q).1 ∈ frontier P := by rw [hold]; exact hedgefront _
  have hlocal : PointLocallyDistancePreserving a y (fun z ↦ (f z).1) := by
    intro z
    exact ⟨univ, isOpen_univ, mem_univ _, fun x _ w _ ↦ hf.dist_eq x w⟩
  have hunmarked : ∀ z, (f z).1 ∉ (↑(pointSignedMarked ν α) : Set ℂ) \ {(ρ 0).1} := by
    apply pointShearedRectangle_unmarked ha y (conePhase_norm stripAngle) hs.le hsdelta
      (fun r ↦ (ρ r).1) hclear (fun z ↦ (f z).1) hlocal
    intro r hr
    exact congrArg Subtype.val (hbottom ⟨r, hr⟩)
  have hqne : (f q).1 ≠ (ρ 0).1 := by
    intro he
    have hno := metric_translated_stage_avoids_bottom stripAngle_pos stripAngle_lt_pi hR hs.le ρ hρ f hf hbottom
      (⟨0, le_rfl, hR.le⟩ : Icc (0 : ℝ) R) (⟨s, hs.le, le_rfl⟩ : Icc (0 : ℝ) s) hs
    exact hno ⟨0, Subtype.ext he.symm⟩
  have hqoff : (f q).1 ∉ pointSignedMarked ν α := fun hm ↦ hunmarked q ⟨hm, hqne⟩
  have hqzero : ν (f q).1 = 0 := (pointSigned_eq_zero_off_marked hqoff).1
  obtain ⟨C, hCν⟩ := hν (f q).1 hqfront
  have hCwidth : C.flatPhysicalWidth = Real.pi := by
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    nlinarith [hCν, hqzero]
  have hCadm : C.Admissible := retained_flat_width_admissible C hCwidth
  let Ch := C.flatHalfDiskChart ha y (f q).2 hCwidth
  obtain ⟨L, hL, hLR, hLs, g, hg, hg0, hgback, hgout⟩ :=
    exists_translated_source_halfDisk stripAngle_pos stripAngle_lt_pi hR hs hsell f hf edge hedge hold Ch
  let es : Icc (0 : ℝ) s → P := fun u ↦ edge ⟨u.1, u.2.1, u.2.2.trans hsell.le⟩
  have hes : Isometry es := by
    apply Isometry.of_dist_eq
    intro u v
    exact hedge.dist_eq _ _
  obtain ⟨δ, hδ, hδ0, hδs, hδrange, hδfront, hδback, hδavoid⟩ :=
    point_exists_translated_backward_end ha y stripAngle_pos stripAngle_lt_pi hR hs ρ hρ hρfront
      es hes (fun u ↦ hedgefront _) f hf hbottom hold
  obtain ⟨E, hE0, hE1, hEL, hEP, r, hrc, hr0, hrd, hEclock, hrow⟩ :=
    point_exists_translated_row_clock ha y hR f hf (⟨s, hs.le, le_rfl⟩ : Icc (0 : ℝ) s)
  let backward : ℝ → ℂ := δ ∘ Real.toNNReal
  have hbc : Continuous backward := hδ.continuous.comp continuous_real_toNNReal
  have hb0 : backward 0 = E.start := by
    have he : (es ⟨s, hs.le, le_rfl⟩).1 = (f q).1 := (congrArg Subtype.val (hold ⟨s, hs.le, le_rfl⟩)).symm
    simpa only [backward, Function.comp_apply, Real.toNNReal_zero] using hδ0.trans (he.trans hE0.symm)
  have hbproper : IsClosedEmbedding (fun u : NNReal ↦ backward (u : ℝ)) := by
    simpa only [backward, Function.comp_apply, Real.toNNReal_coe] using hδ
  have hbfront : ∀ u ∈ Ici (0 : ℝ), backward u ∈ frontier P := fun u _ ↦ hδfront _
  have hcenter : (g (flatLinkSectorDiskApex Real.pi_pos.le hL.le)).1 = E.start :=
    (congrArg Subtype.val hg0).trans hE0.symm
  let CE : PointRetainedConeNeighborhood a y P E.start := hE0.symm ▸ C
  have hCEadm : CE.Admissible := by
    have hcast {p q : ℂ} (D : PointRetainedConeNeighborhood a y P p)
        (he : p = q) (hD : D.Admissible) :
        (he ▸ D : PointRetainedConeNeighborhood a y P q).Admissible := by
      cases he
      exact hD
    exact hcast C hE0.symm hCadm
  have hback : ∀ t : ℝ, ∀ ht : 0 ≤ t, ∀ htL : t ≤ L,
      (g (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl t ⟨ht, htL⟩ 0)).1 = backward t := by
    intro t ht htL
    obtain ⟨hts, hgt⟩ := hgback t ht htL
    rw [hgt]
    have hδt := hδback (⟨t, ht⟩ : NNReal) (htL.trans hLs.le)
    have hb : backward t = δ ⟨t, ht⟩ := by
      apply congrArg δ
      exact Real.toNNReal_of_nonneg ht
    rw [hb, hδt]
  have hout : ∀ t : ℝ, ∀ ht : 0 ≤ t, ∀ htL : t ≤ L,
      (g (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl t ⟨ht, htL⟩
        (parallelHalfDiskDirection (sub_pos.mpr stripAngle_lt_pi) (by linarith : Real.pi-stripAngle<Real.pi)))).1 = r t := by
    intro t ht htL
    obtain ⟨htR, hgt⟩ := hgout t ht htL
    exact (congrArg Subtype.val hgt).trans (hrow ⟨t, htR⟩).symm
  have havoid : ∀ t ∈ Ioc (0 : ℝ) (pointActualEdgeLength E),
      ∀ u ∈ Ici (0 : ℝ), r t ≠ backward u := by
    intro t ht u hu he
    have htR : t ∈ Icc (0 : ℝ) R := ⟨ht.1.le, hEL ▸ ht.2⟩
    apply hδavoid ⟨t, htR⟩ ht.1
    refine ⟨u.toNNReal, ?_⟩
    exact he.symm.trans (hrow ⟨t, htR⟩)
  let A := min L CE.radius / 2
  have hA : 0 < A := half_pos (lt_min hL CE.radius_pos)
  have hAL : A ≤ L := (half_le_self (le_of_lt (lt_min hL CE.radius_pos))).trans (min_le_left _ _)
  have hAC : A < CE.radius := (half_lt_self (lt_min hL CE.radius_pos)).trans_le (min_le_right _ _)
  have hflat : ν E.start = 0 := by rw [hE0]; exact hqzero
  have hpRemoved : ∃ u : ℝ, 0 < u ∧ backward u = (ρ 0).1 := by
    refine ⟨s, hs, ?_⟩
    change δ s.toNNReal = (ρ 0).1
    exact (congrArg δ (Real.toNNReal_of_nonneg hs.le)).trans hδs
  have hinterior := point_actual_parallel_edge_positive_mem_interior ha y HP hP pieces hpieces
    hL stripAngle_pos stripAngle_lt_pi (fun z ↦ (g z).1) (fun x z ↦ hg.dist_eq x z) (fun z ↦ (g z).2)
    E hEP hcenter CE hCEadm backward r hbc hrc hb0 hbproper hback hout hA hAL hAC
    hbfront hr0 hrd hEclock havoid hbudget hν hcorner hflat hpRemoved
  intro t ht
  let τ : unitInterval := ⟨t.1/R, div_nonneg t.2.1 hR.le, (div_le_one hR).mpr t.2.2⟩
  have hτ : 0 < τ.1 := div_pos ht hR
  have htime : pointActualEdgeLength E * τ.1 = t.1 := by rw [hEL]; exact mul_div_cancel₀ _ hR.ne'
  have heq : E.curve τ = (f (shearedTopPoint (conePhase stripAngle) R s hs.le t)).1 := by
    rw [hEclock τ, htime]
    exact hrow t
  exact heq ▸ hinterior τ hτ

end RepulsiveCoulomb
