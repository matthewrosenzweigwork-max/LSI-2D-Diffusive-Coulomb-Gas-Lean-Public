import LeanResearch.RepulsiveCoulomb.PointTranslatedRegularStages

/-! SOURCE-ONLY, UNCOMPILED. Construct the actual distance-preserving strip at
the finite supremum of ALL actual regular widths. The map and its compatibility
are outputs. The old compact edge remains on the frontier by closedness; every
point strictly below the limiting top belongs to a genuine earlier stage and
is unmarked except at the original apex. Top contact and extension are not
assumed or claimed by this finite-limit lemma. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb.PointTranslatedRegularData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} (D : PointTranslatedRegularData a y ha P ν α)

/-- Output of genuine Cauchy completion, not a certificate supplied to the
original-data producer. Every field is proved below. -/
structure FiniteWidthLimit where
  bounded : BddAbove D.regularWidths
  positive : 0 < sSup D.regularWidths
  map : flatShearedStrip (conePhase D.angle) (sSup D.regularWidths) → P
  metric : @Isometry _ P inferInstance
    (pointRegionMetricSpace ha y P).toPseudoEMetricSpace map
  bottom : ∀ r : NNReal, map (translatedStripBottom positive.le r) = D.ray r
  extends_stage : ∀ {s : ℝ} (T : D.Stage s) (z : flatShearedStrip (conePhase D.angle) s),
    map ⟨z.1, flatShearedStrip_mono (le_csSup bounded (show s ∈ D.regularWidths from ⟨T⟩)) z.2⟩ = T.map z
  edge_frontier : ∀ u : Icc (0 : ℝ) (sSup D.regularWidths),
    (map (translatedStripEdge u)).1 ∈ frontier P
  below_unmarked : ∀ r : NNReal, ∀ u : Icc (0 : ℝ) (sSup D.regularWidths),
    u.1 < sSup D.regularWidths →
    (map ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩).1 ∉
      (↑(pointSignedMarked ν α) : Set ℂ) \ {(D.ray 0).1}
  below_positive_interior : ∀ r : NNReal, 0 < r →
    ∀ u : Icc (0 : ℝ) (sSup D.regularWidths), 0 < u.1 → u.1 < sSup D.regularWidths →
    (map ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩).1 ∈ interior P
  closed : IsClosedEmbedding (fun z ↦ (map z).1)
  proper : IsProperMap (fun z ↦ (map z).1)

/-- Finite-width attainment of the actual isometry. The sole temporary premise
is boundedness of the specifically constructed regular-width set; the geometric
boundedness adapter discharges it using a retained positive-budget point. -/
theorem exists_finite_width_limit (hbound : BddAbove D.regularWidths) :
    Nonempty D.FiniteWidthLimit := by
  classical
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  letI : UniformSpace P := M.toUniformSpace
  letI : CompleteSpace P := pointRegionMetricSpace_complete ha y D.toPointRetainedSignedHalfplaneState.isClosed
  let W := D.regularWidths
  let T : ∀ s : W, D.Stage s.1 := fun s ↦ Classical.choice s.2
  let f := fun s : W ↦ (T s).map
  have hf (s : W) : Isometry (f s) := (T s).metric
  have hcompat : ∀ s t : W, ∀ z (hs : z ∈ flatShearedStrip (conePhase D.angle) s.1)
      (ht : z ∈ flatShearedStrip (conePhase D.angle) t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩ := by
    intro s t z hs ht
    rcases le_total s.1 t.1 with hst | hts
    · exact D.stages_agree (T s) (T t) hst ⟨z, hs⟩
    · exact (D.stages_agree (T t) (T s) hts ⟨z, ht⟩).symm
  obtain ⟨F, hF, hFold⟩ := exists_shearedStrip_width_supremum_isometry
    (conePhase_norm D.angle) D.direction_im_ne_zero D.regularWidths_nonempty
    D.regularWidths_positive hbound f hf hcompat
  obtain ⟨s₀, hs₀⟩ := D.regularWidths_nonempty
  have hs₀pos : 0 < s₀ := D.regularWidths_positive s₀ hs₀
  have hs₀b : s₀ ≤ sSup W := le_csSup hbound hs₀
  have hb : 0 < sSup W := hs₀pos.trans_le hs₀b
  have hbottom (r : NNReal) : F (translatedStripBottom hb.le r) = D.ray r :=
    (hFold ⟨s₀, hs₀⟩ (translatedStripBottom (T ⟨s₀, hs₀⟩).positive.le r)).trans
      ((T ⟨s₀, hs₀⟩).bottom r)
  have hext : ∀ {s : ℝ} (U : D.Stage s) (z : flatShearedStrip (conePhase D.angle) s),
      F ⟨z.1, flatShearedStrip_mono (le_csSup hbound (show s ∈ W from ⟨U⟩)) z.2⟩ = U.map z := by
    intro s U z
    exact (hFold ⟨s, ⟨U⟩⟩ z).trans (D.stages_agree (T ⟨s, ⟨U⟩⟩) U le_rfl z)
  have hbelow (r : NNReal) (u : Icc (0 : ℝ) (sSup W)) (hub : u.1 < sSup W) :
      ∃ s : W, ∃ hu : u.1 ≤ s.1,
        F ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩ =
          (T s).map ⟨flatShearedPoint (conePhase D.angle) r.1 u.1,
            r.1, r.2, u.1, ⟨u.2.1, hu⟩, rfl⟩ := by
    obtain ⟨s, hs, hus⟩ := exists_lt_of_lt_csSup D.regularWidths_nonempty hub
    refine ⟨⟨s, hs⟩, hus.le, ?_⟩
    exact hFold ⟨s, hs⟩
      ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, ⟨u.2.1, hus.le⟩, rfl⟩
  have hmarks (r : NNReal) (u : Icc (0 : ℝ) (sSup W)) (hub : u.1 < sSup W) :
      (F ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩).1 ∉
        (↑(pointSignedMarked ν α) : Set ℂ) \ {(D.ray 0).1} := by
    obtain ⟨s, hu, he⟩ := hbelow r u hub
    rw [he]
    exact (T s).unmarked _
  have hint (r : NNReal) (hr : 0 < r) (u : Icc (0 : ℝ) (sSup W))
      (hu : 0 < u.1) (hub : u.1 < sSup W) :
      (F ⟨flatShearedPoint (conePhase D.angle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩).1 ∈ interior P := by
    obtain ⟨s, hus, he⟩ := hbelow r u hub
    rw [he]
    exact (T s).positive_interior r hr ⟨u.1, u.2.1, hus⟩ hu
  obtain ⟨hclosed, hproper⟩ := pointTranslatedStrip_closed_proper ha y D.direction_im_ne_zero F
    (fun x z ↦ hF.dist_eq x z)
  have hedge : ∀ u : Icc (0 : ℝ) (sSup W), (F (translatedStripEdge u)).1 ∈ frontier P := by
    let top : Icc (0 : ℝ) (sSup W) := ⟨sSup W, hb.le, le_rfl⟩
    let e : Icc (0 : ℝ) (sSup W) → ℂ := fun u ↦ (F (translatedStripEdge u)).1
    have hecont : Continuous e := by
      apply hclosed.continuous.comp
      apply Continuous.subtype_mk
      change Continuous (fun u : Icc (0 : ℝ) (sSup W) ↦ flatShearedPoint (conePhase D.angle) 0 u.1)
      unfold flatShearedPoint
      fun_prop
    have hpre : IsClosed (e ⁻¹' frontier P) := isClosed_frontier.preimage hecont
    have hlow : Iio top ⊆ e ⁻¹' frontier P := by
      intro u hu
      obtain ⟨s, hus, he⟩ := hbelow 0 u hu
      change (F (translatedStripEdge u)).1 ∈ frontier P
      change F (translatedStripEdge u) = (T s).map (translatedStripEdge ⟨u.1, u.2.1, hus⟩) at he
      rw [he]
      exact (T s).edge_frontier ⟨u.1, u.2.1, hus⟩
    have hclosure : closure (Iio top) = Iic top := closure_Iio'
      ⟨(⟨0, le_rfl, hb.le⟩ : Icc (0 : ℝ) (sSup W)), hb⟩
    intro u
    exact closure_minimal hlow hpre (by rw [hclosure]; exact u.2.2)
  exact ⟨⟨hbound, hb, F, hF, hbottom, hext, hedge, hmarks, hint, hclosed, hproper⟩⟩

namespace FiniteWidthLimit
variable {D} (L : D.FiniteWidthLimit)

/-- Any genuinely new marked point of the attained closed limit must be on
its actual free top ray; it cannot hide in the interior or compact open edge. -/
theorem new_marked_on_top {x : ℂ}
    (hx : x ∈ range (fun q ↦ (L.map q).1))
    (hm : x ∈ (↑(pointSignedMarked ν α) : Set ℂ) \ {(D.ray 0).1}) :
    x ∈ range (fun r ↦ (L.map (translatedStripTop L.positive.le r)).1) := by
  obtain ⟨q, rfl⟩ := hx
  obtain ⟨r, hr, u, hu, hq⟩ := q.2
  have hub : u = sSup D.regularWidths := by
    by_contra hn
    have hlt : u < sSup D.regularWidths := lt_of_le_of_ne hu.2 hn
    have he : q = ⟨flatShearedPoint (conePhase D.angle) r u, r, hr, u, hu, rfl⟩ := Subtype.ext hq
    exact L.below_unmarked ⟨r, hr⟩ ⟨u, hu⟩ hlt (he ▸ hm)
  refine ⟨⟨r, hr⟩, ?_⟩
  apply congrArg (fun q ↦ (L.map q).1)
  apply Subtype.ext
  change flatShearedPoint (conePhase D.angle) r (sSup D.regularWidths) = q.1
  simpa only [hub] using hq.symm

end FiniteWidthLimit
end RepulsiveCoulomb.PointTranslatedRegularData
