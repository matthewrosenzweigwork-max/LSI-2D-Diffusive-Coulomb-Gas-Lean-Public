import LeanResearch.RepulsiveCoulomb.PointLinePieceEndpointTangents

/-! Records-only, uncompiled. Equal physical endpoint directions for two
original regular C1 representatives of the same oriented metric line.
The endpoint may be a positive atom. The original line is never differentiated.
Only the two representatives are differentiated, along common one-sided
secants obtained by inverting their continuous clocks on compact intervals. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb

/-- The inverse of an actual strictly increasing clock on the compact unit
interval exists on its exact source interval and is continuous there, including
both endpoints. Its arbitrary totalization outside that interval is irrelevant. -/
theorem exists_compact_oriented_clock_inverse {T : ℝ → ℝ}
    (hT : Continuous T) (hmono : StrictMonoOn T (Icc (0 : ℝ) 1)) :
    ∃ ρ : ℝ → Icc (0 : ℝ) 1,
      (∀ q ∈ Icc (T 0) (T 1), T (ρ q) = q) ∧
      (∀ t : Icc (0 : ℝ) 1,
        Tendsto ρ (𝓝[Icc (T 0) (T 1)] (T t)) (𝓝 t)) := by
  classical
  have himage : T '' Icc (0 : ℝ) 1 = Icc (T 0) (T 1) :=
    hT.continuousOn.image_Icc_of_monotoneOn (by norm_num) hmono.monotoneOn
  have hex (q : ℝ) (hq : q ∈ Icc (T 0) (T 1)) :
      ∃ t : Icc (0 : ℝ) 1, T t = q := by
    rw [← himage] at hq
    obtain ⟨t, ht, heq⟩ := hq
    exact ⟨⟨t, ht⟩, heq⟩
  let ρ : ℝ → Icc (0 : ℝ) 1 := fun q =>
    if hq : q ∈ Icc (T 0) (T 1) then (hex q hq).choose else 0
  have hρ (q : ℝ) (hq : q ∈ Icc (T 0) (T 1)) : T (ρ q) = q := by
    dsimp only [ρ]
    rw [dif_pos hq]
    exact (hex q hq).choose_spec
  have hemb : Topology.IsClosedEmbedding (fun t : Icc (0 : ℝ) 1 => T t) :=
    (hT.comp continuous_subtype_val).isClosedEmbedding (by
      intro s t hst
      exact Subtype.ext (hmono.injOn s.property t.property hst))
  refine ⟨ρ, hρ, fun t => ?_⟩
  apply hemb.tendsto_nhds_iff.mpr
  have heq : (fun q => T (ρ q)) =ᶠ[𝓝[Icc (T 0) (T 1)] (T t)] id := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hρ q hq
  exact (tendsto_id.mono_left nhdsWithin_le_nhds).congr' heq.symm

/-- Common initial source time gives common normalized physical derivatives.
The source curve `c` is arbitrary: it is not assumed differentiable, even at
the common point. Positive orientation is supplied by the two actual clocks. -/
theorem oriented_clocks_same_initial_tangent
    {F G c : ℝ → ℂ} {T U : ℝ → ℝ}
    (hT : Continuous T) (hTm : StrictMonoOn T (Icc (0 : ℝ) 1))
    (hU : Continuous U) (hUm : StrictMonoOn U (Icc (0 : ℝ) 1))
    (hclock : T 0 = U 0)
    (hFparam : EqOn F (c ∘ T) (Icc (0 : ℝ) 1))
    (hGparam : EqOn G (c ∘ U) (Icc (0 : ℝ) 1))
    (hF : DifferentiableAt ℝ F 0) (hG : DifferentiableAt ℝ G 0)
    (hV : deriv F 0 ≠ 0) (hW : deriv G 0 ≠ 0) :
    deriv F 0 / (‖deriv F 0‖ : ℂ) = deriv G 0 / (‖deriv G 0‖ : ℂ) := by
  obtain ⟨ρ, hρ, hρlim⟩ := exists_compact_oriented_clock_inverse hU hUm
  let τ : ℝ → ℝ := fun s => (ρ (T s)).val
  have hwidth : T 0 < U 1 := by
    rw [hclock]
    exact hUm (by norm_num) (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ s : ℝ in 𝓝[>] 0,
      s ∈ Ioo (0 : ℝ) 1 ∧ U 0 < T s ∧ T s < U 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
      ((hT.tendsto 0).eventually (Iio_mem_nhds hwidth)).filter_mono nhdsWithin_le_nhds]
      with s hs hs1 hsU
    refine ⟨⟨hs, hs1⟩, ?_, hsU⟩
    rw [← hclock]
    exact hTm (by norm_num) ⟨hs.le, hs1.le⟩ hs
  have hsource : Tendsto T (𝓝[>] (0 : ℝ)) (𝓝[Icc (U 0) (U 1)] (U 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hsmall.mono (fun _ hs => ⟨hs.2.1.le, hs.2.2.le⟩)⟩
    simpa only [hclock] using (hT.tendsto 0).mono_left nhdsWithin_le_nhds
  have hτlim : Tendsto τ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    (continuous_subtype_val.tendsto (0 : Icc (0 : ℝ) 1)).comp
      ((hρlim 0).comp hsource)
  have hτpos : ∀ᶠ s : ℝ in 𝓝[>] 0, 0 < τ s := by
    filter_upwards [hsmall] with s hs
    have heq : U (τ s) = T s := hρ (T s) ⟨hs.2.1.le, hs.2.2.le⟩
    have hne : τ s ≠ 0 := by
      intro hz
      rw [hz] at heq
      exact (ne_of_lt hs.2.1) heq
    exact lt_of_le_of_ne (ρ (T s)).property.1 (Ne.symm hne)
  have hτ : Tendsto τ (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hτlim, hτpos⟩
  have hbase : F 0 = G 0 := by
    rw [hFparam (by norm_num), hGparam (by norm_num)]
    simp only [Function.comp_apply, hclock]
  apply normalized_derivatives_eq_of_oriented_clock hF.hasDerivAt hG.hasDerivAt hV hW
    (tendsto_id.mono_right (nhdsGT_le_nhdsNE 0))
    (hτ.mono_right (nhdsGT_le_nhdsNE 0)) hbase
  · filter_upwards [hsmall] with s hs
    change F s = G (ρ (T s)).val
    rw [hFparam (Ioo_subset_Icc_self hs.1), hGparam (ρ (T s)).property]
    simp only [Function.comp_apply]
    rw [hρ (T s) ⟨hs.2.1.le, hs.2.2.le⟩]
  · filter_upwards [hsmall, hτpos] with s hs hτs
    exact div_pos (by simpa using hτs) (by simpa using hs.1.1)

/-- Common final source time gives common normalized incoming derivatives.
Both representative time increments are negative, so their quotient is
positive. In particular this does not accidentally negate the incoming tangent. -/
theorem oriented_clocks_same_final_tangent
    {F G c : ℝ → ℂ} {T U : ℝ → ℝ}
    (hT : Continuous T) (hTm : StrictMonoOn T (Icc (0 : ℝ) 1))
    (hU : Continuous U) (hUm : StrictMonoOn U (Icc (0 : ℝ) 1))
    (hclock : T 1 = U 1)
    (hFparam : EqOn F (c ∘ T) (Icc (0 : ℝ) 1))
    (hGparam : EqOn G (c ∘ U) (Icc (0 : ℝ) 1))
    (hF : DifferentiableAt ℝ F 1) (hG : DifferentiableAt ℝ G 1)
    (hV : deriv F 1 ≠ 0) (hW : deriv G 1 ≠ 0) :
    deriv F 1 / (‖deriv F 1‖ : ℂ) = deriv G 1 / (‖deriv G 1‖ : ℂ) := by
  obtain ⟨ρ, hρ, hρlim⟩ := exists_compact_oriented_clock_inverse hU hUm
  let τ : ℝ → ℝ := fun s => (ρ (T s)).val
  have hwidth : U 0 < T 1 := by
    rw [hclock]
    exact hUm (by norm_num) (by norm_num) (by norm_num)
  have hsmall : ∀ᶠ s : ℝ in 𝓝[<] 1,
      s ∈ Ioo (0 : ℝ) 1 ∧ U 0 < T s ∧ T s < U 1 := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds,
      ((hT.tendsto 1).eventually (Ioi_mem_nhds hwidth)).filter_mono nhdsWithin_le_nhds]
      with s hs hs0 hsU
    refine ⟨⟨hs0, hs⟩, hsU, ?_⟩
    rw [← hclock]
    exact hTm ⟨hs0.le, hs.le⟩ (by norm_num) hs
  have hsource : Tendsto T (𝓝[<] (1 : ℝ)) (𝓝[Icc (U 0) (U 1)] (U 1)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, hsmall.mono (fun _ hs => ⟨hs.2.1.le, hs.2.2.le⟩)⟩
    simpa only [hclock] using (hT.tendsto 1).mono_left nhdsWithin_le_nhds
  have hτlim : Tendsto τ (𝓝[<] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
    (continuous_subtype_val.tendsto (1 : Icc (0 : ℝ) 1)).comp
      ((hρlim 1).comp hsource)
  have hτlt : ∀ᶠ s : ℝ in 𝓝[<] 1, τ s < 1 := by
    filter_upwards [hsmall] with s hs
    have heq : U (τ s) = T s := hρ (T s) ⟨hs.2.1.le, hs.2.2.le⟩
    have hne : τ s ≠ 1 := by
      intro hz
      rw [hz] at heq
      exact (ne_of_lt hs.2.2) heq.symm
    exact lt_of_le_of_ne (ρ (T s)).property.2 hne
  have hτ : Tendsto τ (𝓝[<] (1 : ℝ)) (𝓝[<] (1 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hτlim, hτlt⟩
  have hbase : F 1 = G 1 := by
    rw [hFparam (by norm_num), hGparam (by norm_num)]
    simp only [Function.comp_apply, hclock]
  apply normalized_derivatives_eq_of_oriented_clock hF.hasDerivAt hG.hasDerivAt hV hW
    (tendsto_id.mono_right (nhdsLT_le_nhdsNE 1))
    (hτ.mono_right (nhdsLT_le_nhdsNE 1)) hbase
  · filter_upwards [hsmall] with s hs
    change F s = G (ρ (T s)).val
    rw [hFparam (Ioo_subset_Icc_self hs.1), hGparam (ρ (T s)).property]
    simp only [Function.comp_apply]
    rw [hρ (T s) ⟨hs.2.1.le, hs.2.2.le⟩]
  · filter_upwards [hsmall, hτlt] with s hs hτs
    exact div_pos_of_neg_of_neg (sub_neg.mpr hτs) (sub_neg.mpr hs.1.2)

/-- Two actual original radial pieces beginning at the same point of the
same oriented metric line have the same normalized outgoing physical tangent.
Their enclosing segments and source clocks may differ. Positive atoms are allowed. -/
theorem PointRadialC1ArcPiece.same_line_start_tangent
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {tm tp um up : ℝ} (ht : tm < tp) (hu : um < up)
    (e : PointRadialC1ArcPiece ha y (lineCapSegment c tm tp))
    (d : PointRadialC1ArcPiece ha y (lineCapSegment c um up))
    (hbase : e.curve 0 = d.curve 0) :
    deriv e.curve 0 / (‖deriv e.curve 0‖ : ℂ) =
      deriv d.curve 0 / (‖deriv d.curve 0‖ : ℂ) := by
  obtain ⟨T, hT, hTm, _, _, hTp⟩ := e.exists_actual_line_clock hd ht
  obtain ⟨U, hU, hUm, _, _, hUp⟩ := d.exists_actual_line_clock hd hu
  have hclock : T 0 = U 0 := by
    apply (pointMetricLine_isClosedEmbedding ha y c hd).injective
    exact (hTp (by norm_num)).symm.trans (hbase.trans (hUp (by norm_num)))
  exact oriented_clocks_same_initial_tangent hT hTm hU hUm hclock hTp hUp
    (e.smooth.differentiable (by norm_num) 0)
    (d.smooth.differentiable (by norm_num) 0)
    (e.regular 0 (by norm_num)) (d.regular 0 (by norm_num))

/-- Two actual original radial pieces ending at the same point of the same
oriented metric line have the same normalized incoming physical tangent,
including at a positive atom. No differentiability of the metric line is used. -/
theorem PointRadialC1ArcPiece.same_line_finish_tangent
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {tm tp um up : ℝ} (ht : tm < tp) (hu : um < up)
    (e : PointRadialC1ArcPiece ha y (lineCapSegment c tm tp))
    (d : PointRadialC1ArcPiece ha y (lineCapSegment c um up))
    (hbase : e.curve 1 = d.curve 1) :
    deriv e.curve 1 / (‖deriv e.curve 1‖ : ℂ) =
      deriv d.curve 1 / (‖deriv d.curve 1‖ : ℂ) := by
  obtain ⟨T, hT, hTm, _, _, hTp⟩ := e.exists_actual_line_clock hd ht
  obtain ⟨U, hU, hUm, _, _, hUp⟩ := d.exists_actual_line_clock hd hu
  have hclock : T 1 = U 1 := by
    apply (pointMetricLine_isClosedEmbedding ha y c hd).injective
    exact (hTp (by norm_num)).symm.trans (hbase.trans (hUp (by norm_num)))
  exact oriented_clocks_same_final_tangent hT hTm hU hUm hclock hTp hUp
    (e.smooth.differentiable (by norm_num) 1)
    (d.smooth.differentiable (by norm_num) 1)
    (e.regular 1 (by norm_num)) (d.regular 1 (by norm_num))

/-- Reversing both incoming derivatives gives the same outward ray at the
common finish. The minus sign is explicit and applied on both sides. -/
theorem PointRadialC1ArcPiece.same_line_finish_outward_tangent
    {m : ℕ} {a : Fin m → ℝ} {ha : ∀ j, 0 ≤ a j} {y : Fin m → ℂ}
    {c : ℝ → ℂ}
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {tm tp um up : ℝ} (ht : tm < tp) (hu : um < up)
    (e : PointRadialC1ArcPiece ha y (lineCapSegment c tm tp))
    (d : PointRadialC1ArcPiece ha y (lineCapSegment c um up))
    (hbase : e.curve 1 = d.curve 1) :
    -deriv e.curve 1 / (‖-deriv e.curve 1‖ : ℂ) =
      -deriv d.curve 1 / (‖-deriv d.curve 1‖ : ℂ) := by
  simpa only [norm_neg, neg_div] using
    congrArg (fun z : ℂ => -z) (e.same_line_finish_tangent hd ht hu d hbase)

end RepulsiveCoulomb
