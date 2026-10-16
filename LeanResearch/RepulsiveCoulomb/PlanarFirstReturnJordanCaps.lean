import LeanResearch.RepulsiveCoulomb.PointLineCapJordan
import LeanResearch.RepulsiveCoulomb.PlanarLineHalfplaneSides

/-! Source-only draft. The old-boundary arc is constructed by restricting its
actual proper-line parametrization. Only that parametrization's continuity and
injectivity are needed for the compact arc. The stopped ray and old arc give
an actual simple loop and the actual bounded Jordan cap; neither is an input.
The straightening hypothesis below is an actual ambient homeomorphism, which
the separate initial-line topology draft constructs for initial line sides. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

/-- The accepted affine arc restriction is injective for either orientation. -/
theorem lineCapSegment_injective_of_ne {b : ℝ → ℂ} (hb : Function.Injective b)
    {s t : ℝ} (hst : s ≠ t) : Function.Injective (lineCapSegment b s t) := by
  intro u v huv
  apply Subtype.ext
  have h := hb huv
  change s + u.1 * (t - s) = s + v.1 * (t - s) at h
  exact mul_right_cancel₀ (sub_ne_zero.mpr hst.symm) (add_left_cancel h)

/-- The stopped restriction only needs injectivity on the actual stopped
interval, rather than an artificial extension of the ray to a full line. -/
theorem lineCapSegment_injectiveOn_interval {r : ℝ → ℂ} {z w : ℝ}
    (hzw : z < w) (hr : InjOn r (Icc z w)) :
    Function.Injective (lineCapSegment r z w) := by
  have hm (u : unitInterval) : z + u.1 * (w - z) ∈ Icc z w := by
    have hlo := mul_nonneg u.2.1 (sub_pos.mpr hzw).le
    have hhi := mul_le_mul_of_nonneg_right u.2.2 (sub_pos.mpr hzw).le
    constructor <;> nlinarith
  intro u v huv
  apply Subtype.ext
  have h := hr (hm u) (hm v) huv
  exact mul_right_cancel₀ (sub_pos.mpr hzw).ne' (add_left_cancel h)

/-- Endpoint-only intersection is derived from the actual first-return gap.
The old arc is literally `b` between the two endpoint boundary parameters. -/
theorem firstReturn_oldArc_intersection {P : Set ℂ} {r b : ℝ → ℂ}
    {z w s t : ℝ} (hzw : z < w)
    (hboundary : range b = frontier P)
    (hs : b s = r z) (ht : b t = r w)
    (hgap : ∀ u ∈ Ioo z w, r u ∉ frontier P) :
    range (lineCapSegment r z w) ∩ range (lineCapSegment b s t) = {r z, r w} := by
  ext x
  constructor
  · rintro ⟨hx, v, hv⟩
    rw [lineCapSegment_range r hzw] at hx
    obtain ⟨u, hu, hux⟩ := hx
    have hub : r u ∈ frontier P := by
      rw [← hboundary]
      exact ⟨s + v.1 * (t - s), hv.trans hux.symm⟩
    have huends : u = z ∨ u = w := by
      by_contra h
      have huz : u ≠ z := fun he => h (Or.inl he)
      have huw : u ≠ w := fun he => h (Or.inr he)
      exact hgap u ⟨lt_of_le_of_ne hu.1 huz.symm, lt_of_le_of_ne hu.2 huw⟩ hub
    rcases huends with rfl | rfl
    · exact Or.inl hux.symm
    · exact Or.inr (mem_singleton_iff.mpr hux.symm)
  · rintro (hx | hx)
    · subst x
      exact ⟨⟨0, lineCapSegment_zero r z w⟩,
        ⟨0, (lineCapSegment_zero b s t).trans hs⟩⟩
    · have hx' := mem_singleton_iff.mp hx
      subst x
      exact ⟨⟨1, lineCapSegment_one r z w⟩,
        ⟨1, (lineCapSegment_one b s t).trans ht⟩⟩

/-- Actual Jordan curve from a stopped embedded ray and the original boundary
arc. In particular no Jordan-region or endpoint-angle certificate is assumed. -/
theorem firstReturn_oldArc_jordan {P : Set ℂ} {r b : ℝ → ℂ}
    (hr : Continuous r) (hb : Continuous b) (hbi : Function.Injective b)
    {z w s t : ℝ} (hzw : z < w) (hri : InjOn r (Icc z w))
    (hboundary : range b = frontier P)
    (hs : b s = r z) (ht : b t = r w)
    (hgap : ∀ u ∈ Ioo z w, r u ∉ frontier P) :
    Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr ''
      (range (lineCapSegment r z w) ∪ range (lineCapSegment b s t))) := by
  have hrzw : r z ≠ r w := by
    intro he
    exact hzw.ne (hri ⟨le_rfl, hzw.le⟩ ⟨hzw.le, le_rfl⟩ he)
  have hst : s ≠ t := fun he => hrzw (hs.symm.trans ((congrArg b he).trans ht))
  let e := Complex.orthonormalBasisOneI.repr
  let γ := lineCapSegment r z w
  let η := lineCapSegment b s t
  have hγ := isArcBetween_of_continuous_injective_interval (e ∘ γ)
    (e.continuous.comp (lineCapSegment_continuous hr z w))
    (e.injective.comp (lineCapSegment_injectiveOn_interval hzw hri))
  have hη := isArcBetween_of_continuous_injective_interval (e ∘ η)
    (e.continuous.comp (lineCapSegment_continuous hb s t))
    (e.injective.comp (lineCapSegment_injective_of_ne hbi hst))
  have hγ' : Schoenflies.IsArcBetween (range (e ∘ γ)) (e (r z)) (e (r w)) := by
    simpa [γ] using hγ
  have hη' : Schoenflies.IsArcBetween (range (e ∘ η)) (e (r z)) (e (r w)) := by
    simpa [η, hs, ht] using hη
  have hmeet : range (e ∘ γ) ∩ range (e ∘ η) = {e (r z), e (r w)} := by
    rw [range_comp, range_comp, ← image_inter e.injective,
      firstReturn_oldArc_intersection hzw hboundary hs ht hgap, image_insert_eq, image_singleton]
  have hJ := Schoenflies.IsJordanCurve.two_arcs_of_two_arcs hγ' hη' hmeet
  simpa only [range_comp, ← image_union] using hJ

/-- A connected set escaping every compact set is forced into the actual
unbounded Jordan region if it misses the curve. Applies both to `Pᶜ` and to
the interior of an already embedded proper sector/strip. -/
theorem connected_escaping_set_outside_bounded_jordan_region
    {C U V W : Set ℂ} (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcover : U ∪ V = Cᶜ) (hK : IsCompact (closure U))
    (hW : IsPreconnected W) (hWC : Disjoint W C)
    (hescape : ∀ K : Set ℂ, IsCompact K → ∃ x ∈ W, x ∉ K) :
    W ⊆ V ∧ Disjoint (closure U) W := by
  have hsub : W ⊆ U ∪ V := by
    intro x hx
    rw [hcover]
    exact fun hxc => disjoint_left.mp hWC hx hxc
  have hWV : W ⊆ V := by
    rcases IsPreconnected.subset_or_subset hU hV hUV hsub hW with hWU | hWV
    · obtain ⟨x, hxW, hxK⟩ := hescape (closure U) hK
      exact (hxK (subset_closure (hWU hxW))).elim
    · exact hWV
  exact ⟨hWV, (hUV.closure_left hV).mono_right hWV⟩

/-- The bounded cap lies in the literal original closed set. Connectedness and
escape of its complement are geometric topology hypotheses, not a cap-side
identity in disguise; the following theorem constructs them from a straightening. -/
theorem bounded_jordan_region_subset_closed_halfplane {P C U V : Set ℂ}
    (hP : IsClosed P) (hPc : IsPreconnected Pᶜ)
    (hescape : ∀ K : Set ℂ, IsCompact K → ∃ x ∈ Pᶜ, x ∉ K)
    (hCP : C ⊆ P) (hU : IsOpen U) (hV : IsOpen V)
    (hUV : Disjoint U V) (hcover : U ∪ V = Cᶜ) (hK : IsCompact (closure U)) :
    closure U ⊆ P := by
  have hdis : Disjoint Pᶜ C := disjoint_left.mpr (fun x hx hc => hx (hCP hc))
  have hout := connected_escaping_set_outside_bounded_jordan_region
    hU hV hUV hcover hK hPc hdis hescape
  intro x hx
  by_contra hxP
  exact disjoint_left.mp hout.2 hx hxP

/-- Actual ambient straightening supplies all the complement facts required by
cap containment. No Euclidean boundedness preservation of a homeomorphism is
assumed: a compact set's imaginary-coordinate image has a finite lower bound. -/
theorem straightened_halfplane_complement_geometry (H : ℂ ≃ₜ ℂ) :
    IsClosed (H ⁻¹' planarClosedUpperHalfplane) ∧
      IsPreconnected (H ⁻¹' planarClosedUpperHalfplane)ᶜ ∧
      ∀ K : Set ℂ, IsCompact K →
        ∃ x ∈ (H ⁻¹' planarClosedUpperHalfplane)ᶜ, x ∉ K := by
  have hcompl : (H ⁻¹' planarClosedUpperHalfplane)ᶜ = H ⁻¹' planarOpenLowerHalfplane := by
    ext x
    simp [planarClosedUpperHalfplane, planarOpenLowerHalfplane, not_le]
  have hlow : IsPreconnected planarOpenLowerHalfplane :=
    (convex_halfSpace_lt (.mk Complex.add_im Complex.smul_im) (0 : ℝ)).isPreconnected
  refine ⟨(isClosed_le continuous_const Complex.continuous_im).preimage H.continuous, ?_, ?_⟩
  · rw [hcompl]
    exact H.isPreconnected_preimage.mpr hlow
  · intro K hK
    obtain ⟨L, hL⟩ := hK.bddBelow_image (Complex.continuous_im.comp H.continuous).continuousOn
    let v : ℂ := ⟨0, min L 0 - 1⟩
    refine ⟨H.symm v, ?_, ?_⟩
    · rw [hcompl]
      change (H (H.symm v)).im < 0
      rw [H.apply_symm_apply]
      change min L 0 - 1 < 0
      linarith [min_le_right L (0 : ℝ)]
    · intro hx
      have h := hL (mem_image_of_mem (fun x : ℂ => (H x).im) hx)
      simp only [H.apply_symm_apply] at h
      change L ≤ min L 0 - 1 at h
      linarith [min_le_left L (0 : ℝ)]

/-- The boundary coordinates, actual compact old arc, simple loop, open Jordan
regions and containment of the closed bounded cap are all outputs. The map `r`
is only assumed embedded on its stopped portion. -/
theorem exists_firstReturn_actual_cap {P : Set ℂ} (H : ℂ ≃ₜ ℂ)
    (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (b r : ℝ → ℂ) (hb : Continuous b) (hbi : Function.Injective b)
    (hboundary : range b = frontier P) (hr : Continuous r)
    {z w : ℝ} (hzw : z < w) (hri : InjOn r (Icc z w))
    (hz : r z ∈ frontier P) (hw : r w ∈ frontier P)
    (hrP : MapsTo r (Icc z w) P)
    (hgap : ∀ u ∈ Ioo z w, r u ∉ frontier P) :
    ∃ s t : ℝ, b s = r z ∧ b t = r w ∧ s ≠ t ∧
      let C := range (lineCapSegment r z w) ∪ range (lineCapSegment b s t)
      Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr '' C) ∧
      ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
        Disjoint U V ∧ U ∪ V = Cᶜ ∧ frontier U = C ∧ frontier V = C ∧
        IsCompact (closure U) ∧ closure U ⊆ P := by
  obtain ⟨s, hs⟩ := hboundary.symm ▸ hz
  obtain ⟨t, ht⟩ := hboundary.symm ▸ hw
  have hrzw : r z ≠ r w := fun h => hzw.ne (hri ⟨le_rfl, hzw.le⟩ ⟨hzw.le, le_rfl⟩ h)
  have hst : s ≠ t := fun h => hrzw (hs.symm.trans ((congrArg b h).trans ht))
  have hJ := firstReturn_oldArc_jordan hr hb hbi hzw hri hboundary hs ht hgap
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, hK⟩ :=
    complex_jordan_regions_of_image hJ
  obtain ⟨hclosed, hconn, hescape⟩ := straightened_halfplane_complement_geometry H
  rw [← hP] at hclosed hconn hescape
  have hCP : range (lineCapSegment r z w) ∪ range (lineCapSegment b s t) ⊆ P := by
    rintro x (hx | ⟨u, rfl⟩)
    · rw [lineCapSegment_range r hzw] at hx
      obtain ⟨v, hv, rfl⟩ := hx
      exact hrP hv
    · apply hclosed.frontier_subset
      rw [← hboundary]
      exact mem_range_self _
  have hcontain := bounded_jordan_region_subset_closed_halfplane
    hclosed hconn hescape hCP hU hV hUV hcover hK
  exact ⟨s, t, hs, ht, hst, hJ, U, V, hU, hV, hUc, hVc,
    hUV, hcover, hfu, hfv, hK, hcontain⟩

end RepulsiveCoulomb
