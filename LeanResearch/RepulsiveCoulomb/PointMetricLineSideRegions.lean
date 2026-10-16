module

public import LeanResearch.RepulsiveCoulomb.PointMetricLineCompactification
public import LeanResearch.RepulsiveCoulomb.PlaneJordanSeparation

@[expose] public section

/-! Construct the actual two open sides of a complete minimizing line, by
inverting its actual Jordan compactification. The missing inversion pole is
restored to the unbounded Jordan side using an explicit punctured ball.
No halfplane or global plane-straightening certificate is supplied as input. -/
noncomputable section
open Set Topology Metric
namespace RepulsiveCoulomb

/-- Use the actual Jordan theorem in ordinary complex coordinates. -/
theorem complex_jordan_regions_of_image {C : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr '' C)) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Cᶜ ∧ frontier U = C ∧ frontier V = C ∧
      IsCompact (closure U) := by
  let e : ℂ ≃ₜ Schoenflies.Plane := Complex.orthonormalBasisOneI.repr.toHomeomorph
  obtain ⟨f, hf, him⟩ := hC
  let γ : ℝ → ℂ := e.symm ∘ f
  have hc : ContinuousOn γ (Icc (0 : ℝ) 1) := e.symm.continuous.comp_continuousOn hf.continuousOn
  have hclose : γ 0 = γ 1 := congrArg e.symm hf.closes
  have hinj : InjOn γ (Ico (0 : ℝ) 1) := by
    intro s hs t ht he
    exact hf.injOn hs ht (e.symm.injective he)
  have hγim : γ '' Icc (0 : ℝ) 1 = C := by
    rw [image_comp, him]
    change e.symm '' (e '' C) = C
    exact e.toEquiv.symm_image_image C
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, hK, _, _⟩ :=
    jordan_separation_of_homeomorph e γ hc hclose hinj
  exact ⟨U, V, hU, hV, hUc, hVc, hUV, by simpa only [hγim] using hcover,
    by simpa only [hγim] using hfu, by simpa only [hγim] using hfv, hK⟩

/-- Invert a Jordan curve through zero, omit its zero vertex, and restore the
inverse pole to the exterior side. This constructs the two genuine open sides
of the resulting proper embedded line. -/
theorem complex_jordan_boundary_inversion_regions {C : Set ℂ}
    (hC : Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr '' C))
    (h0C : (0 : ℂ) ∈ C) (p : ℂ) :
    ∃ A B : Set ℂ, IsOpen A ∧ IsOpen B ∧ IsConnected A ∧ IsConnected B ∧
      Disjoint A B ∧ A ∪ B = ((fun w : ℂ ↦ p + w⁻¹) '' (C \ {0}))ᶜ ∧
      frontier A = (fun w : ℂ ↦ p + w⁻¹) '' (C \ {0}) ∧
      frontier B = (fun w : ℂ ↦ p + w⁻¹) '' (C \ {0}) := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv, hK⟩ :=
    complex_jordan_regions_of_image hC
  let f : ℂ → ℂ := planarInversion p
  let g : ℂ → ℂ := fun w ↦ p + w⁻¹
  let S := g '' (C \ {0})
  let A := g '' U
  let B := g '' V ∪ {p}
  have hfg (z : ℂ) : f (g z) = z := by simp [f, g, planarInversion]
  have hgf (z : ℂ) : g (f z) = z := by simp [f, g, planarInversion]
  have hginj : Function.Injective g := fun x y h ↦
    by simpa only [hfg] using congrArg f h
  have hg0 : g 0 = p := by simp [g]
  have hf0 : f p = 0 := by simp [f, planarInversion]
  have hgneq {w : ℂ} (hw : w ≠ 0) : g w ≠ p := by
    intro he
    exact hw (hginj (he.trans hg0.symm))
  have hUC : Disjoint U C := by
    apply disjoint_left.mpr
    intro z hz hzC
    have hz' : z ∈ U ∪ V := Or.inl hz
    rw [hcover] at hz'
    exact hz' hzC
  have hVC : Disjoint V C := by
    apply disjoint_left.mpr
    intro z hz hzC
    have hz' : z ∈ U ∪ V := Or.inr hz
    rw [hcover] at hz'
    exact hz' hzC
  have hU0 : (0 : ℂ) ∉ U := fun h ↦ disjoint_left.mp hUC h h0C
  have hV0 : (0 : ℂ) ∉ V := fun h ↦ disjoint_left.mp hVC h h0C
  have hgc (w : ℂ) (hw : w ≠ 0) : ContinuousAt g w :=
    continuousAt_const.add (continuousAt_id.inv₀ hw)
  have hgopen {T : Set ℂ} (hT : IsOpen T) (hT0 : (0 : ℂ) ∉ T) : IsOpen (g '' T) := by
    have heq : g '' T = f ⁻¹' T := by
      ext z
      constructor
      · rintro ⟨w, hw, rfl⟩
        change f (g w) ∈ T
        rwa [hfg]
      · intro hz
        exact ⟨f z, hz, hgf z⟩
    rw [heq]
    apply (continuousOn_planarInversion (p := p) (A := ({p}ᶜ : Set ℂ)) (by simp)).isOpen_preimage
      isOpen_compl_singleton ?_ hT
    intro z hz
    change z ≠ p
    intro he
    have hzT : f z ∈ T := hz
    rw [he, hf0] at hzT
    exact hT0 hzT
  have hAo : IsOpen A := hgopen hU hU0
  have hVo : IsOpen (g '' V) := hgopen hV hV0
  have hAc : IsConnected A := hUc.image g (fun w hw ↦ (hgc w (by
    intro he; exact hU0 (he ▸ hw))).continuousWithinAt)
  have hVimage : IsConnected (g '' V) := hVc.image g (fun w hw ↦ (hgc w (by
    intro he; exact hV0 (he ▸ hw))).continuousWithinAt)
  have hpA : p ∉ A := by
    rintro ⟨w, hw, hwp⟩
    exact hgneq (fun he ↦ hU0 (he ▸ hw)) hwp
  have hAB : Disjoint A B := by
    apply disjoint_left.mpr
    rintro z ⟨u, hu, huz⟩ (⟨v, hv, hvz⟩ | hzp)
    · exact disjoint_left.mp hUV hu (by simpa only [hginj (huz.trans hvz.symm)] using hv)
    · exact hpA ⟨u, hu, huz.trans (mem_singleton_iff.mp hzp)⟩
  obtain ⟨r, hr⟩ := (isBounded_iff_subset_closedBall (0 : ℂ)).mp hK.isBounded
  let R := max r 1
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hRout : (closedBall (0 : ℂ) R)ᶜ ⊆ V := by
    intro z hz
    have hzcl : z ∉ closure U := fun h ↦ hz
      (closedBall_subset_closedBall (le_max_left _ _) (hr h))
    have hzC : z ∉ C := fun h ↦ hzcl (frontier_subset_closure (hfu.symm ▸ h))
    have hm : z ∈ U ∪ V := hcover.symm ▸ hzC
    exact hm.resolve_left (fun h ↦ hzcl (subset_closure h))
  have hfnorm (z : ℂ) : ‖f z‖ = (dist z p)⁻¹ := by
    simp only [f, planarInversion, norm_inv, dist_eq_norm]
  have hBball : ball p R⁻¹ ⊆ B := by
    intro z hz
    by_cases hzp : z = p
    · exact Or.inr (mem_singleton_iff.mpr hzp)
    · refine Or.inl ⟨f z, hRout ?_, hgf z⟩
      rw [mem_compl_iff, mem_closedBall, dist_zero_right, hfnorm]
      exact not_le.mpr (lt_inv_of_lt_inv₀ (dist_pos.mpr hzp) (mem_ball.mp hz))
  have hBo : IsOpen B := by
    have heq : B = g '' V ∪ ball p R⁻¹ := by
      apply Subset.antisymm
      · rintro z (hz | hz)
        · exact Or.inl hz
        · exact Or.inr ((mem_singleton_iff.mp hz).symm ▸ mem_ball_self (inv_pos.mpr hR))
      · exact union_subset subset_union_left hBball
    rw [heq]
    exact hVo.union isOpen_ball
  have hpcl : p ∈ closure (g '' V) := by
    have hpball : p ∈ closure (ball p R⁻¹ \ {p}) := by
      simpa only [Set.sdiff_eq, inter_comm] using
        (dense_compl_singleton p).open_subset_closure_inter isOpen_ball
          (mem_ball_self (inv_pos.mpr hR))
    apply closure_mono (fun z hz ↦ ?_) hpball
    exact (hBball hz.1).resolve_right hz.2
  have hBc : IsConnected B := hVimage.subset_closure subset_union_left
    (union_subset subset_closure (singleton_subset_iff.mpr hpcl))
  have hAS : Disjoint A S := by
    apply disjoint_left.mpr
    rintro z ⟨u, hu, huz⟩ ⟨w, hw, hwz⟩
    exact disjoint_left.mp hUC hu (by simpa only [hginj (huz.trans hwz.symm)] using hw.1)
  have hBS : Disjoint B S := by
    apply disjoint_left.mpr
    rintro z (⟨v, hv, hvz⟩ | hzp) ⟨w, hw, hwz⟩
    · exact disjoint_left.mp hVC hv (by simpa only [hginj (hvz.trans hwz.symm)] using hw.1)
    · exact hgneq (by simpa only [mem_singleton_iff] using hw.2)
        (hwz.trans (mem_singleton_iff.mp hzp))
  have hnewcover : A ∪ B = Sᶜ := by
    ext z
    constructor
    · rintro (hz | hz)
      · exact fun hs ↦ disjoint_left.mp hAS hz hs
      · exact fun hs ↦ disjoint_left.mp hBS hz hs
    · intro hz
      by_cases hzp : z = p
      · exact Or.inr (Or.inr (mem_singleton_iff.mpr hzp))
      · have hfz0 : f z ≠ 0 := by
          intro he
          exact hzp ((hgf z).symm.trans ((congrArg g he).trans hg0))
        have hfzC : f z ∉ C := fun h ↦ hz ⟨f z, ⟨h, by simpa using hfz0⟩, hgf z⟩
        rcases (hcover.symm ▸ hfzC : f z ∈ U ∪ V) with hu | hv
        · exact Or.inl ⟨f z, hu, hgf z⟩
        · exact Or.inr (Or.inl ⟨f z, hv, hgf z⟩)
  have hfrontA : frontier A = S := by
    apply Subset.antisymm
    · intro z hz
      have hzA : z ∉ A := (hAo.frontier_eq ▸ hz).2
      by_contra hzS
      have hm : z ∈ A ∪ B := hnewcover.symm ▸ hzS
      have hzB := hm.resolve_left hzA
      exact disjoint_left.mp (hAB.symm.closure_right hBo) hzB (frontier_subset_closure hz)
    · rintro z ⟨w, hw, rfl⟩
      rw [hAo.frontier_eq]
      refine ⟨mem_closure_image (hgc w (by simpa only [mem_singleton_iff] using hw.2))
        (frontier_subset_closure (hfu.symm ▸ hw.1)), ?_⟩
      exact fun h ↦ disjoint_left.mp hAS h ⟨w, hw, rfl⟩
  have hfrontB : frontier B = S := by
    apply Subset.antisymm
    · intro z hz
      have hzB : z ∉ B := (hBo.frontier_eq ▸ hz).2
      by_contra hzS
      have hm : z ∈ A ∪ B := hnewcover.symm ▸ hzS
      have hzA := hm.resolve_right hzB
      exact disjoint_left.mp (hAB.closure_right hAo) hzA (frontier_subset_closure hz)
    · rintro z ⟨w, hw, rfl⟩
      rw [hBo.frontier_eq]
      refine ⟨closure_mono subset_union_left
        (mem_closure_image (hgc w (by simpa only [mem_singleton_iff] using hw.2))
          (frontier_subset_closure (hfv.symm ▸ hw.1))), ?_⟩
      exact fun h ↦ disjoint_left.mp hBS h ⟨w, hw, rfl⟩
  exact ⟨A, B, hAo, hBo, hAc, hBc, hAB, hnewcover, hfrontA, hfrontB⟩

/-- Actual side regions of the actual line, obtained with no prescribed side
sets or halfplane certificate. Their boundaries are exactly the whole line. -/
theorem exists_pointMetricLine_side_regions {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) (ℓ : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (ℓ s) (ℓ t)).toReal = dist s t) :
    ∃ U V : Set ℂ, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = (range ℓ)ᶜ ∧ frontier U = range ℓ ∧ frontier V = range ℓ := by
  obtain ⟨p, hp⟩ := pointMetricLine_compl_nonempty ha y ℓ hd
  let C : Set ℂ := insert 0 (planarInversion p '' range ℓ)
  have hJ : Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr '' C) :=
    pointMetricLine_inverted_jordan ha y ℓ hd hp
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcover, hfu, hfv⟩ :=
    complex_jordan_boundary_inversion_regions hJ (mem_insert 0 _) p
  have hcarrier : (fun w : ℂ ↦ p + w⁻¹) '' (C \ {0}) = range ℓ := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      rcases hw.1 with hw0 | ⟨x, hx, hxw⟩
      · exact False.elim (hw.2 (mem_singleton_iff.mpr hw0))
      · rw [← hxw]
        simpa [planarInversion] using hx
    · intro hz
      have hzp : z ≠ p := fun he ↦ hp (he ▸ hz)
      refine ⟨planarInversion p z, ⟨Or.inr ⟨z, hz, rfl⟩, ?_⟩, ?_⟩
      · exact fun h ↦ planarInversion_ne_zero hzp (mem_singleton_iff.mp h)
      · simp [planarInversion]
  exact ⟨U, V, hU, hV, hUc, hVc, hUV, by simpa only [hcarrier] using hcover,
    by simpa only [hcarrier] using hfu, by simpa only [hcarrier] using hfv⟩

end RepulsiveCoulomb
