import LeanResearch.RepulsiveCoulomb.PlanarOldBoundaryComplementRay

/-! SOURCE-ONLY, UNCOMPILED. Orient the actual full boundary clock opposite
to a given actual proper boundary ray. The orientation is derived from the
injective continuous clock, not an endpoint-side or contact certificate. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem exists_full_boundary_clock_opposite_ray
    {P : Set ℂ} (H : ℂ ≃ₜ ℂ) (hP : P = H ⁻¹' planarClosedUpperHalfplane)
    (δ : NNReal → ℂ) (hδ : IsClosedEmbedding δ)
    (hδfront : ∀ t, δ t ∈ frontier P) :
    ∃ β : ℝ → ℂ, ∃ clock : ℂ → ℝ,
      IsClosedEmbedding β ∧ range β = frontier P ∧
      (∀ t, clock (β t) = t) ∧ StrictAnti (clock ∘ δ) := by
  have hfront : frontier P = {w : ℂ | (H w).im = 0} := by
    rw [hP, ← H.preimage_frontier]
    change H ⁻¹' frontier {w : ℂ | (0 : ℝ) ≤ w.im} = _
    rw [Complex.frontier_setOfPred_le_im]
    rfl
  let b : ℝ → ℂ := fun t ↦ H.symm (t : ℂ)
  let c : ℂ → ℝ := fun x ↦ (H x).re
  have hb : IsClosedEmbedding b :=
    H.symm.isClosedEmbedding.comp Complex.isometry_ofReal.isClosedEmbedding
  have hcb : ∀ t, c (b t) = t := by intro t; simp [b, c]
  have hbc (x : ℂ) (hx : x ∈ frontier P) : b (c x) = x := by
    have him : (H x).im = 0 := by
      simpa only [hfront, mem_setOf_eq] using hx
    have he : ((H x).re : ℂ) = H x := by
      apply Complex.ext <;> simp [him]
    dsimp [b, c]
    rw [he, H.symm_apply_apply]
  have hbrange : range b = frontier P := by
    apply Subset.antisymm
    · rintro x ⟨t, rfl⟩
      rw [hfront]
      simp [b]
    · intro x hx
      exact ⟨c x, hbc x hx⟩
  let f : NNReal → ℝ := c ∘ δ
  have hfactor : b ∘ f = δ := funext (fun t ↦ hbc (δ t) (hδfront t))
  have hf : IsClosedEmbedding f := hb.of_comp_iff.mp (hfactor.symm ▸ hδ)
  rcases hf.continuous.strictMono_of_inj hf.injective with hmono | hanti
  · let β : ℝ → ℂ := fun t ↦ b (-t)
    let clock : ℂ → ℝ := fun x ↦ -c x
    have hβ : IsClosedEmbedding β := hb.comp (Homeomorph.neg ℝ).isClosedEmbedding
    have hβrange : range β = frontier P := by
      rw [← hbrange]
      ext x
      constructor
      · rintro ⟨t, rfl⟩
        exact ⟨-t, rfl⟩
      · rintro ⟨t, rfl⟩
        exact ⟨-t, by simp [β]⟩
    refine ⟨β, clock, hβ, hβrange, ?_, ?_⟩
    · intro t
      dsimp [clock, β]
      rw [hcb, neg_neg]
    · intro s t hst
      exact neg_lt_neg (hmono hst)
  · exact ⟨b, c, hb, hbrange, hcb, hanti⟩

end RepulsiveCoulomb
