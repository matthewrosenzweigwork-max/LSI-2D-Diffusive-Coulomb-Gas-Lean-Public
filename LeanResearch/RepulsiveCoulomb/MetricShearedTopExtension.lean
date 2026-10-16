import LeanResearch.RepulsiveCoulomb.ShearedTopPatchThickening

/-! NEW implementation after source loss. Actual supported local patches
are glued and restricted to the genuinely enlarged rectangle interior. For
an arbitrary metric target the result is locally distance preserving only;
point-specific globalization belongs to the later closure-map wrapper. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- Construct the local top extension from independent genuine patches.
The argument order and result match the retained full normal-top caller.
The general-H source inclusion is explicitly new, not a recovered signature. -/
theorem exists_sheared_top_local_extension {Y : Type*} [MetricSpace Y]
    {v : ℂ} (hv : ‖v‖ = 1) (hvi : v.im ≠ 0) {R s delta : ℝ}
    (hR : 0 < R) (hs : 0 < s) (hsdelta : s < delta)
    {H : Set ℂ} (hH : Convex ℝ H)
    (hdeltaH : flatShearedRectangle v R delta ⊆ H)
    (f : flatShearedRectangle v R s → Y) (hf : Isometry f)
    (B : Icc (0 : ℝ) R → ℝ) (hB : ∀ r, 0 < B r)
    (e : ∀ r, supportedFlatPatch H (shearedTopPoint v R s hs.le r).1 (B r) ≃ᵢ
      ball (f (shearedTopPoint v R s hs.le r)) (B r))
    (hold : ∀ r (x : flatShearedRectangle v R s)
      (hx : x.1 ∈ supportedFlatPatch H (shearedTopPoint v R s hs.le r).1 (B r)),
      (e r ⟨x.1, hx⟩).1 = f x) :
    ∃ h : ℝ, 0 < h ∧ s + h < delta ∧
      ∃ G : interior (flatShearedRectangle v R (s + h)) → Y,
        (∀ x : interior (flatShearedRectangle v R s),
          ∀ hx : x.1 ∈ interior (flatShearedRectangle v R (s + h)),
            G ⟨x.1, hx⟩ = f ⟨x.1, interior_subset x.2⟩) ∧
        ∀ p, ∃ V : Set (interior (flatShearedRectangle v R (s + h))), IsOpen V ∧ p ∈ V ∧
          ∀ x ∈ V, ∀ z ∈ V, dist (G x) (G z) = dist x z := by
  let K := flatShearedRectangle v R s
  let q := shearedTopPoint v R s hs.le
  let W := supportedFlatPatchedSet H q B
  have hKH : K ⊆ H :=
    (flatShearedRectangle_mono le_rfl hsdelta.le).trans hdeltaH
  obtain ⟨F, hFold, hFlocal⟩ := exists_supported_flat_patched_union
    (flatShearedRectangle_convex v R s) (flatShearedRectangle_interior_nonempty hvi hR hs)
    hH hKH f hf q B hB e hold
  obtain ⟨h, hh, hhdelta, hUW⟩ :=
    exists_sheared_top_patch_thickening hv hvi hR hs hsdelta hdeltaH B hB
  let U := interior (flatShearedRectangle v R (s + h))
  let incl : U → W := Set.inclusion hUW
  have hincl : Isometry incl := fun _ _ ↦ rfl
  let G : U → Y := F ∘ incl
  refine ⟨h, hh, hhdelta, G, ?_, ?_⟩
  · intro x hx
    exact hFold ⟨x.1, interior_subset x.2⟩ (hUW hx)
  · intro p
    obtain ⟨V, hV, hpV, hdist⟩ := hFlocal (incl p)
    refine ⟨incl ⁻¹' V, hV.preimage hincl.continuous, hpV, ?_⟩
    intro x hx z hz
    exact (hdist (incl x) hx (incl z) hz).trans (hincl.dist_eq x z)

end RepulsiveCoulomb
