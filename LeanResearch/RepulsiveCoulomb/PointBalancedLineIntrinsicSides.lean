import LeanResearch.RepulsiveCoulomb.PointActualBalancedLineAllMasses
import LeanResearch.RepulsiveCoulomb.PointClosedRegionIntrinsicMetric

/-! Uncompiled records-only successor. Match the already constructed fixed
balanced sides to the genuine intrinsic side construction, allowing exactly
one explicit global swap. No convexity or intrinsic-distance equality is
assumed for the balanced-side pair. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointBalancedLine_two_open_connected_partitions_eq_or_swap
    {A B U V : Set ℂ} (hAc : IsConnected A) (hBc : IsConnected B)
    (hU : IsOpen U) (hV : IsOpen V) (hUc : IsConnected U) (hVc : IsConnected V)
    (hUV : Disjoint U V) (hcover : A ∪ B = U ∪ V) :
    (A = U ∧ B = V) ∨ (A = V ∧ B = U) := by
  have hAsub : A ⊆ U ∪ V := by rw [← hcover]; exact subset_union_left
  have hBsub : B ⊆ U ∪ V := by rw [← hcover]; exact subset_union_right
  have hbuild (hAU : A ⊆ U) (hBV : B ⊆ V) : A = U ∧ B = V := by
    constructor
    · apply Subset.antisymm hAU
      intro z hz
      have hab : z ∈ A ∪ B := hcover.symm ▸ Or.inl hz
      exact hab.resolve_right (fun hb => disjoint_left.mp hUV hz (hBV hb))
    · apply Subset.antisymm hBV
      intro z hz
      have hab : z ∈ A ∪ B := hcover.symm ▸ Or.inr hz
      exact hab.resolve_left (fun ha => disjoint_left.mp hUV (hAU ha) hz)
  have hbuild' (hAV : A ⊆ V) (hBU : B ⊆ U) : A = V ∧ B = U := by
    constructor
    · apply Subset.antisymm hAV
      intro z hz
      have hab : z ∈ A ∪ B := hcover.symm ▸ Or.inr hz
      exact hab.resolve_right (fun hb => disjoint_left.mp hUV (hBU hb) hz)
    · apply Subset.antisymm hBU
      intro z hz
      have hab : z ∈ A ∪ B := hcover.symm ▸ Or.inl hz
      exact hab.resolve_left (fun ha => disjoint_left.mp hUV hz (hAV ha))
  rcases IsPreconnected.subset_or_subset hU hV hUV hAsub hAc.isPreconnected with hAU | hAV
  · rcases IsPreconnected.subset_or_subset hU hV hUV hBsub hBc.isPreconnected with hBU | hBV
    · obtain ⟨z, hz⟩ := hVc.nonempty
      have hab : z ∈ A ∪ B := hcover.symm ▸ Or.inr hz
      exact False.elim (disjoint_left.mp hUV (hab.elim (fun ha => hAU ha) (fun hb => hBU hb)) hz)
    · exact Or.inl (hbuild hAU hBV)
  · rcases IsPreconnected.subset_or_subset hU hV hUV hBsub hBc.isPreconnected with hBU | hBV
    · exact Or.inr (hbuild' hAV hBU)
    · obtain ⟨z, hz⟩ := hUc.nonempty
      have hab : z ∈ A ∪ B := hcover.symm ▸ Or.inl hz
      exact False.elim (disjoint_left.mp hUV hz (hab.elim (fun ha => hAV ha) (fun hb => hBV hb)))

/-- The SAME fixed balanced-side pair has actual contained minimizers and
its constrained old-metric length infimum equals the ambient metric. -/
theorem pointMetricLine_fixed_sides_intrinsic_geometry
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (c : ℝ → ℂ)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (c s) (c t)).toReal = dist s t)
    {A B : Set ℂ} (hAc : IsConnected A) (hBc : IsConnected B)
    (hcover : A ∪ B = (range c)ᶜ) :
    PointGeodesicallyConvex a y (closure A) ∧ PointGeodesicallyConvex a y (closure B) ∧
      (∀ x ∈ closure A, ∀ z ∈ closure A,
        pointRegionIntrinsicEDist ha y (closure A) x z = pointSmoothConformalEDist a y x z) ∧
      (∀ x ∈ closure B, ∀ z ∈ closure B,
        pointRegionIntrinsicEDist ha y (closure B) x z = pointSmoothConformalEDist a y x z) := by
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hcoverUV, _, _, hUP, hVP⟩ :=
    exists_pointMetricLine_intrinsically_geodesic_sides ha y c hd
  have hp := pointBalancedLine_two_open_connected_partitions_eq_or_swap hAc hBc hU hV hUc hVc hUV
    (hcover.trans hcoverUV.symm)
  have hconvex : PointGeodesicallyConvex a y (closure A) ∧ PointGeodesicallyConvex a y (closure B) := by
    rcases hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hUP, hVP⟩
    · exact ⟨hVP, hUP⟩
  exact ⟨hconvex.1, hconvex.2,
    fun x hx z hz => pointRegionIntrinsicEDist_eq_ambient ha y hconvex.1 hx hz,
    fun x hx z hz => pointRegionIntrinsicEDist_eq_ambient ha y hconvex.2 hx hz⟩

end RepulsiveCoulomb
