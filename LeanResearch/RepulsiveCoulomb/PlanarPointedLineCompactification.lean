import LeanResearch.RepulsiveCoulomb.PlanarProperRayCompactification
import LeanResearch.RepulsiveCoulomb.Imported.Schoenflies.JordanSchoenflies
import Mathlib.Topology.Compactification.OnePoint.Basic

/-! Parameter-preserving, pointed compactification of a proper embedded line.
The boundary correspondence is constructed before invoking relative Schoenflies.
Neither a global straightening nor a closed-side homeomorphism is an input. -/
noncomputable section
open Set Topology Filter Function
open scoped OnePoint
namespace RepulsiveCoulomb

def pointedPlanarLine (p : ℂ) (ℓ : ℝ → ℂ) (t : OnePoint ℝ) : ℂ :=
  t.elim 0 (fun s ↦ planarInversion p (ℓ s))

@[simp] theorem pointedPlanarLine_infty (p : ℂ) (ℓ : ℝ → ℂ) :
    pointedPlanarLine p ℓ ∞ = 0 := rfl

@[simp] theorem pointedPlanarLine_coe (p : ℂ) (ℓ : ℝ → ℂ) (t : ℝ) :
    pointedPlanarLine p ℓ t = planarInversion p (ℓ t) := rfl

theorem pointedPlanarLine_continuous {ℓ : ℝ → ℂ} (hℓ : IsClosedEmbedding ℓ)
    {p : ℂ} (hp : p ∉ range ℓ) : Continuous (pointedPlanarLine p ℓ) := by
  apply (OnePoint.continuous_iff _).mpr
  constructor
  · rw [Filter.coclosedCompact_eq_cocompact]
    have hd := (tendsto_dist_right_cocompact_atTop p).comp hℓ.tendsto_cocompact
    have hi := hd.inv_tendsto_atTop
    change Tendsto (fun t : ℝ ↦ (dist (ℓ t) p)⁻¹) (cocompact ℝ) (𝓝 (0 : ℝ)) at hi
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [pointedPlanarLine_coe, planarInversion, norm_inv, ← dist_eq_norm,
      Pi.inv_apply, Function.comp_apply] using hi
  · change Continuous (fun t ↦ (ℓ t - p)⁻¹)
    exact (hℓ.continuous.sub continuous_const).inv₀
      (fun t ↦ sub_ne_zero.mpr (fun ht ↦ hp ⟨t, ht⟩))

theorem pointedPlanarLine_injective {ℓ : ℝ → ℂ} (hℓ : Injective ℓ)
    {p : ℂ} (hp : p ∉ range ℓ) : Injective (pointedPlanarLine p ℓ) := by
  intro s t h
  induction s using OnePoint.rec with
  | infty =>
      induction t using OnePoint.rec with
      | infty => rfl
      | coe t =>
          exact False.elim (planarInversion_ne_zero (fun ht ↦ hp ⟨t, ht⟩) h.symm)
  | coe s =>
      induction t using OnePoint.rec with
      | infty =>
          exact False.elim (planarInversion_ne_zero (fun hs ↦ hp ⟨s, hs⟩) h)
      | coe t =>
          exact congrArg OnePoint.some (hℓ (planarInversion_injective p h))

theorem pointedPlanarLine_range (p : ℂ) (ℓ : ℝ → ℂ) :
    range (pointedPlanarLine p ℓ) = insert 0 (planarInversion p '' range ℓ) := by
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    induction t using OnePoint.rec with
    | infty => exact mem_insert _ _
    | coe t => exact Or.inr ⟨ℓ t, mem_range_self t, rfl⟩
  · rintro (rfl | ⟨_, ⟨t, rfl⟩, rfl⟩)
    · exact ⟨∞, rfl⟩
    · exact ⟨(t : OnePoint ℝ), rfl⟩

/-- The compactification has its genuine subspace topology, including at infinity. -/
def pointedPlanarLineHomeomorph {ℓ : ℝ → ℂ} (hℓ : IsClosedEmbedding ℓ)
    {p : ℂ} (hp : p ∉ range ℓ) :
    OnePoint ℝ ≃ₜ ↥(insert 0 (planarInversion p '' range ℓ)) :=
  ((pointedPlanarLine_continuous hℓ hp).isClosedEmbedding
    (pointedPlanarLine_injective hℓ.injective hp)).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr (pointedPlanarLine_range p ℓ))

@[simp] theorem pointedPlanarLineHomeomorph_apply {ℓ : ℝ → ℂ}
    (hℓ : IsClosedEmbedding ℓ) {p : ℂ} (hp : p ∉ range ℓ) (t : OnePoint ℝ) :
    (pointedPlanarLineHomeomorph hℓ hp t : ℂ) = pointedPlanarLine p ℓ t := rfl

/-- Jordan-ness is preserved by a genuine boundary homeomorphism. This uses
only the loop definition and the restricted maps, not an ambient extension. -/
theorem jordanCurve_of_boundary_homeomorph {C D : Set Schoenflies.Plane}
    (hC : Schoenflies.IsJordanCurve C) (e : C ≃ₜ D) :
    Schoenflies.IsJordanCurve D := by
  obtain ⟨f, g, hfg, _⟩ := Schoenflies.exists_isHomeoOn_of_homeomorph e
  obtain ⟨γ, hγ, hγC⟩ := hC
  have hmaps : MapsTo γ (Icc (0 : ℝ) 1) C := by
    intro t ht
    rw [← hγC]
    exact mem_image_of_mem γ ht
  refine ⟨f ∘ γ, ⟨hfg.continuousOn.comp hγ.continuousOn hmaps, ?_, ?_⟩, ?_⟩
  · exact congrArg f hγ.closes
  · intro s hs t ht hst
    exact hγ.injOn hs ht (hfg.injOn (hmaps ⟨hs.1, hs.2.le⟩)
      (hmaps ⟨ht.1, ht.2.le⟩) hst)
  · rw [image_comp, hγC, hfg.image_eq]

/-- Two actual proper line compactifications admit an ambient extension which
matches every finite line parameter and sends the actual infinity point to
infinity. The only Jordan input is the already proved source compactification. -/
theorem exists_pointedPlanarLine_extension {ℓ k : ℝ → ℂ}
    (hℓ : IsClosedEmbedding ℓ) (hk : IsClosedEmbedding k)
    {p q : ℂ} (hp : p ∉ range ℓ) (hq : q ∉ range k)
    (hJ : Schoenflies.IsJordanCurve (Complex.orthonormalBasisOneI.repr ''
      insert 0 (planarInversion p '' range ℓ))) :
    ∃ F : ℂ ≃ₜ ℂ, F 0 = 0 ∧
      ∀ t, F (planarInversion p (ℓ t)) = planarInversion q (k t) := by
  let C := insert 0 (planarInversion p '' range ℓ)
  let D := insert 0 (planarInversion q '' range k)
  let c : ℂ ≃ₜ Schoenflies.Plane := Complex.orthonormalBasisOneI.repr.toHomeomorph
  let eC := pointedPlanarLineHomeomorph hℓ hp
  let eD := pointedPlanarLineHomeomorph hk hq
  let e : C ≃ₜ D := eC.symm.trans eD
  let e' : (c '' C) ≃ₜ (c '' D) := (c.image C).symm.trans (e.trans (c.image D))
  have hCJ : Schoenflies.IsJordanCurve (c '' C) := hJ
  have hDJ := jordanCurve_of_boundary_homeomorph hCJ e'
  obtain ⟨G, hG⟩ := Schoenflies.jordan_schoenflies_of_homeomorph hCJ hDJ e'
  let F : ℂ ≃ₜ ℂ := c.trans (G.trans c.symm)
  have hmatch (s : OnePoint ℝ) : F (pointedPlanarLine p ℓ s) =
      pointedPlanarLine q k s := by
    have h := hG ((c.image C) (eC s))
    apply c.injective
    change c (c.symm (G (c (pointedPlanarLine p ℓ s)))) = c (pointedPlanarLine q k s)
    rw [c.apply_symm_apply]
    simp [e', e, eC, eD, Homeomorph.trans_apply] at h
    rw [pointedPlanarLineHomeomorph_apply] at h
    exact h
  exact ⟨F, by simpa using hmatch ∞, fun t ↦ hmatch (t : OnePoint ℝ)⟩

end RepulsiveCoulomb
