import LeanResearch.RepulsiveCoulomb.CenteredLocalMetricGlobalization
import LeanResearch.RepulsiveCoulomb.ComplexSubsetIsometryExtension
import Mathlib.Topology.OpenPartialHomeomorph.Continuity
import Mathlib.Analysis.Convex.Topology

/-! SOURCE-ONLY, UNCOMPILED. The short metric bridge used by actual
unselected chart overlaps. Centered local equalities are promoted to a
Euclidean-motion germ using convex balls in both directions. A pairwise
local-isometry certificate is not assumed. -/
noncomputable section
open Set Metric Filter
open scoped NNReal Topology
namespace RepulsiveCoulomb

/-- Convex-domain form of centered-local metric globalization. -/
theorem lipschitzOnWith_of_centered_local_bound_of_convex
    {E Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [PseudoMetricSpace Y]
    {K : ℝ≥0} {F : E → Y} {U : Set E} (hU : Convex ℝ U)
    (hlocal : ∀ x ∈ U, ∀ᶠ y in 𝓝 x, dist (F x) (F y) ≤ K * dist x y) :
    LipschitzOnWith K F U := by
  have hsegment : ∀ x z : U, ∃ γ : Icc (0 : ℝ) 1 → U,
      γ ⟨0, by norm_num⟩ = x ∧ γ ⟨1, by norm_num⟩ = z ∧ Continuous γ ∧
      ∀ s t, dist (γ s) (γ t) = |t.1 - s.1| * dist x z := by
    intro x z
    obtain ⟨γ, h0, h1, hγ, hmem, hd⟩ := exists_minimizing_segment_of_convex hU x.2 z.2
    exact ⟨fun t ↦ ⟨γ t, hmem t⟩, Subtype.ext h0, Subtype.ext h1,
      hγ.subtype_mk _, hd⟩
  have hl : ∀ x : U, ∀ᶠ y in 𝓝 x,
      dist (F x.1) (F y.1) ≤ K * dist x y := by
    intro x
    exact continuous_subtype_val.continuousAt.eventually (hlocal x.1 x.2)
  have h := lipschitzWith_of_centered_local_dist_bound_of_segments hsegment hl
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx z hz
  exact h.dist_le_mul ⟨x, hx⟩ ⟨z, hz⟩

/-- An open Euclidean chart with exact centered local distances is genuinely
rigid near every source point. Both local metric inequalities are derived;
reflection is allowed and no two-point uniqueness argument is used. -/
theorem exists_complex_isometry_germ_of_centered_local_dist_eq
    (e : OpenPartialHomeomorph ℂ ℂ)
    (hlocal : ∀ x ∈ e.source, ∀ᶠ z in 𝓝 x, dist (e x) (e z) = dist x z)
    (x : ℂ) (hx : x ∈ e.source) :
    ∃ f : ℂ ≃ᵢ ℂ, (e : ℂ → ℂ) =ᶠ[𝓝 x] (f : ℂ → ℂ) := by
  have hinverse : ∀ y ∈ e.target, ∀ᶠ z in 𝓝 y,
      dist (e.symm y) (e.symm z) = dist y z := by
    intro y hy
    have h := (e.symm.continuousAt hy).eventually (hlocal (e.symm y) (e.map_target hy))
    filter_upwards [h, e.open_target.mem_nhds hy] with z hz hzt
    simpa only [e.right_inv hy, e.right_inv hzt] using hz.symm
  obtain ⟨r, hr, hB⟩ := Metric.mem_nhds_iff.mp (e.open_source.mem_nhds hx)
  let B := ball x r
  have hxB : x ∈ B := mem_ball_self hr
  have hF : LipschitzOnWith 1 e B :=
    lipschitzOnWith_of_centered_local_bound_of_convex (convex_ball x r) (by
      intro z hz
      filter_upwards [hlocal z (hB hz)] with w hw
      simpa only [NNReal.coe_one, one_mul, hw] using (le_refl (dist z w)))
  obtain ⟨s, hs, hV⟩ := Metric.mem_nhds_iff.mp (e.open_target.mem_nhds (e.map_source hx))
  let V := ball (e x) s
  have hyV : e x ∈ V := mem_ball_self hs
  have hG : LipschitzOnWith 1 e.symm V :=
    lipschitzOnWith_of_centered_local_bound_of_convex (convex_ball (e x) s) (by
      intro z hz
      filter_upwards [hinverse z (hV hz)] with w hw
      simpa only [NNReal.coe_one, one_mul, hw] using (le_refl (dist z w)))
  have hnear : B ∩ e ⁻¹' V ∈ 𝓝 x :=
    inter_mem (isOpen_ball.mem_nhds hxB)
      ((e.continuousAt hx).preimage_mem_nhds (isOpen_ball.mem_nhds hyV))
  obtain ⟨t, ht, hA⟩ := Metric.mem_nhds_iff.mp hnear
  let A := ball x t
  let F : A → ℂ := fun z ↦ e z.1
  have hmetric : Isometry F := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (e z.1) (e w.1) = dist z.1 w.1
    have hzB := (hA z.2).1
    have hwB := (hA w.2).1
    have hzV := (hA z.2).2
    have hwV := (hA w.2).2
    apply le_antisymm
    · simpa only [NNReal.coe_one, one_mul] using hF.dist_le_mul z.1 hzB w.1 hwB
    · have h := hG.dist_le_mul (e z.1) hzV (e w.1) hwV
      simpa only [e.left_inv (hB hzB), e.left_inv (hB hwB), NNReal.coe_one, one_mul] using h
  have hAne : (interior A).Nonempty := by
    rw [isOpen_ball.interior_eq]
    exact ⟨x, mem_ball_self ht⟩
  obtain ⟨f, hf⟩ := exists_complex_isometry_extension_of_open_overlap F hmetric hAne
  refine ⟨f, ?_⟩
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_self ht)] with z hz
  exact (hf ⟨z, hz⟩).symm

end RepulsiveCoulomb
