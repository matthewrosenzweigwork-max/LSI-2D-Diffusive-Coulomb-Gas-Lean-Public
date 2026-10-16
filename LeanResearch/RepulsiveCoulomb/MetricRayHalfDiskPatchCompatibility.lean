module

public import LeanResearch.RepulsiveCoulomb.MetricRayHalfDiskOverlap

@[expose] public section

/-! Successor source-only draft. Compatibility of actual arclength-aligned
bottom halfdisk patches follows from common real anchors and the actual
larger chart, rather than being accepted as a continuation certificate. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Two actual bottom patches agree throughout their entire overlap. The
first patch's displayed inverse-chart formula is ordinary constructed local
geometry; its larger chart contains the other patch by a proved metric bound. -/
theorem metricRay_halfDisk_patches_agree {Y : Type*} [MetricSpace Y]
    (ρ : NNReal → Y) (hρ : Isometry ρ) (ri rj : NNReal) {εi εj R : ℝ}
    (hεi : εi < (ri : ℝ)) (hR : 2 * εi ≤ R)
    (F : flatRayHalfDisk ri εi → Y) (G : flatRayHalfDisk rj εj → Y)
    (hF : Isometry F) (hG : Isometry G)
    (hFb : ∀ t : NNReal, ∀ ht : (t : ℂ) ∈ flatRayHalfDisk ri εi,
      F ⟨(t : ℂ), ht⟩ = ρ t)
    (hGb : ∀ t : NNReal, ∀ ht : (t : ℂ) ∈ flatRayHalfDisk rj εj,
      G ⟨(t : ℂ), ht⟩ = ρ t)
    (e : flatUpperDisk R ≃ᵢ ball (ρ ri) R)
    (hformula : ∀ z, ∃ hz : z.1 - (ri : ℂ) ∈ flatUpperDisk R,
      F z = (e ⟨z.1 - (ri : ℂ), hz⟩).1)
    {z : ℂ} (hi : z ∈ flatRayHalfDisk ri εi) (hj : z ∈ flatRayHalfDisk rj εj) :
    F ⟨z, hi⟩ = G ⟨z, hj⟩ := by
  obtain ⟨s, t, hst, hsi, hsj, hti, htj⟩ := flatRayHalfDisk_overlap_real_anchors hεi hi hj
  have hFbR := metricRay_halfDisk_overlap_image_mem_ball ρ hρ ri ri hεi hR F hF hFb hi hi
  have hGbR := metricRay_halfDisk_overlap_image_mem_ball ρ hρ ri rj hεi hR G hG hGb hi hj
  obtain ⟨hscoord, hsformula⟩ := hformula ⟨(s : ℂ), hsi⟩
  obtain ⟨htcoord, htformula⟩ := hformula ⟨(t : ℂ), hti⟩
  have hscoord' : (((s : ℝ) - ri : ℝ) : ℂ) ∈ flatUpperDisk R := by
    simpa only [Complex.ofReal_sub] using hscoord
  have htcoord' : (((t : ℝ) - ri : ℝ) : ℂ) ∈ flatUpperDisk R := by
    simpa only [Complex.ofReal_sub] using htcoord
  have hsmap : (e ⟨(((s : ℝ) - ri : ℝ) : ℂ), hscoord'⟩).1 = ρ s := by
    simpa only [Complex.ofReal_sub, hFb s hsi] using hsformula.symm
  have htmap : (e ⟨(((t : ℝ) - ri : ℝ) : ℂ), htcoord'⟩).1 = ρ t := by
    simpa only [Complex.ofReal_sub, hFb t hti] using htformula.symm
  have hst' : (s : ℝ) - ri ≠ (t : ℝ) - ri := by
    intro he
    exact hst (Subtype.ext (sub_left_inj.mp he))
  have hsDist : dist (⟨F ⟨z, hi⟩, hFbR⟩ : ball (ρ ri) R)
        (e ⟨(((s : ℝ) - ri : ℝ) : ℂ), hscoord'⟩) =
      dist (⟨G ⟨z, hj⟩, hGbR⟩ : ball (ρ ri) R)
        (e ⟨(((s : ℝ) - ri : ℝ) : ℂ), hscoord'⟩) := by
    have hFs := hF.dist_eq ⟨z, hi⟩ ⟨(s : ℂ), hsi⟩
    have hGs := hG.dist_eq ⟨z, hj⟩ ⟨(s : ℂ), hsj⟩
    rw [hFb s hsi] at hFs
    rw [hGb s hsj] at hGs
    change dist (F ⟨z, hi⟩) (e ⟨(((s : ℝ) - ri : ℝ) : ℂ), hscoord'⟩).1 =
      dist (G ⟨z, hj⟩) (e ⟨(((s : ℝ) - ri : ℝ) : ℂ), hscoord'⟩).1
    simpa only [hsmap] using hFs.trans hGs.symm
  have htDist : dist (⟨F ⟨z, hi⟩, hFbR⟩ : ball (ρ ri) R)
        (e ⟨(((t : ℝ) - ri : ℝ) : ℂ), htcoord'⟩) =
      dist (⟨G ⟨z, hj⟩, hGbR⟩ : ball (ρ ri) R)
        (e ⟨(((t : ℝ) - ri : ℝ) : ℂ), htcoord'⟩) := by
    have hFt := hF.dist_eq ⟨z, hi⟩ ⟨(t : ℂ), hti⟩
    have hGt := hG.dist_eq ⟨z, hj⟩ ⟨(t : ℂ), htj⟩
    rw [hFb t hti] at hFt
    rw [hGb t htj] at hGt
    change dist (F ⟨z, hi⟩) (e ⟨(((t : ℝ) - ri : ℝ) : ℂ), htcoord'⟩).1 =
      dist (G ⟨z, hj⟩) (e ⟨(((t : ℝ) - ri : ℝ) : ℂ), htcoord'⟩).1
    simpa only [htmap] using hFt.trans hGt.symm
  exact congrArg Subtype.val (metricHalfDisk_two_anchor_unique e hst' hscoord' htcoord' hsDist htDist)

/-- Construct all boundary patches and all pairwise compatibility, from the
actual ray and genuine retained halfdisk charts at its positive parameters. -/
theorem exists_compatible_metricRay_halfDisk_patches {Y ι : Type*} [MetricSpace Y]
    (ρ : NNReal → Y) (hρ : Isometry ρ) (r : ι → NNReal) (hr : ∀ i, 0 < r i)
    (C : ∀ i, MetricFlatHalfDiskChart Y (ρ (r i))) :
    ∃ ε : ι → ℝ, (∀ i, 0 < ε i) ∧
      ∃ F : ∀ i, flatRayHalfDisk (r i) (ε i) → Y,
        (∀ i, Isometry (F i)) ∧
        (∀ i (t : NNReal) (ht : (t : ℂ) ∈ flatRayHalfDisk (r i) (ε i)),
          F i ⟨(t : ℂ), ht⟩ = ρ t) ∧
        (∀ i j z (hi : z ∈ flatRayHalfDisk (r i) (ε i))
          (hj : z ∈ flatRayHalfDisk (r j) (ε j)), F i ⟨z, hi⟩ = F j ⟨z, hj⟩) ∧
        ∀ i z, 0 < z.1.im → Nonempty (MetricFlatDiskChart Y (F i z)) := by
  have hex (i : ι) := exists_metricRay_aligned_halfDisk_patch ρ hρ (r i) (hr i) (C i)
  choose ε hε hεr hεR htwo F hF hFb hreg e he using hex
  refine ⟨ε, hε, F, hF, hFb, ?_, hreg⟩
  intro i j z hi hj
  exact metricRay_halfDisk_patches_agree ρ hρ (r i) (r j) (hεr i) (htwo i)
    (F i) (F j) (hF i) (hF j) (hFb i) (hFb j) (e i) (he i) hi hj

end RepulsiveCoulomb
