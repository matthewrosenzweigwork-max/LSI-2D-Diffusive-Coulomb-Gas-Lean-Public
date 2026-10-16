import LeanResearch.RepulsiveCoulomb.MetricRayHalfDiskPatchedUnion
import LeanResearch.RepulsiveCoulomb.NormalRectangleSource
import Mathlib.Topology.MetricSpace.Thickening

/-! NEW source-only implementation. Construct a genuine positive-width
compact bottom collar from actual metric halfdisk charts. The width follows
from a finite chart cover and compactness, and is not a hypothesis. Generic
metric targets receive only local distance preservation. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- On any compact positive segment of a minimizing ray, genuine boundary
halfdisk charts produce a positive-width normal collar. Its bottom is the
prescribed ray, and every positive-height image point has a full disk chart.
There is no requirement that the real interval be nonempty. -/
theorem exists_metricRay_compact_initial_collar {Y : Type*} [MetricSpace Y]
    (ρ : NNReal → Y) (hρ : Isometry ρ) {a b : ℝ} (ha : 0 < a)
    (H : ∀ t : Icc a b, MetricFlatHalfDiskChart Y
      (ρ ⟨t.1, ha.le.trans t.2.1⟩)) :
    ∃ η : ℝ, 0 < η ∧ ∃ G : flatNormalRectangle a b η → Y,
      (∀ t : NNReal, ∀ ht : (t : ℂ) ∈ flatNormalRectangle a b η,
        G ⟨(t : ℂ), ht⟩ = ρ t) ∧
      (∀ p, ∃ V : Set (flatNormalRectangle a b η), IsOpen V ∧ p ∈ V ∧
        ∀ x ∈ V, ∀ z ∈ V, dist (G x) (G z) = dist x z) ∧
      ∀ z, 0 < z.1.im → Nonempty (MetricFlatDiskChart Y (G z)) := by
  classical
  let r : Icc a b → NNReal := fun t ↦ ⟨t.1, ha.le.trans t.2.1⟩
  have hr : ∀ t, 0 < r t := by
    intro t
    show 0 < t.1
    exact ha.trans_le t.2.1
  obtain ⟨ε, hε, F, hFb, hFlocal, hFreg⟩ :=
    exists_metricRay_halfDisk_patched_union ρ hρ r hr H
  let K : Set ℂ := Complex.ofReal '' Icc a b
  have hK : IsCompact K := isCompact_Icc.image Complex.continuous_ofReal
  let U : Icc a b → Set ℂ := fun t ↦ ball (r t : ℂ) (ε t)
  have hcover : K ⊆ ⋃ t, U t := by
    rintro z ⟨t, ht, rfl⟩
    exact mem_iUnion.mpr ⟨⟨t, ht⟩, mem_ball_self (hε ⟨t, ht⟩)⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover U (fun _ ↦ isOpen_ball) hcover
  let W : Set ℂ := ⋃ t ∈ T, U t
  have hW : IsOpen W := isOpen_biUnion fun _ _ ↦ isOpen_ball
  obtain ⟨η, hη, hηW⟩ := hK.exists_cthickening_subset_open hW hT
  have hsub : flatNormalRectangle a b η ⊆ flatRayHalfDiskPatchedSet r ε := by
    intro z hz
    have hbase : (z.re : ℂ) ∈ K := ⟨z.re, hz.1, rfl⟩
    have hd : dist z (z.re : ℂ) ≤ η := by
      rw [Complex.dist_of_re_eq (by simp), Real.dist_eq, Complex.ofReal_im, sub_zero,
        abs_of_nonneg hz.2.1]
      exact hz.2.2
    have hzW : z ∈ W :=
      hηW (mem_cthickening_of_dist_le z (z.re : ℂ) η K hbase hd)
    obtain ⟨t, ht⟩ := mem_iUnion.mp hzW
    obtain ⟨_, hzt⟩ := mem_iUnion.mp ht
    exact mem_iUnion.mpr ⟨t, hzt, hz.2.1⟩
  let incl : flatNormalRectangle a b η → flatRayHalfDiskPatchedSet r ε :=
    fun z ↦ ⟨z.1, hsub z.2⟩
  have hincl : Isometry incl := by
    apply Isometry.of_dist_eq
    intro x z
    rfl
  let G : flatNormalRectangle a b η → Y := F ∘ incl
  refine ⟨η, hη, G, ?_, ?_, ?_⟩
  · intro t ht
    exact hFb t (hsub ht)
  · intro p
    obtain ⟨V, hV, hp, hd⟩ := hFlocal (incl p)
    refine ⟨incl ⁻¹' V, hV.preimage hincl.continuous, hp, ?_⟩
    intro x hx z hz
    exact (hd (incl x) hx (incl z) hz).trans (hincl.dist_eq x z)
  · intro z hz
    exact hFreg (incl z) hz

end RepulsiveCoulomb
