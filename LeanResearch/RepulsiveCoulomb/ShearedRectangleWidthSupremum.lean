module

public import LeanResearch.RepulsiveCoulomb.ShearedRectangleGeometry
public import LeanResearch.RepulsiveCoulomb.DirectedFlatIsometryUnion

@[expose] public section

/-! Newly authored after source loss; this is not a recovery of the old body.

Compatible isometries on a nonempty bounded family of positive-width literal
sheared rectangles extend to the rectangle at the supremum width. The source
density statement is proved by clipping the transverse coordinate at a width
chosen from the actual family. The target map is the accepted genuine Cauchy
extension of the directed union. No limiting map or attainment certificate is
an input, and no geometric stage compatibility is asserted here.
-/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Unit transverse direction makes the transverse coordinate arclength. -/
theorem flatShearedPoint_dist_transverse {v : ℂ} (hv : ‖v‖ = 1)
    (r u w : ℝ) :
    dist (flatShearedPoint v r u) (flatShearedPoint v r w) = |u - w| := by
  have he : flatShearedPoint v r u - flatShearedPoint v r w = ((u - w : ℝ) : ℂ) * v := by
    simp only [flatShearedPoint, Complex.ofReal_sub]
    ring
  rw [dist_eq_norm, he, norm_mul, hv, mul_one, Complex.norm_real, Real.norm_eq_abs]

/-- Every point of the supremum rectangle is a limit of points in actual
stages, including the entire top edge and both top corners. No member of the
width family is required to attain the supremum. -/
theorem closure_iUnion_shearedRectangles {v : ℂ} (hv : ‖v‖ = 1) (R : ℝ)
    {W : Set ℝ} (hWne : W.Nonempty) (hWpos : ∀ s ∈ W, 0 < s) (hWbound : BddAbove W) :
    closure (⋃ s : W, flatShearedRectangle v R s.1) =
      flatShearedRectangle v R (sSup W) := by
  apply Subset.antisymm
  · apply closure_minimal
    · intro z hz
      obtain ⟨s, hs⟩ := mem_iUnion.mp hz
      exact flatShearedRectangle_mono le_rfl (le_csSup hWbound s.2) hs
    · exact (flatShearedRectangle_compact v R (sSup W)).isClosed
  · rintro z ⟨r, hr, u, hu, rfl⟩
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    have husup : u - ε < sSup W := (sub_lt_self u hε).trans_le hu.2
    obtain ⟨s, hs, hus⟩ := exists_lt_of_lt_csSup hWne husup
    let w := min u s
    have hw0 : 0 ≤ w := le_min hu.1 (hWpos s hs).le
    have hws : w ≤ s := min_le_right _ _
    have hwu : w ≤ u := min_le_left _ _
    have huεw : u - ε < w := lt_min (sub_lt_self u hε) hus
    refine ⟨flatShearedPoint v r w,
      mem_iUnion.mpr ⟨⟨s, hs⟩, r, hr, w, ⟨hw0, hws⟩, rfl⟩, ?_⟩
    rw [flatShearedPoint_dist_transverse hv, abs_of_nonneg (sub_nonneg.mpr hwu)]
    linarith

/-- Construct the completed map at the supremum of the supplied widths from
the actual complete target and the explicitly compatible isometric stages.
Agreement is literal on every old stage, and the conclusion is all-pairs
isometry on the closed supremum rectangle. -/
theorem exists_shearedRectangle_supremum_isometry
    {Y : Type*} [MetricSpace Y] [CompleteSpace Y]
    {v : ℂ} (hv : ‖v‖ = 1) (R : ℝ)
    {W : Set ℝ} (hWne : W.Nonempty) (hWpos : ∀ s ∈ W, 0 < s) (hWbound : BddAbove W)
    (f : ∀ s : W, flatShearedRectangle v R s.1 → Y)
    (hf : ∀ s, Isometry (f s))
    (hcompat : ∀ s t : W, ∀ z (hs : z ∈ flatShearedRectangle v R s.1)
      (ht : z ∈ flatShearedRectangle v R t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩) :
    ∃ F : flatShearedRectangle v R (sSup W) → Y, Isometry F ∧
      ∀ s (z : flatShearedRectangle v R s.1),
        F ⟨z.1, flatShearedRectangle_mono le_rfl (le_csSup hWbound s.2) z.2⟩ = f s z := by
  let U : W → Set ℂ := fun s ↦ flatShearedRectangle v R s.1
  have hdir : Directed (· ⊆ ·) U := by
    intro s t
    rcases le_total s.1 t.1 with hst | hts
    · exact ⟨t, flatShearedRectangle_mono le_rfl hst, subset_rfl⟩
    · exact ⟨s, subset_rfl, flatShearedRectangle_mono le_rfl hts⟩
  have hclosure := closure_iUnion_shearedRectangles hv R hWne hWpos hWbound
  let incl : flatShearedRectangle v R (sSup W) → closure (⋃ s, U s) :=
    fun z ↦ ⟨z.1, hclosure.symm ▸ z.2⟩
  have hinc : Isometry incl := fun _ _ ↦ rfl
  let F := directedFlatClosure U f hcompat ∘ incl
  refine ⟨F, (directedFlatClosure_isometry U f hdir hcompat hf).comp hinc, ?_⟩
  intro s z
  exact directedFlatClosure_apply U f hdir hcompat hf s z

end RepulsiveCoulomb
