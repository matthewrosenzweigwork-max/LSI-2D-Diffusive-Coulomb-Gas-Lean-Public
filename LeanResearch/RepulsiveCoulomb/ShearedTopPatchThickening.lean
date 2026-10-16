module

public import LeanResearch.RepulsiveCoulomb.MetricSupportedFlatPatchedUnion
public import LeanResearch.RepulsiveCoulomb.ShearedRectangleInteriorGeometry
public import LeanResearch.RepulsiveCoulomb.ShearedRectangleWidthSupremum
public import Mathlib.Topology.MetricSpace.Thickening

@[expose] public section

/-! NEW implementation after source loss. The whole closed top, including
both endpoints, has a finite ambient-open ball cover. Compactness gives one
positive metric thickening; Euclidean source geometry then gives a genuine
larger rectangle interior contained in the supported patch union. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- A point of the entire closed top edge, with endpoints retained. -/
def shearedTopPoint (v : ℂ) (R s : ℝ) (hs : 0 ≤ s) (r : Icc (0 : ℝ) R) :
    flatShearedRectangle v R s :=
  ⟨flatShearedPoint v r.1 s, r.1, r.2, s, ⟨hs, le_rfl⟩, rfl⟩

/-- The closed top edge as an actual compact subset of the Euclidean plane. -/
def shearedTopSet (v : ℂ) (R s : ℝ) : Set ℂ :=
  (fun r : ℝ ↦ flatShearedPoint v r s) '' Icc (0 : ℝ) R

theorem shearedTopSet_compact (v : ℂ) (R s : ℝ) :
    IsCompact (shearedTopSet v R s) := by
  apply isCompact_Icc.image
  unfold flatShearedPoint
  fun_prop

/-- Pointwise positive top radii yield a finite open cover of the whole top
and a positive closed metric thickening contained in that finite union. No
uniform radius or open-neighborhood conclusion is assumed. -/
theorem exists_sheared_top_finite_thickening {v : ℂ} {R s : ℝ}
    (B : Icc (0 : ℝ) R → ℝ) (hB : ∀ r, 0 < B r) :
    ∃ t : Finset (Icc (0 : ℝ) R), ∃ ε : ℝ, 0 < ε ∧
      Metric.cthickening ε (shearedTopSet v R s) ⊆
        ⋃ r ∈ t, ball (flatShearedPoint v r.1 s) (B r) := by
  classical
  let U : Icc (0 : ℝ) R → Set ℂ := fun r ↦ ball (flatShearedPoint v r.1 s) (B r)
  have hcover : shearedTopSet v R s ⊆ ⋃ r, U r := by
    rintro z ⟨r, hr, rfl⟩
    exact mem_iUnion.mpr ⟨⟨r, hr⟩, mem_ball_self (hB ⟨r, hr⟩)⟩
  obtain ⟨t, ht⟩ := (shearedTopSet_compact v R s).elim_finite_subcover U
    (fun _ ↦ isOpen_ball) hcover
  have hopen : IsOpen (⋃ r ∈ t, U r) :=
    isOpen_iUnion fun _ ↦ isOpen_iUnion fun _ ↦ isOpen_ball
  obtain ⟨ε, hε, hεU⟩ := (shearedTopSet_compact v R s).exists_cthickening_subset_open
    hopen ht
  exact ⟨t, ε, hε, hεU⟩

/-- A positive increase of the height stays within the actual supported
patch union. The general-H inclusion is a NEW explicit source-side premise;
it is automatic for H = univ. There is no target-space assumption here. -/
theorem exists_sheared_top_patch_thickening {v : ℂ} (hv : ‖v‖ = 1)
    (hvi : v.im ≠ 0) {R s delta : ℝ} (hR : 0 < R) (hs : 0 < s)
    (hsdelta : s < delta) {H : Set ℂ}
    (hdeltaH : flatShearedRectangle v R delta ⊆ H)
    (B : Icc (0 : ℝ) R → ℝ) (hB : ∀ r, 0 < B r) :
    ∃ h : ℝ, 0 < h ∧ s + h < delta ∧
      interior (flatShearedRectangle v R (s + h)) ⊆
        supportedFlatPatchedSet H (shearedTopPoint v R s hs.le) B := by
  classical
  obtain ⟨t, ε, hε, hεU⟩ := exists_sheared_top_finite_thickening (v := v) (s := s) B hB
  let h : ℝ := min (ε / 2) ((delta - s) / 2)
  have hh : 0 < h := lt_min (half_pos hε) (half_pos (sub_pos.mpr hsdelta))
  have hhε : h ≤ ε / 2 := min_le_left _ _
  have hhdelta : h ≤ (delta - s) / 2 := min_le_right _ _
  have hnewdelta : s + h < delta := by linarith
  have hnewH : flatShearedRectangle v R (s + h) ⊆ H :=
    (flatShearedRectangle_mono le_rfl hnewdelta.le).trans hdeltaH
  refine ⟨h, hh, hnewdelta, ?_⟩
  intro z hz
  have hzH : z ∈ H := hnewH (interior_subset hz)
  rw [flatShearedRectangle_interior hvi] at hz
  obtain ⟨⟨r, u⟩, ⟨hr, hu⟩, rfl⟩ := hz
  by_cases hus : u < s
  · apply Or.inl
    rw [flatShearedRectangle_interior hvi]
    exact ⟨(r, u), ⟨hr, ⟨hu.1, hus⟩⟩, rfl⟩
  · have hsu : s ≤ u := le_of_not_gt hus
    have htop : flatShearedPoint v r s ∈ shearedTopSet v R s :=
      ⟨r, ⟨hr.1.le, hr.2.le⟩, rfl⟩
    have hdist : dist (flatShearedPoint v r u) (flatShearedPoint v r s) ≤ ε := by
      rw [flatShearedPoint_dist_transverse hv, abs_of_nonneg (sub_nonneg.mpr hsu)]
      linarith [hu.2]
    have hzU := hεU (Metric.mem_cthickening_of_dist_le
      (flatShearedPoint v r u) (flatShearedPoint v r s) ε (shearedTopSet v R s) htop hdist)
    obtain ⟨a, ha⟩ := mem_iUnion.mp hzU
    obtain ⟨_, hza⟩ := mem_iUnion.mp ha
    exact Or.inr (mem_iUnion.mpr ⟨a, hza, hzH⟩)

end RepulsiveCoulomb
