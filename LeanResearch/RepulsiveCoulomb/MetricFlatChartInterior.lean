import LeanResearch.RepulsiveCoulomb.MetricFlatDiskPatchExtension
import LeanResearch.RepulsiveCoulomb.MetricFlatHalfDiskChart

/-! Successor source-only draft. Interior points of an actual isometric
Euclidean patch onto a whole metric ball have actual full flat metric disks.
This supplies regular target charts inside retained halfdisk patches. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- Restrict and recenter an actual whole-ball chart at a source interior
point. Both inverse maps are constructed, with no local-flatness certificate. -/
theorem exists_metricFlatDiskChart_of_patch_interior {Y : Type*} [MetricSpace Y]
    {A : Set ℂ} {p : Y} {R : ℝ} (e : A ≃ᵢ ball p R) (x : A)
    (hx : x.1 ∈ interior A) : Nonempty (MetricFlatDiskChart Y (e x).1) := by
  obtain ⟨r, hr, hrA⟩ := Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  let q : Y := (e x).1
  have hgap : 0 < R - dist q p := sub_pos.mpr (e x).2
  let ε := min r (R - dist q p)
  have hε : 0 < ε := lt_min hr hgap
  have hsource (w : ball (0 : ℂ) ε) : x.1 + w.1 ∈ A := by
    apply hrA
    change dist (x.1 + w.1) x.1 < r
    rw [dist_eq_norm, add_sub_cancel_left]
    have hw : ‖w.1‖ < ε := by simpa only [mem_ball, dist_zero_right] using w.2
    exact hw.trans_le (min_le_left _ _)
  have htarget (z : ball q ε) : z.1 ∈ ball p R := by
    have ht := dist_triangle z.1 q p
    have hz : dist z.1 q < ε := z.2
    have hbound : ε ≤ R - dist q p := min_le_right _ _
    change dist z.1 p < R
    linarith
  have hF (z : ball q ε) : (e.symm ⟨z.1, htarget z⟩).1 - x.1 ∈ ball (0 : ℂ) ε := by
    rw [mem_ball, dist_zero_right]
    rw [← dist_eq_norm]
    change dist (e.symm ⟨z.1, htarget z⟩) x < ε
    rw [← e.dist_eq, e.apply_symm_apply]
    exact z.2
  let F : ball q ε → ball (0 : ℂ) ε := fun z ↦
    ⟨(e.symm ⟨z.1, htarget z⟩).1 - x.1, hF z⟩
  have hG (w : ball (0 : ℂ) ε) : (e ⟨x.1 + w.1, hsource w⟩).1 ∈ ball q ε := by
    change dist (e ⟨x.1 + w.1, hsource w⟩) (e x) < ε
    rw [e.dist_eq]
    change dist (x.1 + w.1) x.1 < ε
    simpa only [dist_eq_norm, add_sub_cancel_left, mem_ball, dist_zero_right, sub_zero] using w.2
  let G : ball (0 : ℂ) ε → ball q ε := fun w ↦
    ⟨(e ⟨x.1 + w.1, hsource w⟩).1, hG w⟩
  have hleft : Function.LeftInverse G F := by
    intro z
    apply Subtype.ext
    have he : (⟨x.1 + ((e.symm ⟨z.1, htarget z⟩).1 - x.1), hsource (F z)⟩ : A) =
        e.symm ⟨z.1, htarget z⟩ := by
      apply Subtype.ext
      dsimp
      abel
    change (e ⟨x.1 + ((e.symm ⟨z.1, htarget z⟩).1 - x.1), hsource (F z)⟩).1 = z.1
    rw [he, e.apply_symm_apply]
  have hright : Function.RightInverse G F := by
    intro w
    apply Subtype.ext
    have he : (⟨(e ⟨x.1 + w.1, hsource w⟩).1, htarget (G w)⟩ : ball p R) =
        e ⟨x.1 + w.1, hsource w⟩ := rfl
    change (e.symm ⟨(e ⟨x.1 + w.1, hsource w⟩).1, htarget (G w)⟩).1 - x.1 = w.1
    rw [he, e.symm_apply_apply, add_sub_cancel_left]
  have hFi : Isometry F := by
    apply Isometry.of_dist_eq
    intro z w
    change dist ((e.symm ⟨z.1, htarget z⟩).1 - x.1)
      ((e.symm ⟨w.1, htarget w⟩).1 - x.1) = dist z.1 w.1
    rw [dist_sub_right]
    exact e.symm.dist_eq _ _
  let E : ball q ε ≃ᵢ ball (0 : ℂ) ε :=
    { toFun := F, invFun := G, left_inv := hleft, right_inv := hright, isometry_toFun := hFi }
  refine ⟨⟨ε, hε, E, ?_⟩⟩
  change (e.symm ⟨q, htarget ⟨q, mem_ball_self hε⟩⟩).1 - x.1 = 0
  have he : (⟨q, htarget ⟨q, mem_ball_self hε⟩⟩ : ball p R) = e x := rfl
  rw [he, e.symm_apply_apply, sub_self]

/-- Strictly upper points of the halfdisk are ordinary full flat points. -/
theorem MetricFlatHalfDiskChart.exists_full_at {Y : Type*} [MetricSpace Y] {p : Y}
    (C : MetricFlatHalfDiskChart Y p) (z : flatUpperDisk C.radius) (hz : 0 < z.1.im) :
    Nonempty (MetricFlatDiskChart Y (C.fromEuclidean z).1) := by
  apply exists_metricFlatDiskChart_of_patch_interior C.fromEuclidean z
  let W : Set ℂ := {w | ‖w‖ < C.radius} ∩ {w | 0 < w.im}
  have hW : IsOpen W :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const Complex.continuous_im)
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (hW.mem_nhds ⟨z.2.1, hz⟩) (fun w hw ↦ ⟨hw.1, hw.2.le⟩)

end RepulsiveCoulomb
