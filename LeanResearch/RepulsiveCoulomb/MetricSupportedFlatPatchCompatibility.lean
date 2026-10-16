import LeanResearch.RepulsiveCoulomb.MetricClosedFlatPatchUniqueness
import LeanResearch.RepulsiveCoulomb.MetricFlatChartInterior
import LeanResearch.RepulsiveCoulomb.ConvexDiskOverlap

/-! Post-freeze successor. Genuine overlap comparison for mixed full-disk and
supporting-halfdisk patches. A common convex supporting set H contains the old
rectangle. Actual independent patch equivalences and their old-map agreement
are inputs; all new-new compatibility is proved, never assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Version without closedness: a convex source is contained in the closure
of its interior whenever that interior is nonempty. -/
theorem flat_isometries_eqOn_convex_of_open_germ {Y : Type*} [MetricSpace Y]
    {K : Set ℂ} (hK : Convex ℝ K) (hne : (interior K).Nonempty)
    {f g : ℂ → Y}
    (hf : ∀ x ∈ K, ∀ z ∈ K, dist (f x) (f z) = dist x z)
    (hg : ∀ x ∈ K, ∀ z ∈ K, dist (g x) (g z) = dist x z)
    (hcharts : ∀ x ∈ interior K, ∃ p : Y, ∃ C : MetricFlatDiskChart Y p,
      f x ∈ ball p C.radius)
    {V : Set ℂ} (hV : IsOpen V) (hVne : V.Nonempty) (hVK : V ⊆ interior K)
    (hagree : EqOn f g V) : EqOn f g K := by
  have heq := flat_isometries_eqOn_of_open_germ isOpen_interior hK.interior.isPreconnected
    (fun x hx z hz ↦ hf x (interior_subset hx) z (interior_subset hz))
    (fun x hx z hz ↦ hg x (interior_subset hx) z (interior_subset hz))
    hcharts hV hVne hVK hagree
  have hfl : LipschitzOnWith 1 f K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx z hz
    simpa only [NNReal.coe_one, one_mul, hf x hx z hz] using (le_refl (dist x z))
  have hgl : LipschitzOnWith 1 g K := by
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx z hz
    simpa only [NNReal.coe_one, one_mul, hg x hx z hz] using (le_refl (dist x z))
  apply heq.of_subset_closure hfl.continuousOn hgl.continuousOn interior_subset
  rw [hK.closure_interior_eq_closure_of_nonempty_interior hne]
  exact subset_closure

/-- Supported patch sources; H may be the whole plane or the actual retained
supporting halfplane of the prescribed compact edge. -/
def supportedFlatPatch (H : Set ℂ) (q : ℂ) (R : ℝ) : Set ℂ := ball q R ∩ H

/-- A nonempty pair of supported patches contains old two-dimensional points.
Only source geometry is used. No target overlap/compatibility premise occurs. -/
theorem supportedFlatPatch_old_interior_overlap {K H : Set ℂ}
    (hK : Convex ℝ K) (hne : (interior K).Nonempty) (hKH : K ⊆ H)
    {x z : ℂ} (hx : x ∈ K) (hz : z ∈ K) {r s : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hinter : (supportedFlatPatch H x r ∩ supportedFlatPatch H z s).Nonempty) :
    (interior K ∩ interior (supportedFlatPatch H x r ∩ supportedFlatPatch H z s)).Nonempty := by
  have hballs : (ball x r ∩ ball z s).Nonempty := hinter.mono fun _ hw ↦ ⟨hw.1.1, hw.2.1⟩
  obtain ⟨w, hwK, hwB⟩ := convex_centered_balls_old_interior_overlap hK hne hx hz hr hs hballs
  have hwH : w ∈ interior H := interior_mono hKH hwK
  refine ⟨w, hwK, ?_⟩
  simp only [supportedFlatPatch, interior_inter, isOpen_ball.interior_eq, mem_inter_iff]
  exact ⟨⟨hwB.1, hwH⟩, ⟨hwB.2, hwH⟩⟩

/-- All mixed new patches agree, even beyond the old rectangle. The proof
uses actual whole metric-ball equivalences to construct flat disks at interior
image points, then propagates their genuine old-interior agreement. -/
theorem supported_flat_patches_compatible {Y ι : Type*} [MetricSpace Y]
    {K H : Set ℂ} (hK : Convex ℝ K) (hne : (interior K).Nonempty)
    (hH : Convex ℝ H) (hKH : K ⊆ H) (f : K → Y)
    (q : ι → K) (R : ι → ℝ) (hR : ∀ i, 0 < R i)
    (e : ∀ i, supportedFlatPatch H (q i).1 (R i) ≃ᵢ ball (f (q i)) (R i))
    (hold : ∀ i (x : K) (hx : x.1 ∈ supportedFlatPatch H (q i).1 (R i)),
      (e i ⟨x.1, hx⟩).1 = f x) :
    ∀ i j z (hi : z ∈ supportedFlatPatch H (q i).1 (R i))
      (hj : z ∈ supportedFlatPatch H (q j).1 (R j)), (e i ⟨z, hi⟩).1 = (e j ⟨z, hj⟩).1 := by
  classical
  intro i j z hi hj
  let Ai := supportedFlatPatch H (q i).1 (R i)
  let Aj := supportedFlatPatch H (q j).1 (R j)
  let D := Ai ∩ Aj
  let fi : ℂ → Y := fun x ↦ if hx : x ∈ Ai then (e i ⟨x, hx⟩).1 else f (q i)
  let fj : ℂ → Y := fun x ↦ if hx : x ∈ Aj then (e j ⟨x, hx⟩).1 else f (q j)
  have hfi (x : ℂ) (hx : x ∈ Ai) : fi x = (e i ⟨x, hx⟩).1 := by simp only [fi, dif_pos hx]
  have hfj (x : ℂ) (hx : x ∈ Aj) : fj x = (e j ⟨x, hx⟩).1 := by simp only [fj, dif_pos hx]
  have hD : Convex ℝ D := ((convex_ball _ _).inter hH).inter ((convex_ball _ _).inter hH)
  have hVne : (interior K ∩ interior D).Nonempty :=
    supportedFlatPatch_old_interior_overlap hK hne hKH (q i).2 (q j).2 (hR i) (hR j) ⟨z, hi, hj⟩
  have hDne : (interior D).Nonempty := hVne.mono inter_subset_right
  have hdFi : ∀ x ∈ D, ∀ w ∈ D, dist (fi x) (fi w) = dist x w := by
    intro x hx w hw
    rw [hfi x hx.1, hfi w hw.1]
    exact (e i).dist_eq _ _
  have hdFj : ∀ x ∈ D, ∀ w ∈ D, dist (fj x) (fj w) = dist x w := by
    intro x hx w hw
    rw [hfj x hx.2, hfj w hw.2]
    exact (e j).dist_eq _ _
  have hcharts : ∀ x ∈ interior D, ∃ p : Y, ∃ C : MetricFlatDiskChart Y p, fi x ∈ ball p C.radius := by
    intro x hx
    have hxi : x ∈ interior Ai := interior_mono inter_subset_left hx
    obtain ⟨C⟩ := exists_metricFlatDiskChart_of_patch_interior (e i) ⟨x, interior_subset hxi⟩ hxi
    refine ⟨(e i ⟨x, interior_subset hxi⟩).1, C, ?_⟩
    rw [hfi x (interior_subset hxi)]
    exact mem_ball_self C.radius_pos
  have hagree : EqOn fi fj (interior K ∩ interior D) := by
    intro x hx
    have hxd : x ∈ D := interior_subset hx.2
    rw [hfi x hxd.1, hfj x hxd.2,
      hold i ⟨x, interior_subset hx.1⟩ hxd.1,
      hold j ⟨x, interior_subset hx.1⟩ hxd.2]
  have heq := flat_isometries_eqOn_convex_of_open_germ hD hDne hdFi hdFj hcharts
    (isOpen_interior.inter isOpen_interior) hVne inter_subset_right hagree
  have hz := heq ⟨hi, hj⟩
  rwa [hfi z hi, hfj z hj] at hz

end RepulsiveCoulomb
