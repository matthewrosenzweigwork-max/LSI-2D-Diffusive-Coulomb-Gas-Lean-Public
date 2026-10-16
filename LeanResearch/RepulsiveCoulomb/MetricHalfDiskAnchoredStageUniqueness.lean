import LeanResearch.RepulsiveCoulomb.MetricClosedFlatPatchUniqueness
import LeanResearch.RepulsiveCoulomb.MetricHalfDiskTwoAnchorUniqueness
import LeanResearch.RepulsiveCoulomb.ConvexDiskOverlap

/-! Full-line continuation uses one actual aligned boundary halfdisk, not a
positive corner. Two real anchors construct the local agreement; genuine full
interior charts propagate it to every point of the smaller closed stage. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem metricHalfDisk_anchored_stage_unique {Y : Type*} [MetricSpace Y]
    {p : Y} (C : MetricFlatHalfDiskChart Y p) {c b : ℝ}
    (hb : 0 < b) (hbC : b < C.radius)
    {K L : Set ℂ} (hK : Convex ℝ K) (hclosed : IsClosed K)
    (hne : (interior K).Nonempty) (hKL : K ⊆ L)
    (f : K → Y) (g : L → Y) (hf : Isometry f) (hg : Isometry g)
    (hcK : (c : ℂ) ∈ K) (hcbK : ((c + b : ℝ) : ℂ) ∈ K)
    (hfc : f ⟨(c : ℂ), hcK⟩ = p) (hgc : g ⟨(c : ℂ), hKL hcK⟩ = p)
    (hfb : f ⟨((c + b : ℝ) : ℂ), hcbK⟩ =
      (C.fromEuclidean ⟨(b : ℂ), by simp [flatUpperDisk, abs_of_pos hb, hbC]⟩).1)
    (hgb : g ⟨((c + b : ℝ) : ℂ), hKL hcbK⟩ =
      (C.fromEuclidean ⟨(b : ℂ), by simp [flatUpperDisk, abs_of_pos hb, hbC]⟩).1)
    (hregular : ∀ z : K, z.1 ∈ interior K → Nonempty (MetricFlatDiskChart Y (f z))) :
    ∀ z : K, f z = g ⟨z.1, hKL z.2⟩ := by
  classical
  let F : ℂ → Y := fun z ↦ if hz : z ∈ K then f ⟨z, hz⟩ else p
  let G : ℂ → Y := fun z ↦ if hz : z ∈ L then g ⟨z, hz⟩ else p
  have hF (z : ℂ) (hz : z ∈ K) : F z = f ⟨z, hz⟩ := by simp only [F, dif_pos hz]
  have hG (z : ℂ) (hz : z ∈ L) : G z = g ⟨z, hz⟩ := by simp only [G, dif_pos hz]
  have hdF : ∀ x ∈ K, ∀ z ∈ K, dist (F x) (F z) = dist x z := by
    intro x hx z hz; rw [hF x hx, hF z hz]; exact hf.dist_eq _ _
  have hdG : ∀ x ∈ K, ∀ z ∈ K, dist (G x) (G z) = dist x z := by
    intro x hx z hz; rw [hG x (hKL hx), hG z (hKL hz)]; exact hg.dist_eq _ _
  have hcharts : ∀ z ∈ interior K, ∃ q : Y, ∃ D : MetricFlatDiskChart Y q,
      F z ∈ ball q D.radius := by
    intro z hz
    obtain ⟨D⟩ := hregular ⟨z, interior_subset hz⟩ hz
    refine ⟨f ⟨z, interior_subset hz⟩, D, ?_⟩
    rw [hF z (interior_subset hz)]
    exact mem_ball_self D.radius_pos
  have hVne := convex_interior_inter_ball_nonempty hK hne hcK C.radius_pos
  have hagree : EqOn F G (interior K ∩ ball (c : ℂ) C.radius) := by
    intro z hz
    have hzK := interior_subset hz.1
    have hdFc : dist (f ⟨z, hzK⟩) p = dist z (c : ℂ) := by
      have h := hf.dist_eq ⟨z, hzK⟩ ⟨(c : ℂ), hcK⟩
      change dist (f ⟨z, hzK⟩) (f ⟨(c : ℂ), hcK⟩) = dist z (c : ℂ) at h
      simpa only [hfc] using h
    have hdGc : dist (g ⟨z, hKL hzK⟩) p = dist z (c : ℂ) := by
      have h := hg.dist_eq ⟨z, hKL hzK⟩ ⟨(c : ℂ), hKL hcK⟩
      change dist (g ⟨z, hKL hzK⟩) (g ⟨(c : ℂ), hKL hcK⟩) = dist z (c : ℂ) at h
      simpa only [hgc] using h
    have hfball : f ⟨z, hzK⟩ ∈ ball p C.radius := by rw [mem_ball, hdFc]; exact hz.2
    have hgball : g ⟨z, hKL hzK⟩ ∈ ball p C.radius := by rw [mem_ball, hdGc]; exact hz.2
    have hbD : (b : ℂ) ∈ flatUpperDisk C.radius := by simp [flatUpperDisk, abs_of_pos hb, hbC]
    have hzeroD : (0 : ℂ) ∈ flatUpperDisk C.radius := (flatUpperDiskZero C.radius_pos).2
    have hdc : dist (⟨f ⟨z, hzK⟩, hfball⟩ : ball p C.radius) (C.fromEuclidean ⟨0, hzeroD⟩) =
        dist (⟨g ⟨z, hKL hzK⟩, hgball⟩ : ball p C.radius) (C.fromEuclidean ⟨0, hzeroD⟩) := by
      change dist (f ⟨z, hzK⟩) (C.fromEuclidean ⟨0, hzeroD⟩).1 =
        dist (g ⟨z, hKL hzK⟩) (C.fromEuclidean ⟨0, hzeroD⟩).1
      have hc0 : (C.fromEuclidean ⟨0, hzeroD⟩).1 = p := C.center
      rw [hc0]
      exact hdFc.trans hdGc.symm
    have hdb : dist (⟨f ⟨z, hzK⟩, hfball⟩ : ball p C.radius) (C.fromEuclidean ⟨(b : ℂ), hbD⟩) =
        dist (⟨g ⟨z, hKL hzK⟩, hgball⟩ : ball p C.radius) (C.fromEuclidean ⟨(b : ℂ), hbD⟩) := by
      have hf' := hf.dist_eq ⟨z, hzK⟩ ⟨((c + b : ℝ) : ℂ), hcbK⟩
      have hg' := hg.dist_eq ⟨z, hKL hzK⟩ ⟨((c + b : ℝ) : ℂ), hKL hcbK⟩
      rw [hfb] at hf'
      rw [hgb] at hg'
      exact hf'.trans hg'.symm
    rw [hF z hzK, hG z (hKL hzK)]
    exact congrArg Subtype.val (metricHalfDisk_two_anchor_unique C.fromEuclidean
      (ne_of_lt hb) hzeroD hbD hdc hdb)
  have heq := flat_isometries_eqOn_closed_convex_of_open_germ hK hclosed hne hdF hdG hcharts
    (isOpen_interior.inter isOpen_ball) hVne inter_subset_left hagree
  intro z
  simpa only [hF z.1 z.2, hG z.1 (hKL z.2)] using heq z.2

end RepulsiveCoulomb
