module

public import LeanResearch.RepulsiveCoulomb.MetricHalfDiskBoundaryAlignment
public import LeanResearch.RepulsiveCoulomb.MetricHalfDiskTwoAnchorUniqueness
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section

/-!
SOURCE-ONLY, UNCOMPILED. A ray with genuine whole retained metric halfdisks
at every positive time cannot branch from a second isometric ray after a
positive common prefix. This is a relative halfdisk argument. It does not
assert the false general uniqueness of ambient continuation at cone atoms.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- Continuous induction propagates the literal prefix. At its endpoint a
previous common point and the center are two real-diameter anchors; distances
to these anchors determine the next point inside the same retained halfdisk.
No global target geodesic uniqueness is required. -/
theorem metricHalfDisk_ray_prefix_continuation {Y : Type*} [MetricSpace Y]
    (f g : NNReal → Y) (hf : Isometry f) (hg : Isometry g)
    (hcharts : ∀ t : NNReal, 0 < t → Nonempty (MetricFlatHalfDiskChart Y (g t)))
    {ε : ℝ} (hε : 0 < ε) (hseed : ∀ t : NNReal, t.1 ≤ ε → f t = g t) :
    f = g := by
  let S : Set NNReal := {t | f t = g t}
  have hSc : IsClosed S := isClosed_eq hf.continuous hg.continuous
  have hS0 : (0 : NNReal) ∈ S := hseed 0 hε.le
  have hstep (t : NNReal) (hprefix : Icc (0 : NNReal) t ⊆ S) : S ∈ 𝓝 t := by
    by_cases ht0 : t = 0
    · subst t
      apply Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hε))
      intro u hu
      apply hseed u
      have hu' : dist u (0 : NNReal) < ε := hu
      rw [NNReal.dist_eq, NNReal.coe_zero, sub_zero] at hu'
      exact (le_abs_self (u : ℝ)).trans hu'.le
    · have ht : 0 < (t : ℝ) :=
        lt_of_le_of_ne t.2 (fun he ↦ ht0 (Subtype.ext he.symm))
      have hft : f t = g t := hprefix ⟨t.2, le_rfl⟩
      obtain ⟨C⟩ := hcharts t ht
      let L := min t.1 C.radius / 2
      have hL : 0 < L := half_pos (lt_min ht C.radius_pos)
      have hLt : L < t.1 :=
        (half_lt_self (lt_min ht C.radius_pos)).trans_le (min_le_left _ _)
      have hLC : L < C.radius :=
        (half_lt_self (lt_min ht C.radius_pos)).trans_le (min_le_right _ _)
      let k : Icc (-L) L → NNReal := fun u ↦ ⟨t.1 + u.1, by linarith [u.2.1]⟩
      have hk : Isometry k := by
        apply Isometry.of_dist_eq
        intro u v
        change |(t.1 + u.1) - (t.1 + v.1)| = |u.1 - v.1|
        congr 1
        ring
      have hk0 : k (complexSymmetricIntervalZero hL) = t := by
        apply Subtype.ext
        simp only [k, complexSymmetricIntervalZero, add_zero]
      obtain ⟨e, he0, heline⟩ := C.exists_aligned_to_short_interval hL hLC
        (g ∘ k) (hg.comp hk) (congrArg g hk0)
      let b : Icc (-L) L := ⟨-L / 2, by constructor <;> linarith⟩
      have hb : b.1 ≠ 0 := by dsimp [b]; linarith
      have hkb : k b ≤ t := by change t.1 + (-L / 2) ≤ t.1; linarith
      have hfb : f (k b) = g (k b) := hprefix ⟨(k b).2, hkb⟩
      have h0mem : (0 : ℂ) ∈ flatUpperDisk C.radius :=
        (flatUpperDiskZero C.radius_pos).2
      have hbmem : (b.1 : ℂ) ∈ flatUpperDisk C.radius :=
        (halfDiskIntervalReal hLC b).2
      have heb : (e ⟨(b.1 : ℂ), hbmem⟩).1 = g (k b) := heline b
      apply Filter.mem_of_superset (isOpen_ball.mem_nhds (mem_ball_self hL))
      intro u hu
      have huL : dist u t < L := hu
      have hfball : f u ∈ ball (g t) C.radius := by
        change dist (f u) (g t) < C.radius
        calc
          dist (f u) (g t) = dist (f u) (f t) :=
            congrArg (fun w ↦ dist (f u) w) hft.symm
          _ = dist u t := hf.dist_eq u t
          _ < C.radius := huL.trans hLC
      have hgball : g u ∈ ball (g t) C.radius := by
        change dist (g u) (g t) < C.radius
        rw [hg.dist_eq]
        exact huL.trans hLC
      have hdist0 : dist (⟨f u, hfball⟩ : ball (g t) C.radius)
          (e ⟨0, h0mem⟩) =
          dist (⟨g u, hgball⟩ : ball (g t) C.radius) (e ⟨0, h0mem⟩) := by
        change dist (f u) (e ⟨0, h0mem⟩).1 = dist (g u) (e ⟨0, h0mem⟩).1
        have he : dist (f u) (g t) = dist (g u) (g t) :=
          (congrArg (fun w ↦ dist (f u) w) hft.symm).trans
            ((hf.dist_eq u t).trans (hg.dist_eq u t).symm)
        have he0' : (e ⟨0, h0mem⟩).1 = g t := he0
        rw [he0']
        exact he
      have hdistb : dist (⟨f u, hfball⟩ : ball (g t) C.radius)
          (e ⟨(b.1 : ℂ), hbmem⟩) =
          dist (⟨g u, hgball⟩ : ball (g t) C.radius) (e ⟨(b.1 : ℂ), hbmem⟩) := by
        change dist (f u) (e ⟨(b.1 : ℂ), hbmem⟩).1 =
          dist (g u) (e ⟨(b.1 : ℂ), hbmem⟩).1
        have he : dist (f u) (g (k b)) = dist (g u) (g (k b)) :=
          (congrArg (fun w ↦ dist (f u) w) hfb.symm).trans
            ((hf.dist_eq u (k b)).trans (hg.dist_eq u (k b)).symm)
        simpa only [heb] using he
      exact congrArg Subtype.val
        (metricHalfDisk_two_anchor_unique e (Ne.symm hb) h0mem hbmem hdist0 hdistb)
  funext t
  have hfull : Icc (0 : NNReal) t ⊆ S :=
    (hSc.inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hS0
      (fun u _ hprefix ↦ mem_nhdsWithin_of_mem_nhds (hstep u hprefix))
  exact hfull ⟨t.2, le_rfl⟩

end RepulsiveCoulomb
