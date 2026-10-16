import LeanResearch.RepulsiveCoulomb.MetricCleanRayCompactCollar
import LeanResearch.RepulsiveCoulomb.FullNormalStripSourceGeometry
import LeanResearch.RepulsiveCoulomb.PointConvexLocalFlatEmbedding

/-! Construct an actual positive-width finite normal rectangle along any
finite portion of a full clean boundary line. The source translation merely
lets the genuine aligned-ray halfdisk construction supply its local patches.
There is no positive corner or assumed collar map. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem exists_metricFullLine_initial_rectangle {Y : Type*} [MetricSpace Y]
    (line : ℝ → Y) (hline : Isometry line)
    (H : ∀ t : ℝ, MetricFlatHalfDiskChart Y (line t))
    {R delta : ℝ} (hR : 0 < R) (hdelta : 0 < delta) (c : ℝ) :
    ∃ s : ℝ, ∃ hs : 0 < s, s < delta ∧ ∃ F : flatShearedRectangle Complex.I R s → Y,
      (∀ r : Icc (0 : ℝ) R, F (normalRectangleBottom r.2 hs.le) = line (c + r.1)) ∧
      ∀ p, ∃ V : Set (flatShearedRectangle Complex.I R s), IsOpen V ∧ p ∈ V ∧
        ∀ x ∈ V, ∀ z ∈ V, dist (F x) (F z) = dist x z := by
  let rho : NNReal → Y := fun q ↦ line (c - 1 + q.1)
  have hrho : Isometry rho := by
    apply Isometry.of_dist_eq
    intro q t
    rw [hline.dist_eq]
    change |(c - 1 + q.1) - (c - 1 + t.1)| = |q.1 - t.1|
    congr 1; ring
  obtain ⟨eta, heta, G, hGb, hGl, hGreg⟩ := exists_metricRay_compact_initial_collar
    rho hrho (by norm_num : (0 : ℝ) < 1)
    (fun t : Icc (1 : ℝ) (R + 1) ↦ H (c - 1 + t.1))
  let s := min (eta / 2) (delta / 2)
  have hs : 0 < s := lt_min (half_pos heta) (half_pos hdelta)
  have hseta : s ≤ eta := (min_le_left _ _).trans (half_le_self heta.le)
  have hsdelta : s < delta := (min_le_right _ _).trans_lt (half_lt_self hdelta)
  have hsub (z : flatShearedRectangle Complex.I R s) :
      z.1 + 1 ∈ flatNormalRectangle 1 (R + 1) eta := by
    obtain ⟨r, hr, u, hu, he⟩ := z.2
    rw [he]
    change (flatShearedPoint Complex.I r u + 1).re ∈ Icc 1 (R + 1) ∧
      (flatShearedPoint Complex.I r u + 1).im ∈ Icc 0 eta
    simpa [flatShearedPoint] using
      And.intro (show r + 1 ∈ Icc 1 (R + 1) from ⟨by linarith [hr.1], by linarith [hr.2]⟩)
        (show u ∈ Icc (0 : ℝ) eta from ⟨hu.1, hu.2.trans hseta⟩)
  let incl : flatShearedRectangle Complex.I R s → flatNormalRectangle 1 (R + 1) eta :=
    fun z ↦ ⟨z.1 + 1, hsub z⟩
  have hinc : Isometry incl := by
    apply Isometry.of_dist_eq
    intro x z
    exact dist_add_right x.1 z.1 (1 : ℂ)
  let F := G ∘ incl
  refine ⟨s, hs, hsdelta, F, ?_, ?_⟩
  · intro r
    let q : NNReal := ⟨r.1 + 1, by linarith [r.2.1]⟩
    have hqcast : (q : ℂ) = (r.1 : ℂ) + 1 := by
      change ((r.1 + 1 : ℝ) : ℂ) = (r.1 : ℂ) + 1
      simpa only [Complex.ofReal_one] using (Complex.ofReal_add r.1 1)
    have hq : (q : ℂ) ∈ flatNormalRectangle 1 (R + 1) eta := by
      rw [hqcast]
      exact (incl (normalRectangleBottom r.2 hs.le)).2
    have hi : incl (normalRectangleBottom r.2 hs.le) = ⟨(q : ℂ), hq⟩ := by
      apply Subtype.ext
      change (r.1 : ℂ) + 1 = (q : ℂ)
      exact hqcast.symm
    change G (incl (normalRectangleBottom r.2 hs.le)) = line (c + r.1)
    rw [hi, hGb q hq]
    change line (c - 1 + (r.1 + 1)) = line (c + r.1)
    congr 1; ring
  · intro p
    obtain ⟨V, hV, hp, hd⟩ := hGl (incl p)
    refine ⟨incl ⁻¹' V, hV.preimage hinc.continuous, hp, ?_⟩
    intro x hx z hz
    exact (hd (incl x) hx (incl z) hz).trans (hinc.dist_eq x z)

theorem point_exists_fullLine_initial_rectangle
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (line : ℝ → P)
    (hline : @Isometry ℝ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace line)
    (H : ∀ t : ℝ, @MetricFlatHalfDiskChart P (pointRegionMetricSpace ha y P) (line t))
    {R delta : ℝ} (hR : 0 < R) (hdelta : 0 < delta) (c : ℝ) :
    ∃ s : ℝ, ∃ hs : 0 < s, s < delta ∧ ∃ F : flatShearedRectangle Complex.I R s → P,
      (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
      ∀ r : Icc (0 : ℝ) R, F (normalRectangleBottom r.2 hs.le) = line (c + r.1) := by
  letI : MetricSpace P := pointRegionMetricSpace ha y P
  letI : PseudoMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoMetricSpace
  letI : PseudoEMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoEMetricSpace
  obtain ⟨s, hs, hsdelta, F, hFb, hFl⟩ := exists_metricFullLine_initial_rectangle line hline H hR hdelta c
  have hlocal : PointLocallyDistancePreserving a y (fun z ↦ (F z).1) := hFl
  exact ⟨s, hs, hsdelta, F,
    pointConvexFlat_dist ha y (flatShearedRectangle_convex _ _ _) hlocal, hFb⟩

end RepulsiveCoulomb
