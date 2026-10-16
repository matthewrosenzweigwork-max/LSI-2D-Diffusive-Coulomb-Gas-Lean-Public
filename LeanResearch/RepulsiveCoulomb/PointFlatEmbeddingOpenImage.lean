import LeanResearch.RepulsiveCoulomb.PointFlatLinkConeDisk
import LeanResearch.RepulsiveCoulomb.ComplexSubsetIsometryExtension
import LeanResearch.RepulsiveCoulomb.PointInteriorZeroExponentFlatChart

/-! SOURCE-ONLY, UNCOMPILED. The image of the source interior is proved
ambient-open using the actual zero-exponent cone chart and an extension of a
literal Euclidean isometry. No invariance-of-domain theorem or ambient-open
image assertion is assumed. Regularity is retained construction data; this
file does not infer it from a bare closed-sector embedding. -/
noncomputable section
open Set Metric Filter
open scoped Topology ENNReal
namespace RepulsiveCoulomb

/-- A source interior point that maps to an actual regular point has an
entire ambient metric ball in the image of the source interior. -/
theorem pointFlatEmbedding_interior_ball
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (f : K → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (q : K) (hq : q.1 ∈ interior K) (hzero : coalescedPointExponent a y (f q) = 0) :
    ∃ r : ℝ, 0 < r ∧ ∀ z,
      (pointSmoothConformalEDist a y z (f q)).toReal < r →
      z ∈ f '' {x : K | x.1 ∈ interior K} := by
  obtain ⟨ε, hε, hεK⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hq)
  obtain ⟨C⟩ := exists_pointFlatLinkConeDisk ha y (f q)
  let r := min ε C.radius
  have hr : 0 < r := lt_min hε C.radius_pos
  have hsub (w : ball q.1 r) : w.1 ∈ interior K :=
    hεK ((show dist w.1 q.1 < r from w.2).trans_le (min_le_left _ _))
  let inc : ball q.1 r → K := fun w ↦ ⟨w.1, interior_subset (hsub w)⟩
  have hbound (w : ball q.1 r) :
      (pointSmoothConformalEDist a y (f (inc w)) (f q)).toReal ≤ C.radius := by
    rw [hd]
    exact w.2.le.trans (min_le_right _ _)
  let g : ball q.1 r → ℂ := fun w ↦ C.chart (f (inc w))
  have hg : Isometry g := by
    apply Isometry.of_dist_eq
    intro w v
    have hm := C.metric (f (inc w)) (hbound w) (f (inc v)) (hbound v)
    rw [pointClassicalConeDist_eq_euclidean_of_zero y hzero, hd] at hm
    exact hm.symm
  obtain ⟨e, he⟩ := exists_complex_isometry_extension_of_open_overlap g hg
    (by rw [isOpen_ball.interior_eq]; exact ⟨q.1, mem_ball_self hr⟩)
  have heq : e q.1 = 0 := by
    have h := he ⟨q.1, mem_ball_self hr⟩
    change e q.1 = C.chart (f ⟨q.1, _⟩) at h
    exact h.trans C.center
  refine ⟨r, hr, fun z hz ↦ ?_⟩
  have hzC : (pointSmoothConformalEDist a y z (f q)).toReal ≤ C.radius :=
    hz.le.trans (min_le_right _ _)
  let w : ℂ := e.symm (C.chart z)
  have hw : w ∈ ball q.1 r := by
    change dist (e.symm (C.chart z)) q.1 < r
    rw [← e.dist_eq, e.apply_symm_apply, heq, dist_zero_right, C.norm_chart hzC]
    exact hz
  let wB : ball q.1 r := ⟨w, hw⟩
  refine ⟨inc wB, hsub wB, ?_⟩
  apply C.chart.injOn (C.source (hbound wB)) (C.source hzC)
  calc
    C.chart (f (inc wB)) = e w := (he wB).symm
    _ = C.chart z := e.apply_symm_apply _

/-- Actual regularity of all source-interior images proves ambient openness.
The metric-to-Euclidean topology identification is the established point
metric theorem, including the atom topology. -/
theorem pointFlatEmbedding_isOpen_openImage
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {K : Set ℂ} (f : K → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    (hregular : ∀ x : K, x.1 ∈ interior K → coalescedPointExponent a y (f x) = 0) :
    IsOpen (f '' {x : K | x.1 ∈ interior K}) := by
  apply (isOpen_iff_pointConformal_balls ha y _).mpr
  rintro p ⟨q, hq, rfl⟩
  obtain ⟨r, hr, hball⟩ := pointFlatEmbedding_interior_ball ha y f hd q hq (hregular q hq)
  refine ⟨ENNReal.ofReal r, ENNReal.ofReal_pos.mpr hr, fun z hz ↦ ?_⟩
  apply hball
  rw [pointSmoothConformalEDist_comm a y z (f q)]
  exact (ENNReal.toReal_lt_toReal (pointSmoothConformalEDist_lt_top ha y _ _).ne
    ENNReal.ofReal_ne_top).mpr hz |>.trans_eq (ENNReal.toReal_ofReal hr.le)

end RepulsiveCoulomb
