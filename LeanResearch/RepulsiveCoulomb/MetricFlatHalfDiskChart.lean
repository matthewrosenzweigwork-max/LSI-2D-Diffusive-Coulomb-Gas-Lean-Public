import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart

/-! NEW implementation after workspace loss; independently reviewed revision.
This is not a recovered historical source and inherits no historical check.

A genuine retained link of physical width pi gives the whole upper halfdisk
onto the whole relative ball in the old point-region metric. Pair distances,
center preservation, and surjectivity come from the accepted flat inverse.
Positive ambient exponents are permitted at retained-flat boundary points.
The upper-side reflection is the literal Euclidean map z ↦ -conj z. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Open-radius upper halfdisk, with the real diameter retained. -/
def flatUpperDisk (R : ℝ) : Set ℂ := {z | ‖z‖ < R ∧ 0 ≤ z.im}

def flatUpperDiskZero {R : ℝ} (hR : 0 < R) : flatUpperDisk R :=
  ⟨0, by simp [flatUpperDisk, hR]⟩

/-- A whole halfdisk parametrization of the whole relative metric ball. -/
structure MetricFlatHalfDiskChart (Y : Type*) [MetricSpace Y] (p : Y) where
  radius : ℝ
  radius_pos : 0 < radius
  fromEuclidean : flatUpperDisk radius ≃ᵢ ball p radius
  center : (fromEuclidean (flatUpperDiskZero radius_pos)).1 = p

/-- Reflection in the imaginary axis, preserving the chosen upper side. -/
def flatUpperDiskFlip (R : ℝ) : flatUpperDisk R ≃ᵢ flatUpperDisk R := by
  let F : flatUpperDisk R → flatUpperDisk R := fun z ↦
    ⟨-star z.1, by
      constructor
      · simpa only [norm_neg, Complex.star_def, Complex.norm_conj] using z.2.1
      · simpa only [Complex.neg_im, Complex.star_def, Complex.conj_im, neg_neg] using z.2.2⟩
  have hleft : Function.LeftInverse F F := by
    intro z
    apply Subtype.ext
    change -star (-star z.1) = z.1
    simp
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro z w
    change dist (-star z.1) (-star w.1) = dist z.1 w.1
    simpa only [dist_neg_neg, Complex.star_def] using Complex.dist_conj_conj z.1 w.1
  exact { toFun := F, invFun := F, left_inv := hleft, right_inv := hleft, isometry_toFun := hF }

@[simp] theorem flatUpperDiskFlip_zero {R : ℝ} (hR : 0 < R) :
    flatUpperDiskFlip R (flatUpperDiskZero hR) = flatUpperDiskZero hR := by
  apply Subtype.ext
  change -star (0 : ℂ) = 0
  simp

/-- The accepted all-pairs identity, specialized at the genuine chart center. -/
theorem PointRetainedConeNeighborhood.flatInverse_center_distance
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    (hwidth : C.flatPhysicalWidth ≤ Real.pi)
    {z : ℂ} (hz : z ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius) :
    (pointSmoothConformalEDist a y (C.flatInverse z) p).toReal = ‖z‖ := by
  have h0 : (0 : ℂ) ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius := by
    simp [retainedFlatSectorDisk, closedEuclideanSector, C.flatPhysicalWidth_pos.le, C.radius_pos.le]
  have h := C.flatInverse_dist hwidth hz h0
  simpa only [C.flatInverse_zero, dist_zero_right] using h

/-- Construct the complete metric halfdisk from the literal retained link.
No zero-exponent, flatness certificate, or separate onto premise is assumed. -/
def PointRetainedConeNeighborhood.flatHalfDiskChart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hp : p ∈ P) (hwidth : C.flatPhysicalWidth = Real.pi) :
    @MetricFlatHalfDiskChart P (pointRegionMetricSpace ha y P) ⟨p, hp⟩ := by
  -- Every metric layer used here is a projection of the same old region metric.
  -- No ambient topological instance is replaced.
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : EMetricSpace P := M.toEMetricSpace
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let pP : P := ⟨p, hp⟩
  have hsrc (z : flatUpperDisk C.radius) :
      z.1 ∈ retainedFlatSectorDisk C.flatPhysicalWidth C.radius := by
    rw [hwidth, retainedFlatSectorDisk_pi]
    exact ⟨z.2.2, z.2.1.le⟩
  have hrad (z : flatUpperDisk C.radius) :
      (pointSmoothConformalEDist a y (C.flatInverse z.1) p).toReal < C.radius := by
    rw [C.flatInverse_center_distance hwidth.le (hsrc z)]
    exact z.2.1
  let F : flatUpperDisk C.radius → ball pP C.radius := fun z ↦
    ⟨⟨C.flatInverse z.1, (C.flatInverse_mem_and_radius (hsrc z)).1⟩, hrad z⟩
  have hF : Isometry F := by
    apply Isometry.of_dist_eq
    intro z w
    change (pointSmoothConformalEDist a y (C.flatInverse z.1)
      (C.flatInverse w.1)).toReal = dist z.1 w.1
    exact C.flatInverse_dist hwidth.le (hsrc z) (hsrc w)
  -- First obtain a preimage in the accepted closed retained sector, then use
  -- center distance to show that its norm satisfies the strict ball bound.
  have hsurj : Function.Surjective F := by
    intro w
    have hwR : (pointSmoothConformalEDist a y w.1.1 p).toReal < C.radius := w.2
    obtain ⟨z, hz, hzw⟩ := C.flatInverse_surjOn hwidth.le ⟨w.1.2, hwR.le⟩
    have hzupper : 0 ≤ z.im := by
      have hz' := hz
      rw [hwidth, retainedFlatSectorDisk_pi] at hz'
      exact hz'.1
    have hznorm : ‖z‖ < C.radius := by
      rw [← C.flatInverse_center_distance hwidth.le hz, hzw]
      exact hwR
    refine ⟨⟨z, hznorm, hzupper⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hzw
  let e : flatUpperDisk C.radius ≃ᵢ ball pP C.radius :=
    { Equiv.ofBijective F ⟨hF.injective, hsurj⟩ with isometry_toFun := hF }
  refine ⟨C.radius, C.radius_pos, e, ?_⟩
  apply Subtype.ext
  change C.flatInverse (0 : ℂ) = p
  exact C.flatInverse_zero

end RepulsiveCoulomb
