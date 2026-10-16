module

public import LeanResearch.RepulsiveCoulomb.MetricFlatDiskPatchExtension
public import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart
public import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicAmbientConvexity

@[expose] public section

/-! Successor source-only draft. Full metric Euclidean disk charts are
constructed from the actual retained cone disk at an interior zero-curvature
point. The chart object used by patch extension is therefore genuine geometry,
not an assumed continuation or developing primitive. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

/-- Zero exponent means a literal Euclidean metric in the full cone chart. -/
theorem pointClassicalConeDist_eq_euclidean_of_zero {m : ℕ} {a : Fin m → ℝ}
    (y : Fin m → ℂ) {p : ℂ} (hzero : coalescedPointExponent a y p = 0) (x z : ℂ) :
    pointClassicalConeDist a y p x z = dist x z := by
  change @dist ℂ (classicalConeMetricSpace (coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))).toDist x z = dist x z
  have hcone (α : ℝ) (hα : 0 ≤ α) (hαzero : α = 0) :
      @dist ℂ (classicalConeMetricSpace α hα).toDist x z = dist x z := by
    subst α
    rw [classicalCone_zero_dist, norm_sub_rev]
    exact (dist_eq_norm x z).symm
  exact hcone (coalescedPointExponent a y p / 2)
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
    (by rw [hzero, zero_div])

/-- The exact metric disk in P is parametrized bijectively and isometrically
by the actual cone chart. The only curvature hypothesis is exponent zero. -/
def PointRetainedConeNeighborhood.fullFlatDiskChart {m : ℕ} {a : Fin m → ℝ}
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hp : p ∈ P)
    (hfull : C.Full) (hzero : coalescedPointExponent a y p = 0) :
    @MetricFlatDiskChart P (pointRegionMetricSpace ha y P) ⟨p, hp⟩ := by
  letI : MetricSpace P := pointRegionMetricSpace ha y P
  letI : PseudoMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoMetricSpace
  letI : PseudoEMetricSpace P := (pointRegionMetricSpace ha y P).toPseudoEMetricSpace
  let pP : P := ⟨p, hp⟩
  have hpR : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hnorm (x : ℂ) (hx : (pointSmoothConformalEDist a y x p).toReal ≤ C.radius) :
      ‖C.chart x‖ = (pointSmoothConformalEDist a y x p).toReal := by
    rw [C.metric x hx p hpR, C.center, pointClassicalConeDist_apex]
  have hF (x : ball pP C.radius) : C.chart x.1.1 ∈ ball (0 : ℂ) C.radius := by
    rw [mem_ball, dist_zero_right, hnorm _ x.2.le]
    exact x.2
  let F : ball pP C.radius → ball (0 : ℂ) C.radius := fun x ↦ ⟨C.chart x.1.1, hF x⟩
  have hG (w : ball (0 : ℂ) C.radius) :
      (pointSmoothConformalEDist a y (C.chart.symm w.1) p).toReal < C.radius := by
    have hw : ‖w.1‖ < C.radius := by simpa only [mem_ball, dist_zero_right] using w.2
    obtain ⟨hR, he⟩ := C.inverse_metricBall hw.le
    rw [← hnorm _ hR, he]
    exact hw
  let G : ball (0 : ℂ) C.radius → ball pP C.radius := fun w ↦
    ⟨⟨C.chart.symm w.1, hfull _ (hG w).le⟩, hG w⟩
  have hleft : Function.LeftInverse G F := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    have hxS : x.1.1 ∈ {z : ℂ | (pointSmoothConformalEDist a y z p).toReal ≤ C.radius} := by
      change (pointSmoothConformalEDist a y x.1.1 p).toReal ≤ C.radius
      exact (show (pointSmoothConformalEDist a y x.1.1 p).toReal < C.radius from x.2).le
    exact C.chart.left_inv (C.source hxS)
  have hright : Function.RightInverse G F := by
    intro w
    apply Subtype.ext
    have hw : ‖w.1‖ < C.radius := by
      simpa only [mem_ball, dist_zero_right] using w.2
    exact (C.inverse_metricBall hw.le).2
  have hiso : Isometry F := by
    apply Isometry.of_dist_eq
    intro x z
    change dist (C.chart x.1.1) (C.chart z.1.1) =
      (pointSmoothConformalEDist a y x.1.1 z.1.1).toReal
    rw [C.metric _ x.2.le _ z.2.le, pointClassicalConeDist_eq_euclidean_of_zero y hzero]
  let e : ball pP C.radius ≃ᵢ ball (0 : ℂ) C.radius :=
    { toFun := F
      invFun := G
      left_inv := hleft
      right_inv := hright
      isometry_toFun := hiso }
  exact ⟨C.radius, C.radius_pos, e, C.center⟩

end RepulsiveCoulomb
