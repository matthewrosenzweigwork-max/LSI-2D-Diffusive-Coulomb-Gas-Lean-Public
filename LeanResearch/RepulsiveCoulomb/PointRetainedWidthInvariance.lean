import LeanResearch.RepulsiveCoulomb.ClassicalConeRetainedArcWidth
import LeanResearch.RepulsiveCoulomb.PointRetainedConeNeighborhood

/-! Isolated, uncompiled author draft. Width comparison for genuine charts of
actual local closed regions. The same old metric and center are used throughout.
No angle identity, length certificate, signed measure, convexity, or no-return
conclusion is an input. Full circles are included by proper-prefix exhaustion
in the contradiction argument; they are never treated as injective intervals. -/
noncomputable section
open Set Filter
open scoped Topology
namespace RepulsiveCoulomb
namespace PointRetainedConeNeighborhood
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P Q : Set ℂ} {p : ℂ}

/-- The chart radius is the actual old metric radius, derived from its
all-pairs identity with the center. -/
theorem retainedWidth_chart_norm (C : PointRetainedConeNeighborhood a y P p)
    {z : ℂ} (hz : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius) :
    ‖C.chart z‖ = (pointSmoothConformalEDist a y z p).toReal := by
  have hp : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  rw [C.metric z hz p hp, C.center, pointClassicalConeDist_apex]

/-- The inverse is defined on the entire closed metric disk and preserves
its exact radius. This is proved from the actual BijOn field, not assumed. -/
theorem retainedWidth_inverse (C : PointRetainedConeNeighborhood a y P p)
    {w : ℂ} (hw : ‖w‖ ≤ C.radius) :
    w ∈ C.chart.target ∧ C.chart (C.chart.symm w) = w ∧
      (pointSmoothConformalEDist a y (C.chart.symm w) p).toReal = ‖w‖ := by
  obtain ⟨z, hz, hzw⟩ := C.onto.surjOn hw
  have htarget : w ∈ C.chart.target := hzw ▸ C.chart.mapsTo (C.source hz)
  have hinv : C.chart.symm w = z := by rw [← hzw, C.chart.left_inv (C.source hz)]
  refine ⟨htarget, C.chart.right_inv htarget, ?_⟩
  rw [hinv, ← hzw]
  exact (C.retainedWidth_chart_norm hz).symm

/-- Compare any proper initial subarc of C with D. Actual local inclusion
sends every point of that positive-metric-radius arc into D's retained side;
all distances are compared in the SAME classical cone model. -/
theorem retainedWidth_subarc_le
    (C : PointRetainedConeNeighborhood a y P p)
    (D : PointRetainedConeNeighborhood a y Q p)
    {ε L : ℝ} (hε : 0 < ε) (hL : 0 < L)
    (hLC : L ≤ C.hi - C.lo) (hLfull : L < 2 * Real.pi)
    (hDproper : D.hi - D.lo < 2 * Real.pi)
    (hsub : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε → z ∈ P → z ∈ Q) :
    L ≤ D.hi - D.lo := by
  let r := min C.radius (min D.radius ε) / 2
  have hr : 0 < r := div_pos (lt_min C.radius_pos (lt_min D.radius_pos hε)) (by norm_num)
  have hrC : r ≤ C.radius := by
    have hmin := min_le_left C.radius (min D.radius ε)
    dsimp [r] at *
    linarith
  have hrD : r ≤ D.radius := by
    have hmin := (min_le_right C.radius (min D.radius ε)).trans (min_le_left D.radius ε)
    dsimp [r] at *
    linarith
  have hrε : r ≤ ε := by
    have hmin := (min_le_right C.radius (min D.radius ε)).trans (min_le_right D.radius ε)
    dsimp [r] at *
    linarith
  let w : unitInterval → ℂ := fun t => sectorPolar r (C.lo + L * t.1)
  let z : unitInterval → ℂ := fun t => C.chart.symm (w t)
  let v : unitInterval → ℂ := fun t => D.chart (z t)
  have hwnorm (t : unitInterval) : ‖w t‖ = r := sectorPolar_norm hr.le _
  have hinverse (t : unitInterval) : w t ∈ C.chart.target ∧ C.chart (z t) = w t ∧
      (pointSmoothConformalEDist a y (z t) p).toReal = r := by
    have h := C.retainedWidth_inverse ((hwnorm t).trans_le hrC)
    exact ⟨h.1, h.2.1, h.2.2.trans (hwnorm t)⟩
  have hzC (t : unitInterval) : (pointSmoothConformalEDist a y (z t) p).toReal ≤ C.radius :=
    (hinverse t).2.2.trans_le hrC
  have hzD (t : unitInterval) : (pointSmoothConformalEDist a y (z t) p).toReal ≤ D.radius :=
    (hinverse t).2.2.trans_le hrD
  have hzP (t : unitInterval) : z t ∈ P := by
    apply (C.retained (z t) (hzC t)).mpr
    rw [(hinverse t).2.1]
    refine ⟨r, ⟨hr.le, hrC⟩, C.lo + L * t.1, ?_, ?_⟩
    · constructor
      · linarith [mul_nonneg hL.le t.2.1]
      · have := mul_le_of_le_one_right hL.le t.2.2
        linarith
    · exact sectorPolar_eq_pointRadialSectorPoint _ _
  have hzQ (t : unitInterval) : z t ∈ Q :=
    hsub (z t) ((hinverse t).2.2.trans_le hrε) (hzP t)
  have hvnorm (t : unitInterval) : ‖v t‖ = r :=
    (D.retainedWidth_chart_norm (hzD t)).trans (hinverse t).2.2
  have hmem (t : unitInterval) : ∃ θ ∈ Icc D.lo D.hi, v t = sectorPolar r θ := by
    obtain ⟨s, hs, θ, hθ, he⟩ := (D.retained (z t) (hzD t)).mp (hzQ t)
    have hsrad : s = r := by
      have hn := congrArg norm he
      rw [pointRadialSectorPoint_norm hs.1] at hn
      exact hn.symm.trans (hvnorm t)
    refine ⟨θ, hθ, ?_⟩
    rw [sectorPolar_eq_pointRadialSectorPoint, ← hsrad]
    exact he
  have hwc : Continuous w := by
    dsimp [w, sectorPolar, conePhase]
    fun_prop
  have hzc : Continuous z :=
    C.chart.symm.continuousOn.comp_continuous hwc (fun t => (hinverse t).1)
  have hvc : Continuous v :=
    D.chart.continuousOn.comp_continuous hzc (fun t => D.source (hzD t))
  have hmetric (s t : unitInterval) : pointClassicalConeDist a y p (v s) (v t) =
      pointClassicalConeDist a y p (w s) (w t) := by
    rw [← D.metric (z s) (hzD s) (z t) (hzD t),
      C.metric (z s) (hzC s) (z t) (hzC t), (hinverse s).2.1, (hinverse t).2.1]
  exact classicalCone_retained_arc_width_le
    (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
    hr hL hLfull hDproper hvc hmem hmetric

/-- Actual local side inclusion forces full coordinate-width monotonicity.
A full source circle cannot fit inside a proper target interval: choose a
proper source prefix longer than that target. If the target is full, the
result already follows from C.width_le_full. No full-circle lift is used. -/
theorem coordinate_width_le_of_local_subset
    (C : PointRetainedConeNeighborhood a y P p)
    (D : PointRetainedConeNeighborhood a y Q p)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε → z ∈ P → z ∈ Q) :
    C.hi - C.lo ≤ D.hi - D.lo := by
  by_contra hnot
  have hlt : D.hi - D.lo < C.hi - C.lo := lt_of_not_ge hnot
  let L := ((D.hi - D.lo) + (C.hi - C.lo)) / 2
  have hL : 0 < L := by dsimp [L]; linarith [C.width_pos, D.width_pos]
  have hLC : L ≤ C.hi - C.lo := by dsimp [L]; linarith
  have hLfull : L < 2 * Real.pi := by dsimp [L]; linarith [C.width_le_full]
  have hDproper : D.hi - D.lo < 2 * Real.pi := hlt.trans_le C.width_le_full
  have hbound := C.retainedWidth_subarc_le D hε hL hLC hLfull hDproper hsub
  dsimp [L] at hbound
  linarith

/-- The corresponding physical-width inequality uses the common, actual
coalesced exponent. In particular it remains valid at exponent zero. -/
theorem physical_width_le_of_local_subset
    (C : PointRetainedConeNeighborhood a y P p)
    (D : PointRetainedConeNeighborhood a y Q p)
    {ε : ℝ} (hε : 0 < ε)
    (hsub : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε → z ∈ P → z ∈ Q) :
    (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo) ≤
      (1 + coalescedPointExponent a y p / 2) * (D.hi - D.lo) := by
  exact mul_le_mul_of_nonneg_left (C.coordinate_width_le_of_local_subset D hε hsub)
    (by linarith [coalescedPointExponent_nonneg a y p])

/-- Width is an invariant of the actual local closed-region germ, with no
normalization/orientation identity imposed on the two charts. -/
theorem coordinate_width_eq_of_local_eq
    (C : PointRetainedConeNeighborhood a y P p)
    (D : PointRetainedConeNeighborhood a y Q p)
    {ε : ℝ} (hε : 0 < ε)
    (heq : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε → (z ∈ P ↔ z ∈ Q)) :
    C.hi - C.lo = D.hi - D.lo := by
  exact le_antisymm
    (C.coordinate_width_le_of_local_subset D hε (fun z hz => (heq z hz).mp))
    (D.coordinate_width_le_of_local_subset C hε (fun z hz => (heq z hz).mpr))

/-- Full PHYSICAL widths of two genuine charts of the same local side agree,
including reflex widths, regular points, and the full-circle case. -/
theorem physical_width_eq_of_local_eq
    (C : PointRetainedConeNeighborhood a y P p)
    (D : PointRetainedConeNeighborhood a y Q p)
    {ε : ℝ} (hε : 0 < ε)
    (heq : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε → (z ∈ P ↔ z ∈ Q)) :
    (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo) =
      (1 + coalescedPointExponent a y p / 2) * (D.hi - D.lo) := by
  rw [C.coordinate_width_eq_of_local_eq D hε heq]

/-- Immediate specialization to two retained charts of literally the same P. -/
theorem physical_width_eq (C D : PointRetainedConeNeighborhood a y P p) :
    (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo) =
      (1 + coalescedPointExponent a y p / 2) * (D.hi - D.lo) := by
  exact C.physical_width_eq_of_local_eq D (ε := 1) (by norm_num)
    (fun _ _ => Iff.rfl)

/-- A full-circle chart and a proper chart cannot describe the same local
closed region. This states the boundary case explicitly. -/
theorem full_width_iff_of_local_eq
    (C : PointRetainedConeNeighborhood a y P p)
    (D : PointRetainedConeNeighborhood a y Q p)
    {ε : ℝ} (hε : 0 < ε)
    (heq : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ε → (z ∈ P ↔ z ∈ Q)) :
    C.hi - C.lo = 2 * Real.pi ↔ D.hi - D.lo = 2 * Real.pi := by
  rw [C.coordinate_width_eq_of_local_eq D hε heq]

end PointRetainedConeNeighborhood
end RepulsiveCoulomb
