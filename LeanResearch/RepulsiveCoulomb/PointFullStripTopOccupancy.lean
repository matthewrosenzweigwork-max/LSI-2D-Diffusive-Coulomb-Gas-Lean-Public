module

public import LeanResearch.RepulsiveCoulomb.FullStripResidualSource
public import LeanResearch.RepulsiveCoulomb.PointFullStripRetainedIntervals
public import LeanResearch.RepulsiveCoulomb.PointFlatLinkOccupancy

@[expose] public section

/-! A closed literal halfdisk is cut out of the SUPPLIED actual strip at each
top point. The accepted flat-link occupancy theorem is applied to that actual
map. It constructs a retained chart for the local strip germ of physical width
pi; no numerical occupation premise or regularity at the top is assumed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

def fullStripTopHalfDisk {h L : ℝ} (hh : 0 ≤ h) (hLh : L ≤ h) (s : ℝ)
    (z : flatLinkSectorDisk Real.pi L) : flatFullNormalStrip h := by
  have hz : 0 ≤ z.1.im ∧ ‖z.1‖ ≤ L := by
    simpa only [flatLinkSectorDisk_pi, mem_setOf_eq] using z.2
  refine ⟨(fullStripTop hh s).1 + starRingEnd ℂ z.1, ?_, ?_⟩
  · simp only [Complex.add_im, fullStripTop_im, Complex.conj_im]
    have hi := (le_abs_self z.1.im).trans (Complex.abs_im_le_norm z.1)
    linarith [hz.2, hLh]
  · simp only [Complex.add_im, fullStripTop_im, Complex.conj_im]
    linarith [hz.1]

@[simp] theorem fullStripTopHalfDisk_apex {h L : ℝ} (hh : 0 ≤ h) (hLh : L ≤ h)
    (hL : 0 ≤ L) (s : ℝ) :
    fullStripTopHalfDisk hh hLh s (flatLinkSectorDiskApex Real.pi_pos.le hL) = fullStripTop hh s := by
  apply Subtype.ext
  simp [fullStripTopHalfDisk, flatLinkSectorDiskApex]

theorem fullStripTopHalfDisk_isometry {h L : ℝ} (hh : 0 ≤ h) (hLh : L ≤ h) (s : ℝ) :
    Isometry (fullStripTopHalfDisk hh hLh s) := by
  apply Isometry.of_dist_eq
  intro z w
  change dist ((fullStripTop hh s).1 + starRingEnd ℂ z.1)
    ((fullStripTop hh s).1 + starRingEnd ℂ w.1) = dist z.1 w.1
  rw [dist_add_left]
  exact Complex.dist_conj_conj z.1 w.1

/-- Every source point within radius L of a top point belongs to that actual
closed halfdisk, including both real edges and the completed top. -/
theorem fullStripTopHalfDisk_local_coverage {h L : ℝ} (hh : 0 ≤ h)
    (hLh : L ≤ h) (s : ℝ) (z : flatFullNormalStrip h)
    (hz : dist z (fullStripTop hh s) ≤ L) :
    z ∈ range (fullStripTopHalfDisk hh hLh s) := by
  let w : ℂ := starRingEnd ℂ (z.1 - (fullStripTop hh s).1)
  have hwim : 0 ≤ w.im := by
    change 0 ≤ -(z.1.im - h)
    linarith [z.2.2]
  have hwn : ‖w‖ ≤ L := by
    simpa only [w, Complex.norm_conj, Subtype.dist_eq, dist_eq_norm] using hz
  have hw : w ∈ flatLinkSectorDisk Real.pi L := by
    rw [flatLinkSectorDisk_pi]
    exact ⟨hwim, hwn⟩
  refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
  change (fullStripTop hh s).1 + starRingEnd ℂ (starRingEnd ℂ (z.1 - (fullStripTop hh s).1)) = z.1
  simp only [Complex.conj_conj]
  abel

/-- The actual halfdisk and the actual global strip have the same local
closed germ, proved from the all-pairs metric law. -/
theorem pointFullStrip_topHalfDisk_germ
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ) {P : Set ℂ}
    {h L : ℝ} (hh : 0 ≤ h) (hLh : L ≤ h) (F : flatFullNormalStrip h → P)
    (hF : ∀ z w, (pointSmoothConformalEDist a y (F z).1 (F w).1).toReal = dist z w)
    (s : ℝ) {z : ℂ}
    (hz : (pointSmoothConformalEDist a y z (F (fullStripTop hh s)).1).toReal ≤ L) :
    z ∈ range (fun x ↦ (F x).1) ↔
      z ∈ range (fun x : flatLinkSectorDisk Real.pi L ↦
        (F (fullStripTopHalfDisk hh hLh s x)).1) := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [hF] at hz
    obtain ⟨w, hw⟩ := fullStripTopHalfDisk_local_coverage hh hLh s x hz
    exact ⟨w, congrArg (fun u ↦ (F u).1) hw⟩
  · rintro ⟨x, rfl⟩
    exact mem_range_self _

theorem flatLinkOccupiedDisk_eq_closed_interval (r lo hi : ℝ) :
    flatLinkOccupiedDisk r lo hi = pointClosedRadialInterval r lo hi := by
  simp only [flatLinkOccupiedDisk, pointClosedRadialInterval,
    sectorPolar_eq_pointRadialSectorPoint]

/-- At EVERY top point, including a positive ambient atom, the actual removed
strip germ occupies a physical halfplane of width pi. Coincident atoms enter
only through their coalesced exponent. Zero mass is included in the same proof. -/
theorem pointFullStrip_construct_top_strip_retained_chart
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {h : ℝ} (hh : 0 < h) (F : flatFullNormalStrip h → P)
    (hF : ∀ z w, (pointSmoothConformalEDist a y (F z).1 (F w).1).toReal = dist z w)
    (s : ℝ) :
    ∃ C : PointRetainedConeNeighborhood a y (range (fun z ↦ (F z).1))
        (F (fullStripTop hh.le s)).1,
      C.lo = 0 ∧
      C.hi = Real.pi / (coalescedPointExponent a y (F (fullStripTop hh.le s)).1 / 2 + 1) ∧
      C.flatPhysicalWidth = Real.pi := by
  let L := h/2
  have hL : 0 < L := half_pos hh
  have hLh : L ≤ h := by dsimp [L]; linarith
  let f : flatLinkSectorDisk Real.pi L → ℂ :=
    fun z ↦ (F (fullStripTopHalfDisk hh.le hLh s z)).1
  have hf : ∀ z w, (pointSmoothConformalEDist a y (f z) (f w)).toReal = dist z w := by
    intro z w
    rw [hF]
    exact (fullStripTopHalfDisk_isometry hh.le hLh s).dist_eq z w
  have hapex : f (flatLinkSectorDiskApex Real.pi_pos.le hL.le) =
      (F (fullStripTop hh.le s)).1 := by simp only [f, fullStripTopHalfDisk_apex]
  have hout := exists_pointFlatHalfDisk_occupancy ha y hL f hf
  rw [hapex] at hout
  obtain ⟨K, ρ, hρ, hρL, hρK, hocc, hwidth⟩ := hout
  let p := (F (fullStripTop hh.le s)).1
  let k := coalescedPointExponent a y p / 2 + 1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hk1 : 1 ≤ k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hw : 0 < Real.pi / k := div_pos Real.pi_pos hk
  have hwpi : Real.pi / k ≤ Real.pi := (div_le_iff₀ hk).mpr (by nlinarith [Real.pi_pos])
  let E := K.restrict hρ hρK
  let C : PointRetainedConeNeighborhood a y (range (fun z ↦ (F z).1)) p :=
    { chart := E.chart
      radius := E.radius
      radius_pos := E.radius_pos
      center := E.center
      source := E.source
      onto := E.onto
      metric := E.metric
      lo := 0
      hi := Real.pi/k
      width_pos := hw
      width_le_full := by linarith [Real.pi_pos]
      retained := by
        intro z hz
        have hg := pointFullStrip_topHalfDisk_germ y hh.le hLh F hF s (hz.trans hρL)
        have ho := hocc z hz
        rw [flatLinkOccupiedDisk_eq_closed_interval] at ho
        exact hg.trans ho }
  refine ⟨C,rfl,rfl,?_⟩
  unfold PointRetainedConeNeighborhood.flatPhysicalWidth
  change (coalescedPointExponent a y p/2+1)*(Real.pi/k-0) = Real.pi
  rw [sub_zero]
  exact hwidth

end RepulsiveCoulomb
