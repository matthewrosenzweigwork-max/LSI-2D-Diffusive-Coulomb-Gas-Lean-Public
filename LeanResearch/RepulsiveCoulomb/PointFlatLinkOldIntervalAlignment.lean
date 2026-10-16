module

public import LeanResearch.RepulsiveCoulomb.ClassicalConeRetainedArcWidth
public import LeanResearch.RepulsiveCoulomb.PointFlatLinkRadialTrace
public import LeanResearch.RepulsiveCoulomb.PointRetainedWidthInvariance
public import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Flat occupancy is aligned INSIDE the actual
old full retained interval. Two unrelated normalized charts are not compared
by a guessed angle equality. The old interval's properness is essential. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem translatedInterval_polar_injective {r lo hi θ φ : ℝ}
    (hr : 0 < r) (hproper : hi-lo < 2*Real.pi)
    (hθ : θ ∈ Icc lo hi) (hφ : φ ∈ Icc lo hi)
    (he : sectorPolar r θ = sectorPolar r φ) : θ = φ := by
  have hphase : Circle.exp θ = Circle.exp φ := by
    apply Subtype.ext
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
    simpa only [sectorPolar_eq_pointRadialSectorPoint,pointRadialSectorPoint] using he
  apply (Circle.exp_injOn_Ico (a := lo) (b := lo+2*Real.pi) (by linarith)) _ _ hphase
  · exact ⟨hθ.1,lt_of_le_of_lt hθ.2 (by linarith)⟩
  · exact ⟨hφ.1,lt_of_le_of_lt hφ.2 (by linarith)⟩

/-- The lift is constructed in the OLD full interval. Its increments agree
with the flat arc's independently constructed directed lift, by uniqueness of
continuous circle lifts. This preserves reflex old intervals. -/
theorem flatArc_in_old_interval_directed_lift
    {α r β lo hi : ℝ} (hα : 0 ≤ α) (hr : 0 < r)
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hproper : hi-lo < 2*Real.pi)
    {v : unitInterval → ℂ} (hc : Continuous v) (hnorm : ∀ t, ‖v t‖ = r)
    (hmem : ∀ t, ∃ θ ∈ Icc lo hi, v t = sectorPolar r θ)
    (hd : ∀ s t, @dist ℂ (classicalConeMetricSpace α hα).toDist (v s) (v t) =
      ‖sectorPolar r (β*s.1)-sectorPolar r (β*t.1)‖) :
    ∃ ψ : unitInterval → ℝ, Continuous ψ ∧ (∀ t, ψ t ∈ Icc lo hi) ∧
      (∀ t, v t = sectorPolar r (ψ t)) ∧
      ((∀ t, ψ t = ψ 0+(β/(α+1))*t.1) ∨
        (∀ t, ψ t = ψ 0-(β/(α+1))*t.1)) := by
  obtain ⟨ψ,hψ,hψmem,hψpolar⟩ := retainedWidth_exists_target_lift hr hproper hc hmem
  obtain ⟨φ,hφ,hφinj,hφpolar,horient⟩ :=
    classicalCone_flat_arc_directed_lift hα hr hβ hβπ hc hnorm hd
  have hexp (t : unitInterval) : Circle.exp (ψ t) = Circle.exp (φ t) := by
    apply Subtype.ext
    apply mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne')
    have he := (hψpolar t).symm.trans (hφpolar t)
    simpa only [sectorPolar_eq_pointRadialSectorPoint,pointRadialSectorPoint] using he
  have hinc (t : unitInterval) : ψ t-ψ 0 = φ t-φ 0 :=
    euclidean_angle_lift_increment_eq hψ hφ hexp 0 t
  refine ⟨ψ,hψ,hψmem,hψpolar,?_⟩
  rcases horient with hp | hm
  · left
    intro t
    have := hinc t
    rw [hp t] at this
    linarith
  · right
    intro t
    have := hinc t
    rw [hm t] at this
    linarith

/-- Sharing the LOWER old boundary germ forces the positive orientation and
locates the ENTIRE occupied arc in [lo, lo+beta/(alpha+1)]. -/
theorem flatArc_anchored_old_lower_interval
    {α r β lo hi : ℝ} (hα : 0 ≤ α) (hr : 0 < r)
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hproper : hi-lo < 2*Real.pi)
    {v : unitInterval → ℂ} (hc : Continuous v) (hnorm : ∀ t, ‖v t‖ = r)
    (hmem : ∀ t, ∃ θ ∈ Icc lo hi, v t = sectorPolar r θ)
    (hd : ∀ s t, @dist ℂ (classicalConeMetricSpace α hα).toDist (v s) (v t) =
      ‖sectorPolar r (β*s.1)-sectorPolar r (β*t.1)‖)
    (hstart : v 0 = sectorPolar r lo) :
    lo+β/(α+1) ≤ hi ∧
      ∀ t, v t = sectorPolar r (lo+(β/(α+1))*t.1) := by
  obtain ⟨ψ,hψ,hψmem,hψpolar,horient⟩ :=
    flatArc_in_old_interval_directed_lift hα hr hβ hβπ hproper hc hnorm hmem hd
  have hlohi : lo ≤ hi := (hψmem 0).1.trans (hψmem 0).2
  have hψ0 : ψ 0 = lo := translatedInterval_polar_injective hr hproper
    (hψmem 0) ⟨le_rfl,hlohi⟩ ((hψpolar 0).symm.trans hstart)
  have hw : 0 < β/(α+1) := div_pos hβ (by linarith)
  rcases horient with hp | hm
  · have h1 := hp 1
    have hm1 := (hψmem 1).2
    simp only [hψ0,show ((1 : unitInterval) : ℝ) = 1 from rfl,mul_one] at h1
    refine ⟨by linarith,?_⟩
    intro t
    rw [hψpolar t,hp t,hψ0]
  · have h1 := hm 1
    have hm1 := (hψmem 1).1
    simp only [hψ0,show ((1 : unitInterval) : ℝ) = 1 from rfl,mul_one] at h1
    linarith

/-- Sharing the UPPER old boundary germ forces the opposite orientation.
No preselected source orientation is smuggled into the theorem. -/
theorem flatArc_anchored_old_upper_interval
    {α r β lo hi : ℝ} (hα : 0 ≤ α) (hr : 0 < r)
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hproper : hi-lo < 2*Real.pi)
    {v : unitInterval → ℂ} (hc : Continuous v) (hnorm : ∀ t, ‖v t‖ = r)
    (hmem : ∀ t, ∃ θ ∈ Icc lo hi, v t = sectorPolar r θ)
    (hd : ∀ s t, @dist ℂ (classicalConeMetricSpace α hα).toDist (v s) (v t) =
      ‖sectorPolar r (β*s.1)-sectorPolar r (β*t.1)‖)
    (hstart : v 0 = sectorPolar r hi) :
    lo ≤ hi-β/(α+1) ∧
      ∀ t, v t = sectorPolar r (hi-(β/(α+1))*t.1) := by
  obtain ⟨ψ,hψ,hψmem,hψpolar,horient⟩ :=
    flatArc_in_old_interval_directed_lift hα hr hβ hβπ hproper hc hnorm hmem hd
  have hlohi : lo ≤ hi := (hψmem 0).1.trans (hψmem 0).2
  have hψ0 : ψ 0 = hi := translatedInterval_polar_injective hr hproper
    (hψmem 0) ⟨hlohi,le_rfl⟩ ((hψpolar 0).symm.trans hstart)
  have hw : 0 < β/(α+1) := div_pos hβ (by linarith)
  rcases horient with hp | hm
  · have h1 := hp 1
    have hm1 := (hψmem 1).2
    simp only [hψ0,show ((1 : unitInterval) : ℝ) = 1 from rfl,mul_one] at h1
    linarith
  · have h1 := hm 1
    have hm1 := (hψmem 1).1
    simp only [hψ0,show ((1 : unitInterval) : ℝ) = 1 from rfl,mul_one] at h1
    refine ⟨by linarith,?_⟩
    intro t
    rw [hψpolar t,hm t,hψ0]

/-- An admissible old boundary interval is a proper interval in its ambient
coordinate circle, even if its physical width is greater than pi. -/
theorem PointRetainedConeNeighborhood.coordinate_width_lt_full_of_admissible
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hadm : C.Admissible) :
    C.hi-C.lo < 2*Real.pi := by
  have hk : 0 < coalescedPointExponent a y p/2+1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  unfold PointRetainedConeNeighborhood.Admissible at hadm
  by_contra hnot
  have hw : 2*Real.pi ≤ C.hi-C.lo := le_of_not_gt hnot
  have hprod := mul_nonpos_of_nonneg_of_nonpos hk.le (sub_nonpos.mpr hw)
  exact (not_le_of_gt Real.pi_pos) (hadm.trans hprod)

/-- The actual supplied sector disk is aligned in the actual OLD retained
chart. The first positive-radius edge point is identified with the lower old
endpoint; the orientation and every other angle are then derived. -/
theorem pointFlatLinkDisk_old_lower_polar
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {P : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hadm : C.Admissible) {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (hfirst : C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)) =
      sectorPolar ρ C.lo) :
    let k := coalescedPointExponent a y (f (flatLinkSectorDiskApex hβ.le hL.le))/2+1
    C.lo+β/k ≤ C.hi ∧ ∀ s t : unitInterval,
      C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ*s.1)
        ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t)) =
        sectorPolar (ρ*s.1) (C.lo+(β/k)*t.1) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let q := flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩
  let v (t : unitInterval) := C.chart (f (q t))
  let K : PointFlatLinkConeDisk a y p :=
    ⟨C.chart,C.radius,C.radius_pos,C.center,C.source,C.onto,C.metric⟩
  have hb (t : unitInterval) : (pointSmoothConformalEDist a y (f (q t)) p).toReal ≤ C.radius := by
    rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    change ‖sectorPolar ρ (β*t.1)‖ ≤ C.radius
    rw [sectorPolar_norm hρ.le]
    exact hρC
  have hvc : Continuous v := C.chart.continuousOn.comp_continuous
    ((continuous_pointFlatLinkDiskMap ha y f hd).comp
      (continuous_flatLinkSectorDiskPoint hβ.le hβπ ⟨hρ.le,hρL⟩))
    (fun t ↦ C.source (hb t))
  have hvnorm (t : unitInterval) : ‖v t‖ = ρ := by
    rw [C.retainedWidth_chart_norm (hb t),pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    exact sectorPolar_norm hρ.le _
  have hmem (t : unitInterval) : ∃ θ ∈ Icc C.lo C.hi, v t = sectorPolar ρ θ := by
    obtain ⟨r,hr,θ,hθ,he⟩ := (C.retained (f (q t)) (hb t)).mp (hfP (q t))
    have hn := congrArg norm he
    rw [pointRadialSectorPoint_norm hr.1] at hn
    have hrρ : r = ρ := hn.symm.trans (hvnorm t)
    refine ⟨θ,hθ,?_⟩
    rw [sectorPolar_eq_pointRadialSectorPoint,← hrρ]
    exact he
  have hα : 0 ≤ coalescedPointExponent a y p/2 :=
    div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hvdist (s t : unitInterval) :
      @dist ℂ (classicalConeMetricSpace (coalescedPointExponent a y p/2) hα).toDist (v s) (v t) =
        ‖sectorPolar ρ (β*s.1)-sectorPolar ρ (β*t.1)‖ := by
    change pointClassicalConeDist a y p (C.chart (f (q s))) (C.chart (f (q t))) = _
    rw [← C.metric (f (q s)) (hb s) (f (q t)) (hb t),hd]
    change dist (sectorPolar ρ (β*s.1)) (sectorPolar ρ (β*t.1)) = _
    exact dist_eq_norm _ _
  obtain ⟨hwidth,htrace⟩ := flatArc_anchored_old_lower_interval hα hρ hβ hβπ
    (C.coordinate_width_lt_full_of_admissible hadm) hvc hvnorm hmem hvdist hfirst
  refine ⟨hwidth,?_⟩
  intro s t
  rw [pointFlatLinkDiskMap_radial y hβ hβπ hL f hd K hρ hρL hρC s t]
  change s.1 • v t = _
  rw [htrace t]
  simp only [sectorPolar,Complex.real_smul,Complex.ofReal_mul]
  ring

/-- Exact occupied-set identity IN the old full interval. It follows from
all-pairs isometry, its derived radiality and derived orientation, with genuine
whole-disk chart injectivity in the inverse direction. -/
theorem pointFlatLinkDisk_old_lower_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {P : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hadm : C.Admissible) {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (hfirst : C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)) =
      sectorPolar ρ C.lo) :
    let p := f (flatLinkSectorDiskApex hβ.le hL.le)
    let k := coalescedPointExponent a y p/2+1
    C.lo+β/k ≤ C.hi ∧ ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
      (z ∈ range f ↔ C.chart z ∈ pointClosedRadialInterval ρ C.lo (C.lo+β/k)) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p/2+1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hw : 0 < β/k := div_pos hβ hk
  obtain ⟨hwidth,hpolar⟩ := pointFlatLinkDisk_old_lower_polar ha y hβ hβπ hL
    f hd hfP C hadm hρ hρL hρC hfirst
  refine ⟨hwidth,?_⟩
  intro z hz
  constructor
  · rintro ⟨x,rfl⟩
    have hx : ‖x.1‖ ≤ ρ := by rwa [pointFlatLinkDiskMap_dist_apex y hβ hL f hd] at hz
    obtain ⟨s,t,hst⟩ := flatLinkSectorDisk_representation hβ hβπ hρ hρL x hx
    rw [hst,hpolar]
    refine ⟨ρ*s.1,⟨mul_nonneg hρ.le s.2.1,mul_le_of_le_one_right hρ.le s.2.2⟩,
      C.lo+(β/k)*t.1,⟨?_,?_⟩,sectorPolar_eq_pointRadialSectorPoint _ _⟩
    · linarith [mul_nonneg hw.le t.2.1]
    · linarith [mul_le_of_le_one_right hw.le t.2.2]
  · rintro ⟨r,hr,θ,hθ,he⟩
    let s : unitInterval := ⟨r/ρ,div_nonneg hr.1 hρ.le,(div_le_one hρ).mpr hr.2⟩
    let t : unitInterval := ⟨(θ-C.lo)/(β/k),div_nonneg (sub_nonneg.mpr hθ.1) hw.le,
      (div_le_one hw).mpr (by linarith [hθ.2])⟩
    have hrs : ρ*s.1 = r := mul_div_cancel₀ _ hρ.ne'
    have hθt : C.lo+(β/k)*t.1 = θ := by
      change C.lo+(β/k)*((θ-C.lo)/(β/k)) = θ
      rw [mul_div_cancel₀ _ hw.ne']
      ring
    let x := flatLinkSectorDiskPoint hβ.le hβπ (ρ*s.1)
      ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t
    have hxC : (pointSmoothConformalEDist a y (f x) p).toReal ≤ C.radius := by
      rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
      change ‖sectorPolar (ρ*s.1) (β*t.1)‖ ≤ C.radius
      rw [sectorPolar_norm (mul_nonneg hρ.le s.2.1),hrs]
      exact hr.2.trans hρC
    refine ⟨x,C.chart.injOn (C.source hxC) (C.source (hz.trans hρC)) ?_⟩
    change C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ*s.1) _ t)) = C.chart z
    rw [hpolar,hrs,hθt,sectorPolar_eq_pointRadialSectorPoint]
    exact he.symm

/-- Symmetric actual old-chart polar construction for the UPPER incoming
boundary germ. This is a separate orientation case, not a rotation shortcut. -/
theorem pointFlatLinkDisk_old_upper_polar
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {P : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hadm : C.Admissible) {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (hfirst : C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)) =
      sectorPolar ρ C.hi) :
    let k := coalescedPointExponent a y (f (flatLinkSectorDiskApex hβ.le hL.le))/2+1
    C.lo ≤ C.hi-β/k ∧ ∀ s t : unitInterval,
      C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ*s.1)
        ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t)) =
        sectorPolar (ρ*s.1) (C.hi-(β/k)*t.1) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let q := flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩
  let v (t : unitInterval) := C.chart (f (q t))
  let K : PointFlatLinkConeDisk a y p :=
    ⟨C.chart,C.radius,C.radius_pos,C.center,C.source,C.onto,C.metric⟩
  have hb (t : unitInterval) : (pointSmoothConformalEDist a y (f (q t)) p).toReal ≤ C.radius := by
    rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    change ‖sectorPolar ρ (β*t.1)‖ ≤ C.radius
    rw [sectorPolar_norm hρ.le]
    exact hρC
  have hvc : Continuous v := C.chart.continuousOn.comp_continuous
    ((continuous_pointFlatLinkDiskMap ha y f hd).comp
      (continuous_flatLinkSectorDiskPoint hβ.le hβπ ⟨hρ.le,hρL⟩))
    (fun t ↦ C.source (hb t))
  have hvnorm (t : unitInterval) : ‖v t‖ = ρ := by
    rw [C.retainedWidth_chart_norm (hb t),pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
    exact sectorPolar_norm hρ.le _
  have hmem (t : unitInterval) : ∃ θ ∈ Icc C.lo C.hi, v t = sectorPolar ρ θ := by
    obtain ⟨r,hr,θ,hθ,he⟩ := (C.retained (f (q t)) (hb t)).mp (hfP (q t))
    have hn := congrArg norm he
    rw [pointRadialSectorPoint_norm hr.1] at hn
    have hrρ : r = ρ := hn.symm.trans (hvnorm t)
    refine ⟨θ,hθ,?_⟩
    rw [sectorPolar_eq_pointRadialSectorPoint,← hrρ]
    exact he
  have hα : 0 ≤ coalescedPointExponent a y p/2 :=
    div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num)
  have hvdist (s t : unitInterval) :
      @dist ℂ (classicalConeMetricSpace (coalescedPointExponent a y p/2) hα).toDist (v s) (v t) =
        ‖sectorPolar ρ (β*s.1)-sectorPolar ρ (β*t.1)‖ := by
    change pointClassicalConeDist a y p (C.chart (f (q s))) (C.chart (f (q t))) = _
    rw [← C.metric (f (q s)) (hb s) (f (q t)) (hb t),hd]
    change dist (sectorPolar ρ (β*s.1)) (sectorPolar ρ (β*t.1)) = _
    exact dist_eq_norm _ _
  obtain ⟨hwidth,htrace⟩ := flatArc_anchored_old_upper_interval hα hρ hβ hβπ
    (C.coordinate_width_lt_full_of_admissible hadm) hvc hvnorm hmem hvdist hfirst
  refine ⟨hwidth,?_⟩
  intro s t
  rw [pointFlatLinkDiskMap_radial y hβ hβπ hL f hd K hρ hρL hρC s t]
  change s.1 • v t = _
  rw [htrace t]
  simp only [sectorPolar,Complex.real_smul,Complex.ofReal_mul]
  ring

/-- Exact occupied interval [hi-beta/k,hi] for the upper-end case. -/
theorem pointFlatLinkDisk_old_upper_occupancy
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (f : flatLinkSectorDisk β L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z)
    {P : Set ℂ} (hfP : ∀ x, f x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (f (flatLinkSectorDiskApex hβ.le hL.le)))
    (hadm : C.Admissible) {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ ≤ C.radius)
    (hfirst : C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)) =
      sectorPolar ρ C.hi) :
    let p := f (flatLinkSectorDiskApex hβ.le hL.le)
    let k := coalescedPointExponent a y p/2+1
    C.lo ≤ C.hi-β/k ∧ ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
      (z ∈ range f ↔ C.chart z ∈ pointClosedRadialInterval ρ (C.hi-β/k) C.hi) := by
  let p := f (flatLinkSectorDiskApex hβ.le hL.le)
  let k := coalescedPointExponent a y p/2+1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hw : 0 < β/k := div_pos hβ hk
  obtain ⟨hwidth,hpolar⟩ := pointFlatLinkDisk_old_upper_polar ha y hβ hβπ hL
    f hd hfP C hadm hρ hρL hρC hfirst
  refine ⟨hwidth,?_⟩
  intro z hz
  constructor
  · rintro ⟨x,rfl⟩
    have hx : ‖x.1‖ ≤ ρ := by rwa [pointFlatLinkDiskMap_dist_apex y hβ hL f hd] at hz
    obtain ⟨s,t,hst⟩ := flatLinkSectorDisk_representation hβ hβπ hρ hρL x hx
    rw [hst,hpolar]
    refine ⟨ρ*s.1,⟨mul_nonneg hρ.le s.2.1,mul_le_of_le_one_right hρ.le s.2.2⟩,
      C.hi-(β/k)*t.1,⟨?_,?_⟩,sectorPolar_eq_pointRadialSectorPoint _ _⟩
    · linarith [mul_le_of_le_one_right hw.le t.2.2]
    · linarith [mul_nonneg hw.le t.2.1]
  · rintro ⟨r,hr,θ,hθ,he⟩
    let s : unitInterval := ⟨r/ρ,div_nonneg hr.1 hρ.le,(div_le_one hρ).mpr hr.2⟩
    let t : unitInterval := ⟨(C.hi-θ)/(β/k),div_nonneg (sub_nonneg.mpr hθ.2) hw.le,
      (div_le_one hw).mpr (by linarith [hθ.1])⟩
    have hrs : ρ*s.1 = r := mul_div_cancel₀ _ hρ.ne'
    have hθt : C.hi-(β/k)*t.1 = θ := by
      change C.hi-(β/k)*((C.hi-θ)/(β/k)) = θ
      rw [mul_div_cancel₀ _ hw.ne']
      ring
    let x := flatLinkSectorDiskPoint hβ.le hβπ (ρ*s.1)
      ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t
    have hxC : (pointSmoothConformalEDist a y (f x) p).toReal ≤ C.radius := by
      rw [pointFlatLinkDiskMap_dist_apex y hβ hL f hd]
      change ‖sectorPolar (ρ*s.1) (β*t.1)‖ ≤ C.radius
      rw [sectorPolar_norm (mul_nonneg hρ.le s.2.1),hrs]
      exact hr.2.trans hρC
    refine ⟨x,C.chart.injOn (C.source hxC) (C.source (hz.trans hρC)) ?_⟩
    change C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (ρ*s.1) _ t)) = C.chart z
    rw [hpolar,hrs,hθt,sectorPolar_eq_pointRadialSectorPoint]
    exact he.symm

end RepulsiveCoulomb
