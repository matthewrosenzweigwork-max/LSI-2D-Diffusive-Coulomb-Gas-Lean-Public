module

public import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicRadialGerms
public import LeanResearch.RepulsiveCoulomb.PointRetainedFlatSectorChart
public import LeanResearch.RepulsiveCoulomb.PointActualGeodesicUniqueness
public import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicAmbientConvexity
public import LeanResearch.RepulsiveCoulomb.PointSignedSectorBudget

@[expose] public section

/-!
ISOLATED SOURCE-ONLY DRAFT. Never compiled, staged, or accepted.

Construct the full ordered angular representative of an ACTUAL short minimizing
segment from retained chart membership and the proved actual radiality theorem.
No direction selector, principal argument, or positive-direction certificate is
an input. The coordinate is still raw: the frontier-endpoint and clean-boundary
continuation bridges needed to anchor it to a supplied clean ray and prove strict
positivity are deliberately NOT claimed in this module.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb
namespace PointRetainedConeNeighborhood
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}

/-- Admissibility prevents identification of the two raw interval endpoints.
This is a coordinate width bound; the physical retained width may exceed pi. -/
theorem admissible_coordinate_width_lt_two_pi
    (C : PointRetainedConeNeighborhood a y P p) (hadm : C.Admissible) :
    C.hi - C.lo < 2 * Real.pi := by
  have hA : 0 ≤ coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  by_contra h
  have hcomp : 2 * Real.pi - (C.hi - C.lo) ≤ 0 := by linarith
  have hprod := mul_nonpos_of_nonneg_of_nonpos hA hcomp
  change Real.pi ≤ (coalescedPointExponent a y p / 2 + 1) *
    (2 * Real.pi - (C.hi - C.lo)) at hadm
  linarith [Real.pi_pos]

/-- Injectivity on the actual ordered coordinate interval, not on a principal
argument interval. Admissibility, not a physical-width-at-most-pi assumption,
excludes endpoint wrap. -/
theorem retained_polar_angle_unique
    (C : PointRetainedConeNeighborhood a y P p) (hadm : C.Admissible)
    {r s θ φ : ℝ} (hr : 0 < r) (hs : 0 ≤ s)
    (hθ : θ ∈ Icc C.lo C.hi) (hφ : φ ∈ Icc C.lo C.hi)
    (he : pointRadialSectorPoint r θ = pointRadialSectorPoint s φ) :
    r = s ∧ θ = φ := by
  have hrs : r = s := by
    have h := congrArg norm he
    simpa only [pointRadialSectorPoint_norm hr.le,
      pointRadialSectorPoint_norm hs] using h
  subst s
  have hphase : (Circle.exp θ : ℂ) = (Circle.exp φ : ℂ) :=
    mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr hr.ne') he
  have htop : C.hi < C.lo + 2 * Real.pi := by
    linarith [C.admissible_coordinate_width_lt_two_pi hadm]
  refine ⟨rfl, ?_⟩
  exact (Circle.exp_injOn_Ico (a := C.lo) (b := C.lo + 2 * Real.pi)
    (by linarith)) ⟨hθ.1, hθ.2.trans_lt htop⟩
      ⟨hφ.1, hφ.2.trans_lt htop⟩ (Subtype.ext hphase)

/-- The unique raw angle is extracted from the chart image of an actual point.
Its radial coordinate is the actual apex distance, equivalently chart norm. -/
theorem exists_unique_retained_raw_angle
    (C : PointRetainedConeNeighborhood a y P p) (hadm : C.Admissible)
    {z : ℂ} (hz : z ∈ P)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius)
    (hzp : z ≠ p) :
    ∃! θ : ℝ, θ ∈ Icc C.lo C.hi ∧
      C.chart z = pointRadialSectorPoint ‖C.chart z‖ θ := by
  have hpR : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hz0 : C.chart z ≠ 0 := by
    intro h
    apply hzp
    exact C.chart.injOn (C.source hzR) (C.source hpR) (h.trans C.center.symm)
  obtain ⟨r, hr, θ, hθ, he⟩ := (C.retained z hzR).mp hz
  have hn : ‖C.chart z‖ = r := by
    rw [he, pointRadialSectorPoint_norm hr.1]
  have heθ : C.chart z = pointRadialSectorPoint ‖C.chart z‖ θ := by
    simpa only [hn] using he
  refine ⟨θ, ⟨hθ, heθ⟩, ?_⟩
  intro φ hφ
  exact (C.retained_polar_angle_unique hadm (norm_pos_iff.mpr hz0)
    (norm_nonneg _) hφ.1 hθ (hφ.2.symm.trans heθ)).2

/-- This choice comes from an actual point of a minimizing segment, never from
an externally supplied angular selector. -/
def retainedRawAngle
    (C : PointRetainedConeNeighborhood a y P p) (hadm : C.Admissible)
    {z : ℂ} (hz : z ∈ P)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius)
    (hzp : z ≠ p) : ℝ :=
  Classical.choose (C.exists_unique_retained_raw_angle hadm hz hzR hzp).exists

theorem retainedRawAngle_spec
    (C : PointRetainedConeNeighborhood a y P p) (hadm : C.Admissible)
    {z : ℂ} (hz : z ∈ P)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius)
    (hzp : z ≠ p) :
    C.retainedRawAngle hadm hz hzR hzp ∈ Icc C.lo C.hi ∧
      C.chart z = pointRadialSectorPoint ‖C.chart z‖
        (C.retainedRawAngle hadm hz hzR hzp) :=
  Classical.choose_spec (C.exists_unique_retained_raw_angle hadm hz hzR hzp).exists

/-- The raw angle just constructed describes the entire ACTUAL intrinsic
minimizing segment within the center chart. Radiality is proved by the accepted
intrinsic theorem, not assumed in this theorem's inputs. -/
theorem intrinsic_segment_retainedRawAngle
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hconn : IsPreconnected P)
    (hcharts : ∀ q ∈ P, Nonempty (PointRetainedConeNeighborhood a y P q))
    {p z : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible)
    (γ : unitInterval → ℂ) (h0 : γ 0 = p) (h1 : γ 1 = z)
    (hP : ∀ t, γ t ∈ P)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius)
    (hzp : z ≠ p)
    (hd : ∀ s t, (pointRegionIntrinsicEDist ha y P (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointRegionIntrinsicEDist ha y P p z).toReal) :
    ∀ t, C.chart (γ t) = pointRadialSectorPoint (t.1 * ‖C.chart z‖)
      (C.retainedRawAngle hadm (h1 ▸ hP 1) hzR hzp) := by
  have hrad := (C.intrinsic_geodesic_from_center_radial ha y hconn hcharts
    γ h0 h1 hP hzR hd).2
  have hθ := (C.retainedRawAngle_spec hadm (h1 ▸ hP 1) hzR hzp).2
  intro t
  calc
    C.chart (γ t) = t.1 • C.chart z := hrad t
    _ = t.1 • pointRadialSectorPoint ‖C.chart z‖
        (C.retainedRawAngle hadm (h1 ▸ hP 1) hzR hzp) :=
      congrArg (fun w : ℂ ↦ t.1 • w) hθ
    _ = _ := by
      simp only [pointRadialSectorPoint, Complex.real_smul, Complex.ofReal_mul]
      ring

/-- The same construction for an actual ambient minimizing segment contained
in P, as provided by the accepted admissible-region convexity theorem. -/
theorem actual_segment_retainedRawAngle
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p z : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible)
    (γ : unitInterval → ℂ) (h0 : γ 0 = p) (h1 : γ 1 = z)
    (hP : ∀ t, γ t ∈ P)
    (hzR : (pointSmoothConformalEDist a y z p).toReal ≤ C.radius)
    (hzp : z ≠ p)
    (hd : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y p z).toReal) :
    ∀ t, C.chart (γ t) = pointRadialSectorPoint (t.1 * ‖C.chart z‖)
      (C.retainedRawAngle hadm (h1 ▸ hP 1) hzR hzp) := by
  have hpR : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hL : (pointSmoothConformalEDist a y p z).toReal = ‖C.chart z‖ := by
    rw [pointSmoothConformalEDist_comm a y p z, C.metric z hzR p hpR,
      C.center, pointClassicalConeDist_apex]
  have hball (t : unitInterval) :
      (pointSmoothConformalEDist a y (γ t) p).toReal ≤ C.radius := by
    have h := hd t 0
    rw [h0, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg t.2.1] at h
    rw [h]
    apply (mul_le_of_le_one_left ENNReal.toReal_nonneg t.2.2).trans
    rwa [pointSmoothConformalEDist_comm a y p z]
  have hrad (t : unitInterval) : C.chart (γ t) = t.1 • C.chart z := by
    apply classicalCone_geodesic_from_apex_nonneg
      (α := coalescedPointExponent a y p / 2)
      (div_nonneg (coalescedPointExponent_nonneg a y p) (by norm_num))
      (fun s ↦ C.chart (γ s)) (C.chart z)
      ((congrArg C.chart h0).trans C.center) (congrArg C.chart h1)
    intro s u
    change pointClassicalConeDist a y p (C.chart (γ s)) (C.chart (γ u)) = _
    rw [← C.metric (γ s) (hball s) (γ u) (hball u), hd, hL]
  have hθ := (C.retainedRawAngle_spec hadm (h1 ▸ hP 1) hzR hzp).2
  intro t
  calc
    C.chart (γ t) = t.1 • C.chart z := hrad t
    _ = t.1 • pointRadialSectorPoint ‖C.chart z‖
        (C.retainedRawAngle hadm (h1 ▸ hP 1) hzR hzp) :=
      congrArg (fun w : ℂ ↦ t.1 • w) hθ
    _ = _ := by
      simp only [pointRadialSectorPoint, Complex.real_smul, Complex.ofReal_mul]
      ring

/-- From an arbitrary actual minimizing edge, construct a positive short
sample, its full ordered angle, and the actual radial formula for the prefix.
No sampled point, sample time, radial-germ certificate, or angle is an input. -/
theorem exists_actual_edge_initial_raw_angle
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E : PointGeodesicTreeEdge a y)
    (hstart : E.start = p) (hP : ∀ t, E.curve t ∈ P) :
    ∃ r : ℝ, ∃ τ : unitInterval, ∃ θ : ℝ,
      0 < r ∧ r < C.radius ∧ 0 < τ.1 ∧ τ.1 < 1 ∧
      θ ∈ Icc C.lo C.hi ∧
      (pointSmoothConformalEDist a y (E.curve τ) p).toReal = r ∧
      ∀ s : unitInterval,
        C.chart (E.curve (pointEdgeSubparam 0 τ s)) =
          pointRadialSectorPoint (s.1 * r) θ := by
  let L := (pointSmoothConformalEDist a y E.start E.finish).toReal
  have hL : 0 < L := ENNReal.toReal_pos
    (pointSmoothConformalEDist_ne_zero ha y E.distinct)
    (pointSmoothConformalEDist_lt_top ha y _ _).ne
  let r := min C.radius L / 2
  have hr : 0 < r := half_pos (lt_min C.radius_pos hL)
  have hrR : r < C.radius := by
    have h := min_le_left C.radius L
    dsimp [r]
    linarith [C.radius_pos]
  have hrL : r < L := by
    have h := min_le_right C.radius L
    dsimp [r]
    linarith
  let τ : unitInterval := ⟨r / L,
    (div_pos hr hL).le, ((div_lt_one hL).mpr hrL).le⟩
  have hτ0 : 0 < τ.1 := div_pos hr hL
  have hτ1 : τ.1 < 1 := (div_lt_one hL).mpr hrL
  have hdist : (pointSmoothConformalEDist a y (E.curve τ) p).toReal = r := by
    have h := E.geodesic τ 0
    have h0 : E.curve (0 : unitInterval) = p := E.curve_start.trans hstart
    rw [h0, Set.Icc.coe_zero, zero_sub, abs_neg, abs_of_nonneg τ.2.1] at h
    change (pointSmoothConformalEDist a y (E.curve τ) p).toReal = r / L * L at h
    simpa only [div_mul_cancel₀ _ hL.ne'] using h
  have hb : (pointSmoothConformalEDist a y (E.curve τ) p).toReal ≤ C.radius :=
    hdist.le.trans hrR.le
  have hzp : E.curve τ ≠ p := by
    intro h
    rw [h, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at hdist
    exact hr.ne' hdist.symm
  have hpR : (pointSmoothConformalEDist a y p p).toReal ≤ C.radius := by
    rw [pointSmoothConformalEDist_self, ENNReal.toReal_zero]
    exact C.radius_pos.le
  have hn : ‖C.chart (E.curve τ)‖ = r := by
    have h := hdist
    rw [C.metric _ hb p hpR, C.center, pointClassicalConeDist_apex] at h
    exact h
  let δ := pointGeodesicSubedge ha y E 0 τ hτ0
  have hδ0 : δ.curve 0 = p :=
    δ.curve_start.trans (E.curve_start.trans hstart)
  have hδ1 : δ.curve 1 = E.curve τ := δ.curve_finish
  have hδP : ∀ t, δ.curve t ∈ P := fun t ↦ hP _
  have hδgeo : ∀ s t,
      (pointSmoothConformalEDist a y (δ.curve s) (δ.curve t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y p (E.curve τ)).toReal := by
    have h := δ.geodesic
    change ∀ s t,
      (pointSmoothConformalEDist a y (δ.curve s) (δ.curve t)).toReal =
        |t.1 - s.1| * (pointSmoothConformalEDist a y (E.curve 0) (E.curve τ)).toReal at h
    have hE0 : E.curve (0 : unitInterval) = p := E.curve_start.trans hstart
    rwa [hE0] at h
  let θ := C.retainedRawAngle hadm (hP τ) hb hzp
  have hθ := (C.retainedRawAngle_spec hadm (hP τ) hb hzp).1
  refine ⟨r, τ, θ, hr, hrR, hτ0, hτ1, hθ, hdist, ?_⟩
  intro s
  have h := C.actual_segment_retainedRawAngle ha y hadm δ.curve
    hδ0 hδ1 hδP hb hzp hδgeo s
  change C.chart (δ.curve s) = pointRadialSectorPoint (s.1 * r)
    (C.retainedRawAngle hadm (hP τ) hb hzp)
  simpa only [hn] using h

/-- Two positive radial descriptions of the same actual initial edge give
the same full ordered angle. Evaluate them at the product of their sample
clocks; this is a positive time in both prefixes. -/
theorem actual_initial_raw_angle_unique
    (C : PointRetainedConeNeighborhood a y P p) (hadm : C.Admissible)
    (E : PointGeodesicTreeEdge a y)
    {r s θ φ : ℝ} {τ σ : unitInterval}
    (hr : 0 < r) (hs : 0 < s) (hτ : 0 < τ.1) (hσ : 0 < σ.1)
    (hθ : θ ∈ Icc C.lo C.hi) (hφ : φ ∈ Icc C.lo C.hi)
    (hfirst : ∀ u : unitInterval,
      C.chart (E.curve (pointEdgeSubparam 0 τ u)) =
        pointRadialSectorPoint (u.1 * r) θ)
    (hsecond : ∀ u : unitInterval,
      C.chart (E.curve (pointEdgeSubparam 0 σ u)) =
        pointRadialSectorPoint (u.1 * s) φ) : θ = φ := by
  have hparam : pointEdgeSubparam 0 τ σ = pointEdgeSubparam 0 σ τ := by
    apply Subtype.ext
    simp only [pointEdgeSubparam, AffineMap.lineMap_apply_module',
      Set.Icc.coe_zero, sub_zero, smul_eq_mul, add_zero]
    ring
  have he : pointRadialSectorPoint (σ.1 * r) θ =
      pointRadialSectorPoint (τ.1 * s) φ :=
    (hfirst σ).symm.trans
      ((congrArg (fun t ↦ C.chart (E.curve t)) hparam).trans (hsecond τ))
  exact (C.retained_polar_angle_unique hadm (mul_pos hσ hr)
    (mul_pos hτ hs).le hθ hφ he).2

/-- A unique full raw INITIAL GERM coordinate is constructed from the actual
edge. The witness data are actual short restrictions, not a supplied selector. -/
theorem exists_unique_actual_initial_raw_angle
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E : PointGeodesicTreeEdge a y)
    (hstart : E.start = p) (hP : ∀ t, E.curve t ∈ P) :
    ∃! θ : ℝ, θ ∈ Icc C.lo C.hi ∧
      ∃ r : ℝ, ∃ τ : unitInterval,
        0 < r ∧ r < C.radius ∧ 0 < τ.1 ∧ τ.1 < 1 ∧
        ∀ u : unitInterval,
          C.chart (E.curve (pointEdgeSubparam 0 τ u)) =
            pointRadialSectorPoint (u.1 * r) θ := by
  obtain ⟨r, τ, θ, hr, hrR, hτ, hτ1, hθ, _, hrad⟩ :=
    C.exists_actual_edge_initial_raw_angle ha y hadm E hstart hP
  refine ⟨θ, ⟨hθ, r, τ, hr, hrR, hτ, hτ1, hrad⟩, ?_⟩
  rintro φ ⟨hφ, s, σ, hs, _, hσ, _, hrad'⟩
  exact C.actual_initial_raw_angle_unique hadm E hs hr hσ hτ hφ hθ hrad' hrad

/-- The actual-edge germ selector is a CONSTRUCTION from the preceding theorem.
It is not part of the geometric input data. -/
def actualInitialRawAngle
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E : PointGeodesicTreeEdge a y)
    (hstart : E.start = p) (hP : ∀ t, E.curve t ∈ P) : ℝ :=
  Classical.choose (C.exists_unique_actual_initial_raw_angle ha y hadm E hstart hP).exists

theorem actualInitialRawAngle_spec
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : ℂ} (C : PointRetainedConeNeighborhood a y P p)
    (hadm : C.Admissible) (E : PointGeodesicTreeEdge a y)
    (hstart : E.start = p) (hP : ∀ t, E.curve t ∈ P) :
    C.actualInitialRawAngle ha y hadm E hstart hP ∈ Icc C.lo C.hi ∧
      ∃ r : ℝ, ∃ τ : unitInterval,
        0 < r ∧ r < C.radius ∧ 0 < τ.1 ∧ τ.1 < 1 ∧
        ∀ u : unitInterval,
          C.chart (E.curve (pointEdgeSubparam 0 τ u)) =
            pointRadialSectorPoint (u.1 * r)
              (C.actualInitialRawAngle ha y hadm E hstart hP) :=
  Classical.choose_spec
    (C.exists_unique_actual_initial_raw_angle ha y hadm E hstart hP).exists

/-- Unwrapped physical coordinates from either possible boundary endpoint.
The actual frontier ray still has to select which of these two formulas applies. -/
theorem retained_physical_coordinates_mem
    (C : PointRetainedConeNeighborhood a y P p)
    {θ : ℝ} (hθ : θ ∈ Icc C.lo C.hi) :
    (coalescedPointExponent a y p / 2 + 1) * (θ - C.lo) ∈
      Icc (0 : ℝ) C.flatPhysicalWidth ∧
    (coalescedPointExponent a y p / 2 + 1) * (C.hi - θ) ∈
      Icc (0 : ℝ) C.flatPhysicalWidth := by
  have hA : 0 ≤ coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  constructor <;> constructor
  · exact mul_nonneg hA (sub_nonneg.mpr hθ.1)
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_right hθ.2 C.lo) hA
  · exact mul_nonneg hA (sub_nonneg.mpr hθ.2)
  · exact mul_le_mul_of_nonneg_left (sub_le_sub_left hθ.1 C.hi) hA

end PointRetainedConeNeighborhood

/-- Construct the actual minimizing edge itself from accepted residual convexity.
The curve is unique by the accepted global actual fixed-endpoint theorem. -/
theorem exists_retained_actual_edge
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hclosed : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p,
      C.Full ∨ C.Admissible)
    {p x : ℂ} (hp : p ∈ P) (hx : x ∈ P) (hpx : p ≠ x) :
    ∃ E : PointGeodesicTreeEdge a y,
      E.start = p ∧ E.finish = x ∧ (∀ t, E.curve t ∈ P) ∧
      ∀ F : PointGeodesicTreeEdge a y,
        F.start = p → F.finish = x → E.curve = F.curve := by
  have hconv := (pointRetainedRegion_intrinsic_eq_and_geodesicallyConvex
    ha y hclosed hconn hcharts).1
  obtain ⟨γ, h0, h1, hc, hP, hd⟩ := hconv p hp x hx
  let E : PointGeodesicTreeEdge a y := ⟨p, x, hpx, γ, h0, h1, hc, hd⟩
  refine ⟨E, rfl, rfl, hP, ?_⟩
  intro F hF0 hF1
  have hFgeo := F.geodesic
  rw [hF0, hF1] at hFgeo
  exact pointConformal_geodesic_unique ha y p x E.curve F.curve
    E.curve_start E.curve_finish (F.curve_start.trans hF0)
    (F.curve_finish.trans hF1) hd hFgeo

/-- The exact residual atom formula, together with actual marked-set
cleanliness, implies INTRINSIC boundary width pi. It says nothing about the
ambient coalesced exponent, which is allowed to be positive. -/
theorem pointSigned_clean_boundary_physical_width_pi
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {q : ℂ}
    (C : PointRetainedConeNeighborhood a y P q) {ν α : ℂ →₀ ℝ}
    (hclean : q ∉ pointSignedMarked ν α)
    (hboundary : ν q = Real.pi - C.flatPhysicalWidth) :
    C.flatPhysicalWidth = Real.pi := by
  have hν := (pointSigned_eq_zero_off_marked hclean).1
  linarith

/-- The actual clean boundary patch is covered by a literal flat halfdisk,
even at a point with positive ambient coalesced exponent. -/
theorem pointSigned_clean_boundary_flat_halfdisk_image
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {q : ℂ}
    (C : PointRetainedConeNeighborhood a y P q) {ν α : ℂ →₀ ℝ}
    (hclean : q ∉ pointSignedMarked ν α)
    (hboundary : ν q = Real.pi - C.flatPhysicalWidth) :
    C.flatInverse '' {z : ℂ | 0 ≤ z.im ∧ ‖z‖ ≤ C.radius} =
      P ∩ {w | (pointSmoothConformalEDist a y w q).toReal ≤ C.radius} := by
  have hw := pointSigned_clean_boundary_physical_width_pi C hclean hboundary
  have h := C.flatInverse_image (by rw [hw])
  rwa [hw, retainedFlatSectorDisk_pi] at h

/-- The eventual Pro cap is positive only with actual alpha-support membership.
The link bound is derived by the accepted budget-cap theorem from the actual
boundary atom formula; membership in the larger marked set is insufficient. -/
theorem pointSigned_supported_initial_cap
    {ν α : ℂ →₀ ℝ} (H : PointSignedBudgetInvariant ν α)
    {p : ℂ} (hp : p ∈ α.support) {stripAngle : ℝ}
    (hboundary : ν p = Real.pi - stripAngle) :
    0 < min Real.pi (α p) ∧ min Real.pi (α p) ≤ Real.pi ∧
      min Real.pi (α p) ≤ stripAngle := by
  have hne : α p ≠ 0 := Finsupp.mem_support_iff.mp hp
  have hpos : 0 < α p := lt_of_le_of_ne (H.budget_nonneg p) hne.symm
  exact ⟨lt_min Real.pi_pos hpos, min_le_left _ _,
    H.min_pi_budget_le_boundary_angle p hboundary⟩

end RepulsiveCoulomb
