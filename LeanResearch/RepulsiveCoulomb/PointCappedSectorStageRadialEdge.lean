import LeanResearch.RepulsiveCoulomb.PointRetainedCappedSectorSeed
import LeanResearch.RepulsiveCoulomb.PointActualMarkedDirection
import LeanResearch.RepulsiveCoulomb.PointConvexLocalFlatEmbedding

/-! ISOLATED SOURCE-ONLY DRAFT. Construct each actual radial metric edge of a
finite convex flat stage and identify its true retained-chart raw direction
from literal agreement with the initial chart. A direction identity is proved,
not included in the stage data. No unbounded sector is assumed or asserted. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem convexDomainSegment_from_zero_val {K : Set ℂ} (hK : Convex ℝ K)
    (h0 : (0 : ℂ) ∈ K) (q : K) (t : unitInterval) :
    (convexDomainSegment hK ⟨0, h0⟩ q t).1 = t.1 • q.1 := by
  simp [convexDomainSegment, AffineMap.lineMap_apply_module']

/-- The source straight segment gives an actual minimizing edge, with its
literal image curve. Its metric witnesses are derived from the stage isometry. -/
def pointConvexRadialEdge
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    (q : K) (hq : q.1 ≠ 0) : PointGeodesicTreeEdge a y := by
  let p : K := ⟨0, h0⟩
  let γ : unitInterval → ℂ := fun t ↦ (f (convexDomainSegment hK p q t)).1
  have hne : (f p).1 ≠ (f q).1 := by
    intro he
    have h := hd p q
    rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at h
    have heq : p = q := dist_eq_zero.mp h.symm
    exact hq (congrArg Subtype.val heq).symm
  have hgeo : ∀ s t, (pointSmoothConformalEDist a y (γ s) (γ t)).toReal =
      |t.1 - s.1| * (pointSmoothConformalEDist a y (f p).1 (f q).1).toReal := by
    intro s t
    rw [hd, hd, convexDomainSegment_dist]
    exact mul_comm _ _
  exact ⟨(f p).1, (f q).1, hne, γ,
    congrArg (fun z : K ↦ (f z).1) (convexDomainSegment_zero hK p q),
    congrArg (fun z : K ↦ (f z).1) (convexDomainSegment_one hK p q),
    pointConformal_geodesic_continuous ha y γ hgeo, hgeo⟩

theorem pointConvexRadialEdge_mem
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    (q : K) (hq : q.1 ≠ 0) :
    ∀ t, (pointConvexRadialEdge ha y hK h0 f hd q hq).curve t ∈ P :=
  fun t ↦ (f (convexDomainSegment hK ⟨0, h0⟩ q t)).2

namespace PointRetainedConeNeighborhood
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}

/-- Direct full-interval coordinate formula for the actual chart seed. -/
theorem cappedFlatInverseCoordinate_formula (C : PointRetainedConeNeighborhood a y P p)
    (z : ℂ) :
    C.flatInverseCoordinate z = pointRadialSectorPoint ‖z‖
      (C.lo + (coalescedPointExponent a y p / 2 + 1)⁻¹ * Complex.arg z) := by
  unfold flatInverseCoordinate sectorAngularMap
  rw [conePhase_mul_sectorPolar, sectorPolar_eq_pointRadialSectorPoint]

/-- Literal seed agreement determines the constructed raw direction of the
actual stage radial edge. The retained physical width may exceed pi. -/
theorem actualRawAngle_of_capped_seed_stage
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    (C : PointRetainedConeNeighborhood a y P (f ⟨0, h0⟩).1) (hC : C.Admissible)
    {β : ℝ} (hβwidth : β ≤ C.flatPhysicalWidth)
    (hKsector : K ⊆ closedEuclideanSector β)
    (hseed : ∀ z : K, ‖z.1‖ ≤ C.radius → (f z).1 = C.flatInverse z.1)
    (q : K) (hq : q.1 ≠ 0) :
    C.actualInitialRawAngle ha y hC (pointConvexRadialEdge ha y hK h0 f hd q hq)
      rfl (pointConvexRadialEdge_mem ha y hK h0 f hd q hq) =
      C.lo + (coalescedPointExponent a y (f ⟨0, h0⟩).1 / 2 + 1)⁻¹ * Complex.arg q.1 := by
  let E := pointConvexRadialEdge ha y hK h0 f hd q hq
  have hEP := pointConvexRadialEdge_mem ha y hK h0 f hd q hq
  obtain ⟨r, τ, hr, hrR, hτ, _, hdr, hpolar⟩ :=
    C.actualInitialRawAngle_sample ha y hC E rfl hEP
  let z := convexDomainSegment hK ⟨0, h0⟩ q τ
  have hzpoint : E.curve τ = (f z).1 := rfl
  have hzr : ‖z.1‖ = r := by
    have h := hd z ⟨0, h0⟩
    change (pointSmoothConformalEDist a y (f z).1 (f ⟨0, h0⟩).1).toReal = dist z.1 0 at h
    rw [dist_zero_right] at h
    exact h.symm.trans hdr
  have hzarg : Complex.arg z.1 = Complex.arg q.1 := by
    rw [convexDomainSegment_from_zero_val hK h0 q τ, Complex.real_smul,
      Complex.arg_real_mul _ hτ]
  have hsample : C.chart (f z).1 = pointRadialSectorPoint r
      (C.actualInitialRawAngle ha y hC E rfl hEP) := by
    have h := hpolar 1
    have hlast : pointEdgeSubparam (0 : unitInterval) τ (1 : unitInterval) = τ :=
      pointEdgeSubparam_one 0 τ
    simpa only [hlast, Set.Icc.coe_one, one_mul, hzpoint] using h
  have hseedchart : C.chart (f z).1 = C.flatInverseCoordinate z.1 := by
    rw [hseed z (hzr.trans_le hrR.le)]
    exact (C.inverse_metricBall
      ((C.flatInverseCoordinate_norm z.1).trans_le (hzr.trans_le hrR.le))).2
  let A := coalescedPointExponent a y (f ⟨0, h0⟩).1 / 2 + 1
  have hA : 0 < A := by dsimp [A]; linarith [coalescedPointExponent_nonneg a y (f ⟨0, h0⟩).1]
  have hqsector := hKsector q.2
  have hangle : C.lo + A⁻¹ * Complex.arg q.1 ∈ Icc C.lo C.hi := by
    refine ⟨le_add_of_nonneg_right (mul_nonneg (inv_nonneg.mpr hA.le) hqsector.1), ?_⟩
    have hqwidth := hqsector.2.trans hβwidth
    have hbound := mul_le_mul_of_nonneg_left hqwidth (inv_nonneg.mpr hA.le)
    have he : A⁻¹ * C.flatPhysicalWidth = C.hi - C.lo := by
      change A⁻¹ * (A * (C.hi - C.lo)) = _
      rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
    rw [he] at hbound
    linarith
  have hcoordinates : pointRadialSectorPoint r
      (C.actualInitialRawAngle ha y hC E rfl hEP) =
        pointRadialSectorPoint r (C.lo + A⁻¹ * Complex.arg q.1) := by
    rw [← hsample, hseedchart, C.cappedFlatInverseCoordinate_formula, hzr, hzarg]
  exact (C.retained_polar_angle_unique hC hr hr.le
    (C.actualInitialRawAngle_spec ha y hC E rfl hEP).1 hangle hcoordinates).2

/-- With the actual clean comparison edge at the lower retained endpoint,
seed agreement proves the physical direction is the literal source argument.
The strict source-angle bounds also prove strict raw-link interior membership. -/
theorem actualPhysicalDirection_of_capped_seed_stage
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    (C : PointRetainedConeNeighborhood a y P (f ⟨0, h0⟩).1) (hC : C.Admissible)
    {β : ℝ} (hβwidth : β ≤ C.flatPhysicalWidth)
    (hKsector : K ⊆ closedEuclideanSector β)
    (hseed : ∀ z : K, ‖z.1‖ ≤ C.radius → (f z).1 = C.flatInverse z.1)
    (q : K) (hq : q.1 ≠ 0) (hqarg : Complex.arg q.1 ∈ Ioo (0 : ℝ) β)
    (F : PointGeodesicTreeEdge a y) (hF0 : F.start = (f ⟨0, h0⟩).1)
    (hFP : ∀ t, F.curve t ∈ P)
    (hFlo : C.actualInitialRawAngle ha y hC F hF0 hFP = C.lo) :
    let E := pointConvexRadialEdge ha y hK h0 f hd q hq
    let hEP := pointConvexRadialEdge_mem ha y hK h0 f hd q hq
    C.actualInitialRawAngle ha y hC E rfl hEP ∈ Ioo C.lo C.hi ∧
      C.actualPhysicalDirection ha y hC E F rfl hF0 hEP hFP = Complex.arg q.1 := by
  let E := pointConvexRadialEdge ha y hK h0 f hd q hq
  have hEP := pointConvexRadialEdge_mem ha y hK h0 f hd q hq
  have hraw := C.actualRawAngle_of_capped_seed_stage ha y hK h0 f hd hC
    hβwidth hKsector hseed q hq
  let A := coalescedPointExponent a y (f ⟨0, h0⟩).1 / 2 + 1
  have hA : 0 < A := by dsimp [A]; linarith [coalescedPointExponent_nonneg a y (f ⟨0, h0⟩).1]
  have hpositive : 0 < A⁻¹ * Complex.arg q.1 := mul_pos (inv_pos.mpr hA) hqarg.1
  have hupper : A⁻¹ * Complex.arg q.1 < C.hi - C.lo := by
    have h := mul_lt_mul_of_pos_left (hqarg.2.trans_le hβwidth) (inv_pos.mpr hA)
    have he : A⁻¹ * C.flatPhysicalWidth = C.hi - C.lo := by
      change A⁻¹ * (A * (C.hi - C.lo)) = _
      rw [← mul_assoc, inv_mul_cancel₀ hA.ne', one_mul]
    rwa [he] at h
  constructor
  · rw [hraw]
    change C.lo < C.lo + A⁻¹ * Complex.arg q.1 ∧
      C.lo + A⁻¹ * Complex.arg q.1 < C.hi
    constructor <;> linarith
  · unfold actualPhysicalDirection
    rw [hraw, hFlo]
    change A * |C.lo + A⁻¹ * Complex.arg q.1 - C.lo| = Complex.arg q.1
    rw [add_sub_cancel_left, abs_of_pos hpositive, ← mul_assoc, mul_inv_cancel₀ hA.ne', one_mul]

end PointRetainedConeNeighborhood
end RepulsiveCoulomb
