module

public import LeanResearch.RepulsiveCoulomb.PointCappedSectorStageRadialEdge

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Keep the supplied geometric apex as the
literal start field of each constructed finite-stage radial edge. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def pointConvexRadialEdgeAt
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    {p : ℂ} (hp : (f ⟨0, h0⟩).1 = p) (q : K) (hq : q.1 ≠ 0) :
    PointGeodesicTreeEdge a y where
  start := p
  finish := (f q).1
  distinct := by
    rw [← hp]
    exact (pointConvexRadialEdge ha y hK h0 f hd q hq).distinct
  curve := (pointConvexRadialEdge ha y hK h0 f hd q hq).curve
  curve_start := (pointConvexRadialEdge ha y hK h0 f hd q hq).curve_start.trans hp
  curve_finish := (pointConvexRadialEdge ha y hK h0 f hd q hq).curve_finish
  continuous := (pointConvexRadialEdge ha y hK h0 f hd q hq).continuous
  geodesic := by
    rw [← hp]
    exact (pointConvexRadialEdge ha y hK h0 f hd q hq).geodesic

theorem pointConvexRadialEdgeAt_mem
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    {p : ℂ} (hp : (f ⟨0, h0⟩).1 = p) (q : K) (hq : q.1 ≠ 0) :
    ∀ t, (pointConvexRadialEdgeAt ha y hK h0 f hd hp q hq).curve t ∈ P :=
  pointConvexRadialEdge_mem ha y hK h0 f hd q hq

theorem PointRetainedConeNeighborhood.actualPhysicalDirection_of_capped_seed_stage_at
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    {p : ℂ} (hp : (f ⟨0, h0⟩).1 = p)
    (C : PointRetainedConeNeighborhood a y P p) (hC : C.Admissible)
    {β : ℝ} (hβwidth : β ≤ C.flatPhysicalWidth)
    (hKsector : K ⊆ closedEuclideanSector β)
    (hseed : ∀ z : K, ‖z.1‖ ≤ C.radius → (f z).1 = C.flatInverse z.1)
    (q : K) (hq : q.1 ≠ 0) (hqarg : Complex.arg q.1 ∈ Ioo (0 : ℝ) β)
    (F : PointGeodesicTreeEdge a y) (hF0 : F.start = p)
    (hFP : ∀ t, F.curve t ∈ P)
    (hFlo : C.actualInitialRawAngle ha y hC F hF0 hFP = C.lo) :
    let E := pointConvexRadialEdgeAt ha y hK h0 f hd hp q hq
    let hEP := pointConvexRadialEdgeAt_mem ha y hK h0 f hd hp q hq
    C.actualInitialRawAngle ha y hC E rfl hEP ∈ Ioo C.lo C.hi ∧
      C.actualPhysicalDirection ha y hC E F rfl hF0 hEP hFP = Complex.arg q.1 := by
  subst p
  exact C.actualPhysicalDirection_of_capped_seed_stage ha y hK h0 f hd hC
    hβwidth hKsector hseed q hq hqarg F hF0 hFP hFlo

theorem PointRetainedConeNeighborhood.actualRawAngle_of_capped_seed_stage_at
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P K : Set ℂ} (hK : Convex ℝ K) (h0 : (0 : ℂ) ∈ K)
    (f : K → P)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x).1 (f z).1).toReal = dist x z)
    {p : ℂ} (hp : (f ⟨0, h0⟩).1 = p)
    (C : PointRetainedConeNeighborhood a y P p) (hC : C.Admissible)
    {β : ℝ} (hβwidth : β ≤ C.flatPhysicalWidth)
    (hKsector : K ⊆ closedEuclideanSector β)
    (hseed : ∀ z : K, ‖z.1‖ ≤ C.radius → (f z).1 = C.flatInverse z.1)
    (q : K) (hq : q.1 ≠ 0) :
    let E := pointConvexRadialEdgeAt ha y hK h0 f hd hp q hq
    let hEP := pointConvexRadialEdgeAt_mem ha y hK h0 f hd hp q hq
    C.actualInitialRawAngle ha y hC E rfl hEP =
      C.lo + (coalescedPointExponent a y p / 2 + 1)⁻¹ * Complex.arg q.1 := by
  subst p
  exact C.actualRawAngle_of_capped_seed_stage ha y hK h0 f hd hC hβwidth hKsector hseed q hq

end RepulsiveCoulomb
