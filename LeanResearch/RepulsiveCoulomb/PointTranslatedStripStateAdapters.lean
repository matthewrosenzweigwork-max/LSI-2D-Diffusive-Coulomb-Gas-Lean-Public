module

public import LeanResearch.RepulsiveCoulomb.PointActualTranslatedStripResidual
public import LeanResearch.RepulsiveCoulomb.PointRetainedIntrinsicAmbientConvexity
public import LeanResearch.RepulsiveCoulomb.PointSignedSectorBudget

@[expose] public section

/-! NEW SOURCE-ONLY, UNCOMPILED. Output adapters for the actual translated cut.
The frozen supplied-strip construction is unchanged. These definitions expose
its ambient negative-side straightening, full-or-admissible retained charts,
all-point signed meaning, and preservation of an existing budget invariant.
They do not construct a new strip or an attained marked contact. -/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

namespace PlanarLineHalfplaneHomeomorphs

/-- An ambient homeomorphism, rather than only a homeomorphism of subtypes. -/
def negativeAmbientStraightening {line : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs line) : ℂ ≃ₜ ℂ :=
  D.straightening.trans Complex.conjCLE.toHomeomorph

@[simp] theorem negativeAmbientStraightening_apply {line : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs line) (x : ℂ) :
    D.negativeAmbientStraightening x = starRingEnd ℂ (D.straightening x) := rfl

/-- The constructed kept closure is the literal preimage required for another
application of the supplied-strip theorem. Complex conjugation exchanges the
two halfplanes and fixes the real boundary coordinate. -/
theorem closure_negative_eq_ambient_upper {line : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs line) :
    closure D.negative =
      D.negativeAmbientStraightening ⁻¹' planarClosedUpperHalfplane := by
  rw [D.negative_eq, ← D.straightening.preimage_closure]
  change D.straightening ⁻¹' closure {z : ℂ | z.im < 0} = _
  rw [Complex.closure_setOfPred_im_lt]
  ext x
  change (D.straightening x).im ≤ 0 ↔
    0 ≤ (starRingEnd ℂ (D.straightening x)).im
  simp only [Complex.conj_im, neg_nonneg]

theorem negativeAmbientStraightening_on_line {line : ℝ → ℂ}
    (D : PlanarLineHalfplaneHomeomorphs line) (t : ℝ) :
    D.negativeAmbientStraightening (line t) = (t : ℂ) := by
  rw [negativeAmbientStraightening_apply, D.on_line]
  simp

end PlanarLineHalfplaneHomeomorphs

/-- A reusable geometric state. Its constructor below produces every field
from actual cut outputs. This record is never an extra premise of that cut. -/
structure PointRetainedSignedHalfplaneState {m : ℕ}
    (a : Fin m → ℝ) (y : Fin m → ℂ) (P : Set ℂ) (ν α : ℂ →₀ ℝ) where
  ambient : ℂ ≃ₜ ℂ
  region_eq : P = ambient ⁻¹' planarClosedUpperHalfplane
  connected : IsConnected P
  charts : ∀ x ∈ P, ∃ C : PointRetainedConeNeighborhood a y P x,
    C.Full ∨ C.Admissible
  interior_coeff : ∀ x ∈ interior P, ν x = -Real.pi * coalescedPointExponent a y x
  boundary_coeff : ∀ x ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P x,
    C.Admissible ∧ ν x = Real.pi - C.flatPhysicalWidth
  exterior_coeff : ∀ x, x ∉ P → ν x = 0
  allocation_support : ∀ x, α x ≠ 0 → x ∈ P

/-- The literal full interval implies the actual entire closed metric disk is
retained. No uniqueness of a polar angle at the center or at 0=2*pi is used. -/
theorem PointRetainedConeNeighborhood.full_of_zero_two_pi
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    (hlo : C.lo = 0) (hhi : C.hi = 2 * Real.pi) : C.Full := by
  intro x hx
  apply (C.retained x hx).mpr
  rw [hlo, hhi, pointClosedRadialInterval_full_disk]
  exact C.onto.mapsTo hx

namespace PointRetainedSignedHalfplaneState

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ}

theorem isClosed (K : PointRetainedSignedHalfplaneState a y P ν α) : IsClosed P := by
  rw [K.region_eq]
  exact (isClosed_le continuous_const Complex.continuous_im).preimage K.ambient.continuous

theorem curvature_support (K : PointRetainedSignedHalfplaneState a y P ν α) :
    ∀ x, ν x ≠ 0 → x ∈ P := by
  intro x hx
  by_contra hxP
  exact hx (K.exterior_coeff x hxP)

theorem marked_support (K : PointRetainedSignedHalfplaneState a y P ν α) :
    (↑(pointSignedMarked ν α) : Set ℂ) ⊆ P :=
  pointSignedMarked_subset K.curvature_support K.allocation_support

/-- The existing local-to-global theorem now applies to the produced state.
This is an explicit invocation; bare existence of charts is not relabeled as
ambient convexity or intrinsic/ambient equality. -/
theorem intrinsic_eq_and_geodesicallyConvex
    (K : PointRetainedSignedHalfplaneState a y P ν α) (ha : ∀ j, 0 ≤ a j) :
    PointGeodesicallyConvex a y P ∧ ∀ x ∈ P, ∀ z ∈ P,
      pointRegionIntrinsicEDist ha y P x z = pointSmoothConformalEDist a y x z :=
  pointRetainedRegion_intrinsic_eq_and_geodesicallyConvex ha y
    K.isClosed K.connected.isPreconnected K.charts

end PointRetainedSignedHalfplaneState

/-- Allocation mass depends on alpha itself, including when the curvature
support acquires a new target or cancels at an old target. -/
theorem pointTranslatedStrip_budgetMass_unchanged (ν μ α : ℂ →₀ ℝ) :
    pointSignedBudgetMass μ α = pointSignedBudgetMass ν α := by
  rw [pointSignedBudgetMass_eq_support_sum, pointSignedBudgetMass_eq_support_sum]

/-- An existing scalar budget invariant passes to the actual transferred
coefficient. No new budget hypothesis is inserted into the cut theorem. -/
theorem pointTranslatedStrip_budgetInvariant_of_update
    {ν μ α : ℂ →₀ ℝ}
    (hnegative : ∀ x, pointSignedNegativePart μ x ≤ pointSignedNegativePart ν x)
    (hmass : pointSignedCurvatureMass μ α = pointSignedCurvatureMass ν α)
    (hbudget : PointSignedBudgetInvariant ν α) : PointSignedBudgetInvariant μ α := by
  have hA := pointTranslatedStrip_budgetMass_unchanged ν μ α
  refine ⟨fun x ↦ (hnegative x).trans (hbudget.dominates x), ?_, ?_⟩
  · rw [hA]
    exact hbudget.budget_pos
  · rw [hA, hmass]
    exact hbudget.mass_le

end RepulsiveCoulomb
