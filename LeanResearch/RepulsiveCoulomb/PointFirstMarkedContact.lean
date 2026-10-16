module

public import LeanResearch.RepulsiveCoulomb.PointFirstMarkedMinimum
public import LeanResearch.RepulsiveCoulomb.PointInitialDirectionSubsegment

@[expose] public section

/-! ISOLATED SOURCE-ONLY bounded first marked contact.
No sector embedding, extension to infinity, old-boundary return exclusion, or
maximality conclusion is asserted. No Lean runs or canonical staging. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- A distance-minimal actual endpoint among equal constructed directions has
no earlier actual marked point on its segment. The earlier point's chosen
segment is identified with the actual prefix, and both initial coordinates
are proved equal by the source-clock subsegment theorem. -/
theorem pointClosestActualDirection_no_earlier_mark
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρP : ∀ t, ρ t ∈ P)
    (C : PointRetainedConeNeighborhood a y P (ρ 0)) (hadm : C.Admissible)
    (E : {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)} →
      PointGeodesicTreeEdge a y)
    (hE0 : ∀ i, (E i).start = ρ 0)
    (hE1 : ∀ i, (E i).finish = i.1)
    (hEP : ∀ i t, (E i).curve t ∈ P)
    (χ : {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)} → ℝ)
    (hχ : ∀ i, χ i = C.actualPhysicalDirection ha y hadm (E i)
      (pointRayComparisonEdge ha y ρ hρ (E i)) (hE0 i) rfl (hEP i) (fun u ↦ hρP _))
    {β : ℝ} (i : {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)})
    (hi : χ i = β)
    (hmin : ∀ j, χ j = β → pointActualEdgeLength (E i) ≤ pointActualEdgeLength (E j)) :
    ∀ t : unitInterval, 0 < t.1 → t.1 < 1 →
      (E i).curve t ∉ pointSignedMarked ν α := by
  classical
  intro t ht ht1 hmark
  have hne : (E i).curve t ≠ ρ 0 := by
    intro he
    have hcurve0 : (E i).curve 0 = ρ 0 := (E i).curve_start.trans (hE0 i)
    have ht0 := pointGeodesicTree_edges_injective ha y (E i) (he.trans hcurve0.symm)
    have hv := congrArg Subtype.val ht0
    change t.1 = 0 at hv
    linarith
  let j : {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)} :=
    ⟨(E i).curve t, Finset.mem_erase.mpr ⟨hne, hmark⟩⟩
  have hfinish : (E j).finish = (E i).curve t := hE1 j
  have hdir : χ j = χ i := by
    rw [hχ j, hχ i]
    exact C.actualPhysicalDirection_of_endpoint_on_edge ha y ρ hρ hρP hadm
      (E i) (E j) (hE0 i) (hE0 j) (hEP i) (hEP j) ht hfinish
  have hdist := hmin j (hdir.trans hi)
  have hlength := pointActualEdgeLength_of_endpoint_on_edge (E i) (E j)
    ((hE0 j).trans (hE0 i).symm) t hfinish
  rw [hlength] at hdist
  have hL := pointActualEdgeLength_pos ha y (E i)
  nlinarith

/-- Complete bounded first-direction/contact construction from the actual
closed region, actual retained charts, actual marked set, and actual clean ray.
The cap h is ordinary positive geometric input; the Pro alpha cap is supplied
by pointSigned_supported_initial_cap using alpha.support and the atom identity.

The output directions are the actual constructed germ coordinates. Beta is the
literal finite minimum. If beta<h, the closest actual beta-direction endpoint
is reached at finite positive distance and its open segment is unmarked. -/
theorem exists_point_actual_first_marked_contact
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hclosed : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p,
      C.Full ∨ C.Admissible)
    {ν α : ℂ →₀ ℝ} (hmarks : (↑(pointSignedMarked ν α) : Set ℂ) ⊆ P)
    (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρP : ∀ t, ρ t ∈ P) (hfront : ∀ t, ρ t ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ))
    (hboundary : ∀ t : NNReal, 0 < t →
      ∃ D : PointRetainedConeNeighborhood a y P (ρ t),
        ν (ρ t) = Real.pi - D.flatPhysicalWidth)
    (C : PointRetainedConeNeighborhood a y P (ρ 0)) (hadm : C.Admissible)
    {h : ℝ} (hh : 0 < h) (hhpi : h ≤ Real.pi) (hhwidth : h ≤ C.flatPhysicalWidth) :
    let ι := {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)}
    ∃ E : ι → PointGeodesicTreeEdge a y,
      ∃ hE0 : ∀ i, (E i).start = ρ 0,
      ∃ hEP : ∀ i t, (E i).curve t ∈ P,
      (∀ i, (E i).finish = i.1) ∧
      ∃ χ : ι → ℝ,
        (∀ i, χ i = C.actualPhysicalDirection ha y hadm (E i)
          (pointRayComparisonEdge ha y ρ hρ (E i)) (hE0 i) rfl (hEP i) (fun u ↦ hρP _)) ∧
        (∀ i, 0 < χ i ∧ χ i ≤ C.flatPhysicalWidth) ∧
        ∃ β : ℝ,
          (∃ hι : Fintype ι, β = @finiteCappedDirectionMinimum ι hι χ h) ∧
          0 < β ∧ β ≤ h ∧ β ≤ Real.pi ∧ β ≤ C.flatPhysicalWidth ∧
          (∀ i, β ≤ χ i) ∧ (β = h ∨ ∃ i, χ i = β) ∧
          (β < h → ∃ i, χ i = β ∧
            (∀ j, χ j = β → pointActualEdgeLength (E i) ≤ pointActualEdgeLength (E j)) ∧
            0 < pointActualEdgeLength (E i) ∧
            ∀ t : unitInterval, 0 < t.1 → t.1 < 1 →
              (E i).curve t ∉ pointSignedMarked ν α) := by
  obtain ⟨E, hE0, hEP, hE1, χ, hχ, hχbounds, hendpoint,
    β, hβmin, hβpos, hβh, hβpi, hβwidth, hβχ, hatt, hclosest⟩ :=
    exists_point_actual_first_marked_direction ha y hclosed hconn hcharts hmarks
      ρ hρ hρP hfront hclean hboundary C hadm hh hhpi hhwidth
  refine ⟨E, hE0, hEP, hE1, χ, hχ, hχbounds, β, hβmin, hβpos,
    hβh, hβpi, hβwidth, hβχ, hatt, ?_⟩
  intro hlt
  obtain ⟨i, hi, hmin⟩ := hclosest hlt
  exact ⟨i, hi, hmin, pointActualEdgeLength_pos ha y (E i),
    pointClosestActualDirection_no_earlier_mark ha y ρ hρ hρP C hadm
      E hE0 hE1 hEP χ hχ i hi hmin⟩

end RepulsiveCoulomb
