module

public import LeanResearch.RepulsiveCoulomb.PointFirstMarkedContact
public import LeanResearch.RepulsiveCoulomb.PointInteriorZeroExponentFlatChart

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Actual positive radial portions before the
constructed first marked direction cannot contain any marked point. The proof
uses actual fixed-endpoint/prefix identities, not a supplied correspondence
between arbitrary directions and marked endpoints. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- Every positive point of an actual retained minimizing edge whose true
physical direction is smaller than the finite minimum is unmarked. -/
theorem point_actual_open_direction_edge_unmarked
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρP : ∀ t, ρ t ∈ P)
    (C : PointRetainedConeNeighborhood a y P (ρ 0)) (hadm : C.Admissible)
    (M : {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)} → PointGeodesicTreeEdge a y)
    (hM0 : ∀ i, (M i).start = ρ 0) (hM1 : ∀ i, (M i).finish = i.1)
    (hMP : ∀ i t, (M i).curve t ∈ P)
    (χ : {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)} → ℝ)
    (hχ : ∀ i, χ i = C.actualPhysicalDirection ha y hadm (M i)
      (pointRayComparisonEdge ha y ρ hρ (M i)) (hM0 i) rfl (hMP i) (fun u ↦ hρP _))
    {β : ℝ} (hmin : ∀ i, β ≤ χ i)
    (E : PointGeodesicTreeEdge a y) (hE0 : E.start = ρ 0) (hEP : ∀ t, E.curve t ∈ P)
    (hdir : C.actualPhysicalDirection ha y hadm E (pointRayComparisonEdge ha y ρ hρ E)
      hE0 rfl hEP (fun u ↦ hρP _) < β) :
    ∀ t : unitInterval, 0 < t.1 → E.curve t ∉ pointSignedMarked ν α := by
  classical
  intro t ht hmark
  have hne : E.curve t ≠ ρ 0 := by
    intro he
    have hzero : E.curve 0 = ρ 0 := E.curve_start.trans hE0
    have ht0 := pointGeodesicTree_edges_injective ha y E (he.trans hzero.symm)
    have hv := congrArg Subtype.val ht0
    change t.1 = 0 at hv
    linarith
  let i : {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)} :=
    ⟨E.curve t, Finset.mem_erase.mpr ⟨hne, hmark⟩⟩
  have heq : χ i = C.actualPhysicalDirection ha y hadm E
      (pointRayComparisonEdge ha y ρ hρ E) hE0 rfl hEP (fun u ↦ hρP _) := by
    rw [hχ i]
    exact C.actualPhysicalDirection_of_endpoint_on_edge ha y ρ hρ hρP hadm
      E (M i) hE0 (hM0 i) hEP (hMP i) ht (hM1 i)
  have hle := hmin i
  rw [heq] at hle
  exact (not_lt_of_ge hle) hdir

/-- Genuine interior unmarked points have constructed whole flat metric disks
as soon as the actual nonzero interior curvature support is included in the
marked set. No stage-flatness certificate is supplied. -/
theorem point_actual_unmarked_interior_flatDisk
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (hcurv : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 →
      p ∈ pointSignedMarked ν α)
    {p : ℂ} (hp : p ∈ interior P) (hmark : p ∉ pointSignedMarked ν α) :
    Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P)
      ⟨p, interior_subset hp⟩) := by
  have hzero : coalescedPointExponent a y p = 0 := by
    by_contra hn
    exact hmark (hcurv p hp hn)
  exact exists_pointInterior_zeroExponent_flatDiskChart ha y hp hzero

end RepulsiveCoulomb
