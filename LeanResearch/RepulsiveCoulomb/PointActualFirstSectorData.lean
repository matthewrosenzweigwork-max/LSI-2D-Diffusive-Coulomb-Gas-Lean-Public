module

public import LeanResearch.RepulsiveCoulomb.PointActualSectorBottomIdentification
public import LeanResearch.RepulsiveCoulomb.PointRetainedConeReflection

@[expose] public section

/-! ISOLATED SOURCE-ONLY DRAFT. Build the entire actual-data context from the
original halfplane, true finite nu/alpha geometry and budget, admissible local
charts, and genuine clean minimizing boundary ray. The endpoint orientation,
marked edges, full physical directions, positive finite minimum, and closest
first marked endpoint are all constructed rather than supplied.
-/
noncomputable section
open Set Topology
namespace RepulsiveCoulomb

theorem exists_actual_first_sector_data
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (HP : ℂ ≃ₜ ℂ) (hP : P = HP ⁻¹' planarClosedUpperHalfplane)
    (hclosed : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p, C.Full ∨ C.Admissible)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hmarks : (↑(pointSignedMarked ν α) : Set ℂ) ⊆ P)
    (hν : ∀ p ∈ frontier P, ∃ K : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (K.hi - K.lo))
    (hcurv : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ pointSignedMarked ν α)
    (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρP : ∀ t, ρ t ∈ P) (hfront : ∀ t, ρ t ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ))
    (hsupport : ρ 0 ∈ α.support)
    (C : PointRetainedConeNeighborhood a y P (ρ 0)) (hadm : C.Admissible) :
    ∃ D : PointActualSectorData a y ha P,
      D.nu = ν ∧ D.alpha = α ∧ D.ray = ρ ∧
      (∃ hι : Fintype {x : ℂ // x ∈ (pointSignedMarked D.nu D.alpha).erase (D.ray 0)},
        D.beta = @finiteCappedDirectionMinimum _ hι D.direction (min Real.pi (D.alpha (D.ray 0)))) ∧
      (D.beta < min Real.pi (D.alpha (D.ray 0)) →
        ∃ i, D.direction i = D.beta ∧
          (∀ j, D.direction j = D.beta → pointActualEdgeLength (D.markedEdge i) ≤ pointActualEdgeLength (D.markedEdge j)) ∧
          0 < pointActualEdgeLength (D.markedEdge i) ∧
          ∀ t : unitInterval, 0 < t.1 → t.1 < 1 →
            (D.markedEdge i).curve t ∉ pointSignedMarked D.nu D.alpha) := by
  let r : ℝ → ℂ := ρ ∘ Real.toNNReal
  have hr0 : r 0 = ρ 0 := by simp [r]
  have hrd : ∀ u ∈ Ici (0 : ℝ), ∀ v ∈ Ici (0 : ℝ),
      (pointSmoothConformalEDist a y (r u) (r v)).toReal = dist u v := by
    intro u hu v hv
    change (pointSmoothConformalEDist a y (ρ u.toNNReal) (ρ v.toNNReal)).toReal = _
    rw [hρ, NNReal.dist_eq, Real.toNNReal_of_nonneg hu, Real.toNNReal_of_nonneg hv, Real.dist_eq]
    rfl
  have hrfront : ∀ u ∈ Ici (0 : ℝ), r u ∈ frontier P := fun _ _ ↦ hfront _
  obtain ⟨K, hKadm, hKwidth, T, hT, _, hKlower⟩ :=
    exists_actual_clean_lower_retained_chart C hadm hclosed r hr0 hrd hrfront
  have hboundary : ∀ t : NNReal, 0 < t →
      ∃ A : PointRetainedConeNeighborhood a y P (ρ t), ν (ρ t) = Real.pi - A.flatPhysicalWidth := by
    intro t ht
    obtain ⟨A, hA⟩ := hν (ρ t) (hfront t)
    refine ⟨A, ?_⟩
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    nlinarith [hA]
  obtain ⟨A, hA⟩ := hν (ρ 0) (hfront 0)
  have hKA := K.physical_width_eq A
  have hνK : ν (ρ 0) = Real.pi - K.flatPhysicalWidth := by
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    nlinarith [hA, hKA]
  obtain ⟨hh, hhπ, hhwidth⟩ := pointSigned_supported_initial_cap hbudget hsupport hνK
  obtain ⟨E, hE0, hEP, hE1, χ, hχ, hχbounds, β, hβmin, hβpos, hβh,
      hβπ, hβwidth, hβχ, hatt, hclosest⟩ :=
    exists_point_actual_first_marked_contact ha y hclosed hconn hcharts hmarks
      ρ hρ hρP hfront hclean hboundary K hKadm hh hhπ hhwidth
  let D : PointActualSectorData a y ha P :=
    { halfplane := HP
      halfplane_eq := hP
      pieceCount := N
      pieces := pieces
      boundary_cover := hpieces
      nu := ν
      alpha := α
      budget := hbudget
      boundary_atom := hν
      interior_support := hcurv
      ray := ρ
      ray_metric := hρ
      ray_mem := hρP
      ray_frontier := hfront
      ray_clean := hclean
      chart := K
      admissible := hKadm
      lowerRadius := T
      lowerRadius_pos := hT
      lower_germ := by
        intro t ht
        have h := hKlower t.1 ⟨t.2, ht⟩
        change K.chart (ρ (Real.toNNReal t.1)) = pointRadialSectorPoint t.1 K.lo at h
        rw [Real.toNNReal_of_nonneg t.2] at h
        exact h
      beta := β
      beta_pos := hβpos
      beta_pi := hβπ
      beta_width := hβwidth
      beta_budget := hβh.trans (min_le_right _ _)
      markedEdge := E
      marked_start := hE0
      marked_finish := hE1
      marked_mem := hEP
      direction := χ
      direction_actual := hχ
      beta_first := hβχ }
  exact ⟨D, rfl, rfl, rfl, hβmin, hclosest⟩

end RepulsiveCoulomb
