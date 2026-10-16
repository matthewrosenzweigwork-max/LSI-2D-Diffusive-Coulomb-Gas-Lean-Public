module

public import LeanResearch.RepulsiveCoulomb.PointFiniteActualCutGeometry
public import LeanResearch.RepulsiveCoulomb.PointFlatEmbeddingClosure
public import LeanResearch.RepulsiveCoulomb.PointPassingEdgeOccupancy

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Feed the actually constructed finite prefix into
local surgery geometry. Interior regularity is recovered from its genuine
clean-sector construction, rather than added to the final allocation input.
No successful termination of the upstream blocked prefix is asserted. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem closedEuclideanSector_interior_nonempty {β : ℝ}
    (hβ : 0 < β) (hβπ : β ≤ Real.pi) :
    (interior (closedEuclideanSector β)).Nonempty := by
  obtain ⟨z, hz⟩ := retainedFlatSectorDisk_interior_nonempty hβ hβπ (by norm_num : (0 : ℝ) < 1)
  exact ⟨z, interior_mono (fun _ h ↦ h.1) hz⟩

theorem PointConstructedCutSector.interior_regular
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (K : PointGeometricCutState a y P ν α) (S : PointConstructedCutSector a y P ν α)
    (z : closedEuclideanSector S.beta) (hz : z.1 ∈ interior (closedEuclideanSector S.beta)) :
    coalescedPointExponent a y (S.map z) = 0 := by
  have harg := closedEuclideanSector_interior_strict_arg S.positive S.le_pi hz
  have hz0 : 0 < ‖z.1‖ := norm_pos_iff.mpr (fun he ↦ by
    have hh := harg.1
    rw [he, Complex.arg_zero] at hh
    exact lt_irrefl _ hh)
  obtain ⟨hP, hν, _⟩ := S.clean_open z hz0 harg.1 harg.2
  rw [K.interior_coeff _ hP] at hν
  exact (mul_eq_zero.mp hν).resolve_left (neg_ne_zero.mpr Real.pi_ne_zero)

/-- Every selected sector really is regular on its source interior. This
property survives forgetting the changing current halfplane in the list. -/
theorem PointFiniteActualCutPrefix.selected_interior_regular
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} {K : PointGeometricCutState a y P ν α}
    (T : PointFiniteActualCutPrefix a y K) :
    ∀ S ∈ T.sectors, ∀ z : closedEuclideanSector S.beta,
      z.1 ∈ interior (closedEuclideanSector S.beta) →
        coalescedPointExponent a y (S.map z) = 0 := by
  induction T with
  | blocked K hm hc => simp [PointFiniteActualCutPrefix.sectors]
  | terminal K B S hspent =>
      intro E hE
      have he : E = S.allocated := by
        simpa only [PointFiniteActualCutPrefix.sectors, List.mem_singleton] using hE
      subst E
      exact S.interior_regular B.state
  | next K B S O tail ih =>
      intro E hE
      rcases List.mem_cons.mp hE with he | he
      · subst E
        exact S.interior_regular B.state
      · exact ih E he

theorem PointFiniteActualCutPrefix.selected_openImage_isOpen
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} {K : PointGeometricCutState a y P ν α}
    (T : PointFiniteActualCutPrefix a y K) (S : PointActualAllocatedSector a y)
    (hS : S ∈ T.sectors) : IsOpen S.openImage :=
  pointFlatEmbedding_isOpen_openImage ha y S.map S.metric (T.selected_interior_regular S hS)

theorem PointActualAllocatedSector.isClosedEmbedding
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) : Topology.IsClosedEmbedding S.map :=
  pointFlatEmbedding_isClosedEmbedding ha y
    (closedEuclideanSector_isClosed S.positive S.le_pi) S.map S.metric

theorem PointActualAllocatedSector.closure_openImage
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) : closure S.openImage = range S.map :=
  pointFlatEmbedding_closure_openImage ha y
    (closedEuclideanSector_isClosed S.positive S.le_pi)
    (closedEuclideanSector_convex S.positive S.le_pi)
    (closedEuclideanSector_interior_nonempty S.positive S.le_pi) S.map S.metric

/-- Actual closed sector images in the selected family cannot enter another
selected open sector. This includes boundary points, not only open interiors. -/
theorem PointFiniteActualCutPrefix.closed_range_disjoint_openImage
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} {K : PointGeometricCutState a y P ν α}
    (T : PointFiniteActualCutPrefix a y K)
    (S E : PointActualAllocatedSector a y) (hE : E ∈ T.sectors)
    (hdis : Disjoint S.openImage E.openImage) :
    Disjoint (range S.map) E.openImage := by
  rw [← S.closure_openImage ha]
  exact hdis.closure_left (T.selected_openImage_isOpen ha y E hE)

/-- At a prescribed point all nonincident sectors can simultaneously be
discarded after shrinking one actual neighborhood. No local-finiteness or
clearance radius is assumed. This remains valid for the unmodified complement. -/
theorem PointFiniteActualCutPrefix.exists_neighborhood_avoiding_nonincident
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} {ν α : ℂ →₀ ℝ} {K : PointGeometricCutState a y P ν α}
    (T : PointFiniteActualCutPrefix a y K) (p : ℂ) :
    ∃ U : Set ℂ, IsOpen U ∧ p ∈ U ∧ ∀ S ∈ T.sectors,
      p ∉ range S.map → Disjoint U (range S.map) := by
  classical
  induction T.sectors with
  | nil => exact ⟨univ, isOpen_univ, mem_univ p, by simp⟩
  | cons S l ih =>
      obtain ⟨U, hU, hpU, havoid⟩ := ih
      by_cases hpS : p ∈ range S.map
      · exact ⟨U, hU, hpU, fun E hE hpE ↦ by
          rcases List.mem_cons.mp hE with he | he
          · exact False.elim (hpE (he ▸ hpS))
          · exact havoid E he hpE⟩
      · refine ⟨U ∩ (range S.map)ᶜ,
          hU.inter (S.isClosedEmbedding ha).isClosed_range.isOpen_compl,
          ⟨hpU, hpS⟩, fun E hE hpE ↦ ?_⟩
        rcases List.mem_cons.mp hE with he | he
        · subst E
          exact disjoint_compl_left.mono_left inter_subset_right
        · exact (havoid E he hpE).mono_left inter_subset_left

end RepulsiveCoulomb
