module

public import LeanResearch.RepulsiveCoulomb.RetainedSectorBottomHalfDisk
public import LeanResearch.RepulsiveCoulomb.PointFlatLinkBoundaryFullness

@[expose] public section

/-! SOURCE-ONLY, NOT COMPILED. The sector covers the ENTIRE old region locally
at every positive bottom point. Both local source edges lie on the actual old
boundary, so full angular occupancy is derived; no old flat-angle premise or
relative-openness certificate is used. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointRetainedSector_bottom_locally_full
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (hσP : ∀ x, σ x ∈ P)
    (hbottom : ∀ u : NNReal, σ (retainedApexBottomSource hβ.le hβπ u) ∈ frontier P)
    (r : NNReal) (hr : 0 < (r:ℝ))
    (C : PointRetainedConeNeighborhood a y P (σ (retainedApexBottomSource hβ.le hβπ r)))
    (hC : C.Admissible) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z,
      (pointSmoothConformalEDist a y z (σ (retainedApexBottomSource hβ.le hβπ r))).toReal ≤ ε →
        (z ∈ range σ ↔ z ∈ P) := by
  obtain ⟨L,hL,hLr,hLsin⟩ := retainedSectorPassingHalfDisk_exists_radius hβ hβπ hr
  let f : flatLinkSectorDisk Real.pi L → ℂ := σ ∘ retainedSectorBottomHalfDisk hβ hβπ hLsin
  have hf (x z : flatLinkSectorDisk Real.pi L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z := by
    dsimp only [f, Function.comp_apply]
    rw [hσ]
    exact (retainedSectorBottomHalfDisk_isometry hβ hβπ hLsin).dist_eq x z
  have hfP (x : flatLinkSectorDisk Real.pi L) : f x ∈ P := hσP _
  have hapex : f (flatLinkSectorDiskApex Real.pi_pos.le hL.le) =
      σ (retainedApexBottomSource hβ.le hβπ r) := by
    change σ (retainedSectorBottomHalfDisk hβ hβπ hLsin
      (flatLinkSectorDiskApex Real.pi_pos.le hL.le)) = _
    rw [retainedSectorBottomHalfDisk_apex hβ hβπ hLsin hL.le (NNReal.coe_nonneg r)]
    rfl
  have hold : ∃ D : PointRetainedConeNeighborhood a y P
      (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)), D.Admissible := by
    rw [hapex]
    exact ⟨C,hC⟩
  obtain ⟨D,hD⟩ := hold
  let ε := min L D.radius/2
  have hε : 0 < ε := half_pos (lt_min hL D.radius_pos)
  have hεL : ε ≤ L := by dsimp [ε]; linarith [min_le_left L D.radius,lt_min hL D.radius_pos]
  have hεD : ε < D.radius := by dsimp [ε]; linarith [min_le_right L D.radius,lt_min hL D.radius_pos]
  have hedge (t : unitInterval) (ht : t = 0 ∨ t = 1) :
      f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ε ⟨hε.le,hεL⟩ t) ∈ frontier P := by
    let w := flatLinkSectorDiskPoint Real.pi_pos.le le_rfl ε ⟨hε.le,hεL⟩ t
    have hwim : w.1.im = 0 := by
      change (sectorPolar ε (Real.pi*t.1)).im = 0
      rcases ht with rfl | rfl <;> simp [sectorPolar_im]
    obtain ⟨u,hu,he⟩ := retainedSectorBottomHalfDisk_real_edge hβ hβπ hLsin hLr w hwim
    change σ (retainedSectorBottomHalfDisk hβ hβπ hLsin w) ∈ frontier P
    rw [he]
    exact hbottom u
  obtain ⟨_,hocc⟩ := pointFlatLinkDisk_fills_old_boundary_interval ha y Real.pi_pos le_rfl hL
    f hf hfP D hD hε hεL hεD (hedge 0 (Or.inl rfl)) (hedge 1 (Or.inr rfl))
  rw [hapex] at hocc
  refine ⟨ε,hε,?_⟩
  intro z hz
  exact (pointRetainedSectorBottomHalfDisk_germ y hβ hβπ hLsin r.2 σ hσ (hz.trans hεL)).trans
    (hocc z hz)

end RepulsiveCoulomb
