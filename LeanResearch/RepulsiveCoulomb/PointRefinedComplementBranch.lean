module

public import LeanResearch.RepulsiveCoulomb.PointComplementCoordinateMaps
public import LeanResearch.RepulsiveCoulomb.PointRefinedAngularBranchPasting

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Fill every local branch law for an actual
unowned refined complement cell. The physical sector isometry, full range,
forward/inverse functions and seam formulas are all constructed. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem exists_pointRefinedComplementBranch
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ) {p : ℂ}
    (C : PointFlatLinkConeDisk a y p) {R ε : ℝ}
    (hR : 0 < R) (hRC : R ≤ C.radius) (hε : 0 < ε) (hεR : ε ≤ R)
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N}
    (Q : FiniteLinkComplementRefinement u owner (coalescedPointExponent a y p / 2 + 1))
    (width : Fin N → ℝ) (x : Σ j : Fin N, Fin (Q.count j))
    (hx : x.1 ∉ range owner) :
    ∃ B : PointRefinedAngularBranch C R ε Q width x,
      (∀ z ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x,
        ∀ w ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x,
          dist (B.forward z) (B.forward w) = (pointSmoothConformalEDist a y z w).toReal) ∧
      (∀ z ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width x,
        ∀ w ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width x,
          (pointSmoothConformalEDist a y (B.inverse z) (B.inverse w)).toReal = dist z w) := by
  classical
  let k := coalescedPointExponent a y p / 2 + 1
  let a₀ := Q.node x.1 x.2.castSucc
  let a₁ := Q.node x.1 x.2.succ
  let β := k * (a₁ - a₀)
  let b₀ := refinedIncidentTargetNode Q width x.1 x.2.castSucc
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  have hβ : 0 < β := mul_pos hk (sub_pos.mpr (Q.strictMono x.1 (show x.2.castSucc < x.2.succ from Fin.castSucc_lt_succ)))
  have hβπ : β ≤ Real.pi := Q.complement_short x.1 hx x.2
  have hspan : a₀ + β / k = a₁ := by
    dsimp [β]
    field_simp [hk.ne']
    ring
  have hnewhi : refinedIncidentTargetNode Q width x.1 x.2.succ = b₀ + β := by
    have h := refinedIncidentTargetNode_step Q width x.1 x.2
    rw [refinedIncidentTargetWidth, if_neg hx] at h
    change _ - b₀ = β at h
    linarith
  have hT : pointRefinedTargetSet ε Q width x = flatLinkOccupiedDisk ε b₀ (b₀ + β) := by
    unfold pointRefinedTargetSet
    rw [hnewhi]
  let g : flatLinkSectorDisk β R → ℂ := pointUnchangedConeSectorMap C a₀
  let F := pointComplementForward ha y C a₀ b₀ hβ hβπ hRC
  let G := pointComplementInverse C a₀ b₀ hβ hβπ hε hεR
  have hrange {z : ℂ} (hz : (pointSmoothConformalEDist a y z p).toReal ≤ R) :
      z ∈ range g ↔ z ∈ pointRefinedSourceSet C R Q x := by
    have h := pointUnchangedConeSectorMap_full_range ha y C a₀ hβ hβπ hR hRC z hz
    change z ∈ range g ↔ C.chart z ∈ flatLinkOccupiedDisk R a₀ (a₀ + β / k) at h
    change z ∈ range g ↔ C.chart z ∈ flatLinkOccupiedDisk R a₀ a₁
    simpa only [hspan] using h
  have hsource_range : pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x ⊆ range g := by
    intro z hz
    exact (hrange ((mem_pointConeOpenBall_iff C hRC z).mp hz.1).le).mpr hz.2
  have hFmap (w : flatLinkSectorDisk β R) : F (g w) = directedSectorPlacement b₀ β true w.1 :=
    pointComplementForward_apply_map ha y C a₀ b₀ hβ hβπ hRC w
  have hGtarget (z : ℂ) (hz : z ∈ pointRefinedTargetSet ε Q width x) :
      G z = g (directedSectorDiskRestriction hβ hβπ hε hεR b₀ true ⟨z, hT ▸ hz⟩) :=
    pointComplementInverse_apply_target C a₀ b₀ hβ hβπ hε hεR (hT ▸ hz)
  have htarget (w : flatLinkSectorDisk β R) (hw : ‖w.1‖ ≤ ε) :
      directedSectorPlacement b₀ β true w.1 ∈ pointRefinedTargetSet ε Q width x := by
    rw [hT, ← directedSectorPlacement_disk_range hβ hβπ hε b₀ true]
    exact ⟨⟨w.1, w.2.1, hw⟩, rfl⟩
  have hGsource (z : ℂ) (hz : z ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width x) :
      G z ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x := by
    let w := directedSectorDiskRestriction hβ hβπ hε hεR b₀ true ⟨z, hT ▸ hz.2⟩
    have hGz : G z = g w := hGtarget z hz.2
    have hdist : (pointSmoothConformalEDist a y (G z) p).toReal = ‖z‖ := by
      rw [hGz, pointUnchangedConeSectorMap_center_distance C a₀ hβ.le hβπ hR.le hRC,
        directedSectorDiskRestriction_norm]
    have hn : ‖z‖ < ε := by simpa only [mem_ball, dist_zero_right] using hz.1
    have hball : (pointSmoothConformalEDist a y (G z) p).toReal < R := by
      rw [hdist]
      exact hn.trans_le hεR
    exact ⟨(mem_pointConeOpenBall_iff C hRC _).mpr hball,
      (hrange hball.le).mp ⟨w, hGz.symm⟩⟩
  let t (top : Bool) : unitInterval := if top then 1 else 0
  have hold_end (top : Bool) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) R) :
      C.chart (g (flatLinkSectorDiskPoint hβ.le hβπ s hs (t top))) =
        sectorPolar s (refinedIncidentSourceEndpoint Q x top) := by
    rw [pointUnchangedConeSectorMap_polar C a₀ hβ.le hβπ hRC]
    cases top
    · change sectorPolar s (a₀ + β / k * 0) = sectorPolar s a₀
      rw [mul_zero, add_zero]
    · change sectorPolar s (a₀ + β / k * 1) = sectorPolar s a₁
      rw [mul_one, hspan]
  have hnew_end (top : Bool) (s : ℝ) :
      directedSectorPlacement b₀ β true (sectorPolar s (β * (t top).1)) =
        sectorPolar s (refinedIncidentTargetEndpoint Q width x top) := by
    rw [directedSectorPlacement_polar_unitInterval]
    cases top
    · change sectorPolar s (b₀ + β * 0) = sectorPolar s b₀
      rw [mul_zero, add_zero]
    · change sectorPolar s (b₀ + β * 1) = sectorPolar s
        (refinedIncidentTargetNode Q width x.1 x.2.succ)
      rw [mul_one, hnewhi]
  have hforward_end : ∀ z ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x,
      ∀ s : ℝ, 0 ≤ s → ∀ top : Bool,
      C.chart z = sectorPolar s (refinedIncidentSourceEndpoint Q x top) →
        F z = sectorPolar s (refinedIncidentTargetEndpoint Q width x top) := by
    intro z hz s hs top he
    have hsR : s < R := by
      have hh : dist (C.chart z) 0 < R := hz.1.2
      rw [dist_zero_right, he, sectorPolar_norm hs] at hh
      exact hh
    let w := flatLinkSectorDiskPoint hβ.le hβπ s ⟨hs, hsR.le⟩ (t top)
    have hgw : g w = z := by
      apply C.chart.injOn
        (C.source (pointUnchangedConeSectorMap_coordinate C a₀ hRC w).1) hz.1.1
      exact (hold_end top s ⟨hs, hsR.le⟩).trans he.symm
    rw [← hgw, hFmap]
    exact hnew_end top s
  have hinverse_end : ∀ z ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width x,
      ∀ s : ℝ, 0 ≤ s → ∀ top : Bool,
      z = sectorPolar s (refinedIncidentTargetEndpoint Q width x top) →
        C.chart (G z) = sectorPolar s (refinedIncidentSourceEndpoint Q x top) := by
    intro z hz s hs top he
    have hsε : s < ε := by
      have hh : dist z 0 < ε := hz.1
      rw [dist_zero_right, he, sectorPolar_norm hs] at hh
      exact hh
    let w := flatLinkSectorDiskPoint hβ.le hβπ s ⟨hs, hsε.le.trans hεR⟩ (t top)
    have hplaced : directedSectorPlacement b₀ β true w.1 = z := (hnew_end top s).trans he.symm
    have hwn : ‖w.1‖ ≤ ε := by
      change ‖sectorPolar s (β * (t top).1)‖ ≤ ε
      rw [sectorPolar_norm hs]
      exact hsε.le
    rw [← hplaced]
    dsimp only [G]
    rw [pointComplementInverse_apply_placed C a₀ b₀ hβ hβπ hε hεR w hwn]
    exact hold_end top s ⟨hs, hsε.le.trans hεR⟩
  let B : PointRefinedAngularBranch C R ε Q width x := {
    forward := F, inverse := G,
    forward_continuous := (pointComplementForward_continuousOn ha y C a₀ b₀ hβ hβπ hRC).mono hsource_range,
    inverse_continuous := by
      have h := pointComplementInverse_continuousOn ha y C a₀ b₀ hβ hβπ hR hRC hε hεR
      rw [← hT] at h
      exact h.mono inter_subset_right,
    forward_target := by
      intro z hz hFz
      obtain ⟨w, rfl⟩ := hsource_range hz
      have hn : ‖F (g w)‖ ≤ ε := by
        have hh : dist (F (g w)) 0 < ε := hFz
        simpa only [dist_zero_right] using hh.le
      rw [hFmap, directedSectorPlacement_norm] at hn
      rw [hFmap]
      exact htarget w hn,
    inverse_source := hGsource,
    left_inv := by
      intro z hz hFz
      apply pointComplement_left_inverse ha y C a₀ b₀ hβ hβπ hRC hε hεR (hsource_range hz)
      have hh : dist (F z) 0 < ε := hFz
      simpa only [dist_zero_right] using hh.le,
    right_inv := fun z hz ↦ pointComplement_right_inverse ha y C a₀ b₀ hβ hβπ hRC hε hεR (hT ▸ hz.2),
    forward_center := pointComplementForward_center ha y C a₀ b₀ hβ hβπ hR.le hRC,
    inverse_center := pointComplementInverse_center C a₀ b₀ hβ hβπ hR.le hε hεR,
    forward_endpoint := hforward_end,
    inverse_endpoint := hinverse_end
  }
  refine ⟨B, ?_, ?_⟩
  · intro z hz w hw
    obtain ⟨v, rfl⟩ := hsource_range hz
    obtain ⟨t, rfl⟩ := hsource_range hw
    change dist (F (g v)) (F (g t)) = _
    rw [hFmap, hFmap, (directedSectorPlacement b₀ β true).dist_eq,
      pointUnchangedConeSectorMap_metric C a₀ hβπ hRC]
    rfl
  · intro z hz w hw
    change (pointSmoothConformalEDist a y (G z) (G w)).toReal = _
    rw [hGtarget z hz.2, hGtarget w hw.2, pointUnchangedConeSectorMap_metric C a₀ hβπ hRC]
    change dist ((directedSectorPlacement b₀ β true).symm z)
      ((directedSectorPlacement b₀ β true).symm w) = dist z w
    exact (directedSectorPlacement b₀ β true).symm.dist_eq z w

end RepulsiveCoulomb
