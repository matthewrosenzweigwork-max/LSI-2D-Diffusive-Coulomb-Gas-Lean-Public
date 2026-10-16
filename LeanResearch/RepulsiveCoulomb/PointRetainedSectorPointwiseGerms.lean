import LeanResearch.RepulsiveCoulomb.PointRetainedApexInitialEntry

/-! SOURCE-ONLY, NOT COMPILED. Export the pointwise old-chart germs of BOTH
actual source rays. Their endpoints and occupied physical width are derived,
so the raw-initial-direction selector can be compared without a cap certificate. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

theorem pointRetainedSector_actual_two_ray_germs
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (hσP : ∀ x, σ x ∈ P)
    (hbottom : ∀ u : NNReal, σ (retainedApexBottomSource hβ.le hβπ u) ∈ frontier P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth) :
    ∃ δ cut endpoint : ℝ, 0 < δ ∧ δ < C.radius ∧
      cut ∈ Ioo C.lo C.hi ∧ endpoint ∈ Icc C.lo C.hi ∧
      ((endpoint=C.lo ∧ cut=C.lo+β/(1+coalescedPointExponent a y (σ (flatLinkSectorApex hβ.le))/2)) ∨
       (endpoint=C.hi ∧ cut=C.hi-β/(1+coalescedPointExponent a y (σ (flatLinkSectorApex hβ.le))/2))) ∧
      (∀ u : NNReal, (u:ℝ) ≤ δ → C.chart (σ (retainedApexUpperSource hβ.le hβπ u)) =
        pointRadialSectorPoint u cut) ∧
      (∀ u : NNReal, (u:ℝ) ≤ δ → C.chart (σ (retainedApexBottomSource hβ.le hβπ u)) =
        pointRadialSectorPoint u endpoint) := by
  let p := σ (flatLinkSectorApex hβ.le)
  let k := coalescedPointExponent a y p/2+1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  let δ := min 1 C.radius/2
  have hδ : 0 < δ := half_pos (lt_min (by norm_num) C.radius_pos)
  have hδ1 : δ ≤ 1 := by dsimp [δ]; linarith [min_le_left (1:ℝ) C.radius,lt_min (by norm_num : (0:ℝ)<1) C.radius_pos]
  have hδC : δ < C.radius := by dsimp [δ]; linarith [min_le_right (1:ℝ) C.radius,lt_min (by norm_num : (0:ℝ)<1) C.radius_pos]
  let f : flatLinkSectorDisk β 1 → ℂ := σ ∘ flatLinkSectorDiskInclusion
  have hf (x z : flatLinkSectorDisk β 1) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z := hσ _ _
  have hfP (x : flatLinkSectorDisk β 1) : f x ∈ P := hσP _
  have hfront : f (flatLinkSectorDiskPoint hβ.le hβπ δ ⟨hδ.le,hδ1⟩ 0) ∈ frontier P := by
    have he : flatLinkSectorDiskInclusion (flatLinkSectorDiskPoint hβ.le hβπ δ ⟨hδ.le,hδ1⟩ 0) =
        retainedApexBottomSource hβ.le hβπ ⟨δ,hδ.le⟩ := by
      apply Subtype.ext
      change sectorPolar δ (β * (0 : unitInterval).1) = sectorPolar δ 0
      simp only [Set.Icc.coe_zero, mul_zero]
    change σ (flatLinkSectorDiskInclusion _) ∈ frontier P
    rw [he]
    exact hbottom _
  have htop_of (cut : ℝ)
      (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ δ →
        (z ∈ range (fun u : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ u)) ↔
          C.chart z ∈ pointClosedRadialInterval δ cut cut)) :
      ∀ u : NNReal, (u:ℝ) ≤ δ → C.chart (σ (retainedApexUpperSource hβ.le hβπ u)) =
        pointRadialSectorPoint u cut := by
    intro u hu
    have hd : (pointSmoothConformalEDist a y (σ (retainedApexUpperSource hβ.le hβπ u)) p).toReal = u := by
      rw [hσ]
      change dist (sectorPolar u β) (0:ℂ) = u
      rw [dist_zero_right,sectorPolar_norm (NNReal.coe_nonneg u)]
    obtain ⟨r,hr,θ,hθ,he⟩ := (hT _ (hd.le.trans hu)).mp (mem_range_self u)
    have hθc : θ = cut := le_antisymm hθ.2 hθ.1
    have hn := congrArg norm he
    rw [pointRadialSectorPoint_norm hr.1] at hn
    have hru : r = (u:ℝ) := hn.symm.trans
      ((C.retainedWidth_chart_norm ((hd.le.trans hu).trans hδC.le)).trans hd)
    simpa only [hθc,hru] using he
  have hbottom_of (endpoint : ℝ)
      (htrace : ∀ s : unitInterval,
        C.chart (f (flatLinkSectorDiskPoint hβ.le hβπ (δ*s.1)
          ⟨mul_nonneg hδ.le s.2.1,(mul_le_of_le_one_right hδ.le s.2.2).trans hδ1⟩ 0)) =
          sectorPolar (δ*s.1) endpoint) :
      ∀ u : NNReal, (u:ℝ) ≤ δ → C.chart (σ (retainedApexBottomSource hβ.le hβπ u)) =
        pointRadialSectorPoint u endpoint := by
    intro u hu
    let s : unitInterval := ⟨(u:ℝ)/δ,div_nonneg u.2 hδ.le,(div_le_one hδ).mpr hu⟩
    have hus : δ*s.1 = u := mul_div_cancel₀ _ hδ.ne'
    have he : flatLinkSectorDiskInclusion (flatLinkSectorDiskPoint hβ.le hβπ (δ*s.1)
        ⟨mul_nonneg hδ.le s.2.1,(mul_le_of_le_one_right hδ.le s.2.2).trans hδ1⟩ 0) =
        retainedApexBottomSource hβ.le hβπ u := by
      apply Subtype.ext
      change sectorPolar (δ*s.1) (β*(0:unitInterval).1) = sectorPolar u 0
      simp only [hus,Set.Icc.coe_zero,mul_zero]
    have h := htrace s
    change C.chart (σ (flatLinkSectorDiskInclusion _)) = _ at h
    rw [he,hus,sectorPolar_eq_pointRadialSectorPoint] at h
    exact h
  rcases pointFlatLinkDisk_first_edge_endpoint hβ hβπ (by norm_num) f hf hfP C
      hδ hδ1 hδC hfront with hlo | hhi
  · obtain ⟨hlc,_,_,hT⟩ := pointRetainedApex_closed_sector_germs ha y hβ hβπ (by norm_num)
      σ hσ hσP C hC hδ hδ1 hδC.le hlo
    obtain ⟨_,hpolar⟩ := pointFlatLinkDisk_old_lower_polar ha y hβ hβπ (by norm_num)
      f hf hfP C hC hδ hδ1 hδC.le hlo
    have ho : k*((C.lo+β/k)-C.lo) = β := by rw [add_sub_cancel_left]; exact mul_div_cancel₀ _ hk.ne'
    have hc : C.lo+β/k < C.hi := by change β < k*(C.hi-C.lo) at hremain; nlinarith [ho]
    refine ⟨δ,C.lo+β/k,C.lo,hδ,hδC,⟨hlc,hc⟩,⟨le_rfl,C.width_pos.le⟩,
      Or.inl ⟨rfl,?_⟩,htop_of _ hT,hbottom_of C.lo ?_⟩
    · dsimp [k]; rw [add_comm (coalescedPointExponent a y p/2) 1]
    · intro s
      simpa only [Set.Icc.coe_zero,mul_zero,add_zero] using hpolar s 0
  · obtain ⟨_,hch,_,hT⟩ := pointRetainedApex_closed_sector_upper_germs ha y hβ hβπ (by norm_num)
      σ hσ hσP C hC hδ hδ1 hδC.le hhi
    obtain ⟨_,hpolar⟩ := pointFlatLinkDisk_old_upper_polar ha y hβ hβπ (by norm_num)
      f hf hfP C hC hδ hδ1 hδC.le hhi
    have ho : k*(C.hi-(C.hi-β/k)) = β := by rw [sub_sub_cancel]; exact mul_div_cancel₀ _ hk.ne'
    have hc : C.lo < C.hi-β/k := by change β < k*(C.hi-C.lo) at hremain; nlinarith [ho]
    refine ⟨δ,C.hi-β/k,C.hi,hδ,hδC,⟨hc,hch⟩,⟨C.width_pos.le,le_rfl⟩,
      Or.inr ⟨rfl,?_⟩,htop_of _ hT,hbottom_of C.hi ?_⟩
    · dsimp [k]; rw [add_comm (coalescedPointExponent a y p/2) 1]
    · intro s
      simpa only [Set.Icc.coe_zero,mul_zero,sub_zero] using hpolar s 0

end RepulsiveCoulomb
