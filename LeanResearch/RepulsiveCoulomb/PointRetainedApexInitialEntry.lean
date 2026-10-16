module

public import LeanResearch.RepulsiveCoulomb.PointRetainedApexUnorientedChart

@[expose] public section

/-! SOURCE-ONLY, NOT COMPILED. The free ray actually starts inside P, with
both old endpoint orientations proved. It also never meets the clean bottom
ray away from the apex. These are geometric first-return frontend inputs. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

def retainedApexBottomSource {β : ℝ} (hβ : 0 ≤ β) (hβπ : β ≤ Real.pi)
    (r : NNReal) : closedEuclideanSector β :=
  ⟨sectorPolar r 0, by simpa only [Set.Icc.coe_zero, mul_zero] using
    (flatLink_polar_mem_sector hβ hβπ (NNReal.coe_nonneg r) (0:unitInterval))⟩

/-- Strictly positive sector width makes the two global source rays disjoint
away from their common apex. Actual all-pairs isometry transfers this fact. -/
theorem retainedApex_free_ray_avoids_bottom
    {m : ℕ} {a : Fin m → ℝ} (y : Fin m → ℂ)
    {β : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    (r : NNReal) (hr : 0 < (r:ℝ)) :
    σ (retainedApexUpperSource hβ.le hβπ r) ∉
      range (fun u : NNReal ↦ σ (retainedApexBottomSource hβ.le hβπ u)) := by
  rintro ⟨u,hu⟩
  change σ (retainedApexBottomSource hβ.le hβπ u) =
    σ (retainedApexUpperSource hβ.le hβπ r) at hu
  have hd := hσ (retainedApexBottomSource hβ.le hβπ u)
    (retainedApexUpperSource hβ.le hβπ r)
  rw [hu,pointSmoothConformalEDist_self,ENNReal.toReal_zero] at hd
  have he := congrArg (fun x : closedEuclideanSector β ↦ x.1) (dist_eq_zero.mp hd.symm)
  change sectorPolar u 0 = sectorPolar r β at he
  have hn := congrArg norm he
  rw [sectorPolar_norm (NNReal.coe_nonneg u),sectorPolar_norm (NNReal.coe_nonneg r)] at hn
  have hu0 : 0 < (u:ℝ) := hn.symm ▸ hr
  have ha := congrArg Complex.arg he
  rw [sectorPolar_arg hu0 ⟨by linarith [Real.pi_pos],Real.pi_pos.le⟩,
    sectorPolar_arg hr ⟨by linarith [Real.pi_pos],hβπ⟩] at ha
  exact hβ.ne' ha.symm

/-- Positive remaining angle forces actual initial interior membership. The
boundary endpoint is inferred from a genuine positive-radius bottom point;
there is no assumed lower-end orientation or new-region input. -/
theorem pointRetainedApex_free_ray_initial_interior
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {β L : ℝ} (hβ : 0 < β) (hβπ : β ≤ Real.pi) (hL : 0 < L)
    (σ : closedEuclideanSector β → ℂ)
    (hσ : ∀ x z, (pointSmoothConformalEDist a y (σ x) (σ z)).toReal = dist x z)
    {P : Set ℂ} (hσP : ∀ x, σ x ∈ P)
    (C : PointRetainedConeNeighborhood a y P (σ (flatLinkSectorApex hβ.le)))
    (hC : C.Admissible) (hremain : β < C.flatPhysicalWidth)
    {ρ : ℝ} (hρ : 0 < ρ) (hρL : ρ ≤ L) (hρC : ρ < C.radius)
    (hfront : σ (flatLinkSectorDiskInclusion
      (flatLinkSectorDiskPoint hβ.le hβπ ρ ⟨hρ.le,hρL⟩ 0)) ∈ frontier P) :
    ∀ r : NNReal, 0 < (r:ℝ) → (r:ℝ) ≤ ρ →
      σ (retainedApexUpperSource hβ.le hβπ r) ∈ interior P := by
  let p := σ (flatLinkSectorApex hβ.le)
  let k := coalescedPointExponent a y p/2+1
  have hk : 0 < k := by dsimp [k]; linarith [coalescedPointExponent_nonneg a y p]
  let f : flatLinkSectorDisk β L → ℂ := σ ∘ flatLinkSectorDiskInclusion
  have hd (x z : flatLinkSectorDisk β L) :
      (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z :=
    hσ (flatLinkSectorDiskInclusion x) (flatLinkSectorDiskInclusion z)
  have hfP (x : flatLinkSectorDisk β L) : f x ∈ P := hσP _
  have hrad (r : NNReal) : (pointSmoothConformalEDist a y
      (σ (retainedApexUpperSource hβ.le hβπ r)) p).toReal = r := by
    rw [hσ]
    change dist (sectorPolar r β) (0:ℂ) = r
    rw [dist_zero_right,sectorPolar_norm (NNReal.coe_nonneg r)]
  have hfromRay (cut : ℝ) (hc : cut ∈ Ioo C.lo C.hi)
      (hT : ∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
        (z ∈ range (fun r : NNReal ↦ σ (retainedApexUpperSource hβ.le hβπ r)) ↔
          C.chart z ∈ pointClosedRadialInterval ρ cut cut)) :
      ∀ r : NNReal, 0 < (r:ℝ) → (r:ℝ) ≤ ρ →
        σ (retainedApexUpperSource hβ.le hβπ r) ∈ interior P := by
    intro r hr hrρ
    have hzρ := (hrad r).le.trans hrρ
    obtain ⟨s,hs,θ,hθ,he⟩ := (hT _ hzρ).mp (mem_range_self r)
    have hθc : θ = cut := le_antisymm hθ.2 hθ.1
    have hn := congrArg norm he
    rw [pointRadialSectorPoint_norm hs.1] at hn
    have hsr : s = (r:ℝ) := hn.symm.trans
      ((C.retainedWidth_chart_norm (hzρ.trans hρC.le)).trans (hrad r))
    apply C.mem_interior_of_strict_radial_coordinate (hzρ.trans_lt hρC) hr hc
    simpa only [hθc,hsr] using he
  rcases pointFlatLinkDisk_first_edge_endpoint hβ hβπ hL f hd hfP C
      hρ hρL hρC hfront with hlo | hhi
  · obtain ⟨hlc,_,_,hT⟩ := pointRetainedApex_closed_sector_germs ha y hβ hβπ hL
      σ hσ hσP C hC hρ hρL hρC.le hlo
    have ho : k*((C.lo+β/k)-C.lo) = β := by
      rw [add_sub_cancel_left]
      exact mul_div_cancel₀ _ hk.ne'
    have hc : C.lo+β/k < C.hi := by
      change β < k*(C.hi-C.lo) at hremain
      nlinarith [ho]
    exact hfromRay _ ⟨hlc,hc⟩ hT
  · obtain ⟨_,hch,_,hT⟩ := pointRetainedApex_closed_sector_upper_germs ha y hβ hβπ hL
      σ hσ hσP C hC hρ hρL hρC.le hhi
    have ho : k*(C.hi-(C.hi-β/k)) = β := by
      rw [sub_sub_cancel]
      exact mul_div_cancel₀ _ hk.ne'
    have hc : C.lo < C.hi-β/k := by
      change β < k*(C.hi-C.lo) at hremain
      nlinarith [ho]
    exact hfromRay _ ⟨hc,hch⟩ hT

end RepulsiveCoulomb
