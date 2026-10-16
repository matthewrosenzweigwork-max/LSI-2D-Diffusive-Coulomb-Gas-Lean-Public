module

public import LeanResearch.RepulsiveCoulomb.PointFlatLinkOccupancy
public import LeanResearch.RepulsiveCoulomb.PointRetainedConeNeighborhood

@[expose] public section

/-! SOURCE-ONLY, NOT COMPILED. An actual isometric halfdisk supplies not only
its occupied interval, but the EXACT pair of radial edge germs. Orientation
is kept as the derived Boolean from the actual metric cone chart. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

private theorem halfDisk_polar_im_zero_cases {r : ℝ} (hr : 0 ≤ r)
    (t : unitInterval) (hz : (sectorPolar r (Real.pi*t.1)).im = 0) :
    r = 0 ∨ t = 0 ∨ t = 1 := by
  by_cases hr0 : r = 0
  · exact Or.inl hr0
  by_cases ht0 : t = 0
  · exact Or.inr (Or.inl ht0)
  by_cases ht1 : t = 1
  · exact Or.inr (Or.inr ht1)
  have ht0' : 0 < t.1 := lt_of_le_of_ne t.2.1
    (fun he ↦ ht0 (Subtype.ext he.symm))
  have ht1' : t.1 < 1 := lt_of_le_of_ne t.2.2
    (fun he ↦ ht1 (Subtype.ext he))
  have hs : 0 < Real.sin (Real.pi*t.1) := Real.sin_pos_of_pos_of_lt_pi
    (mul_pos Real.pi_pos ht0') (by nlinarith [Real.pi_pos])
  rw [sectorPolar_im] at hz
  exact False.elim ((mul_pos (lt_of_le_of_ne hr (Ne.symm hr0)) hs).ne' hz)

private theorem halfDisk_oriented_zero_or_top (forward : Bool) (width : ℝ)
    {t : unitInterval} (ht : t = 0 ∨ t = 1) :
    flatLinkOrientedAngle forward width t = 0 ∨ flatLinkOrientedAngle forward width t = width := by
  rcases ht with rfl | rfl <;> cases forward <;> simp [flatLinkOrientedAngle]

private theorem halfDisk_oriented_edge_surjective (forward : Bool) (width : ℝ)
    {θ : ℝ} (hθ : θ = 0 ∨ θ = width) :
    ∃ t : unitInterval, (t = 0 ∨ t = 1) ∧ flatLinkOrientedAngle forward width t = θ := by
  rcases hθ with rfl | rfl <;> cases forward
  · exact ⟨1,Or.inr rfl,by simp [flatLinkOrientedAngle]⟩
  · exact ⟨0,Or.inl rfl,by simp [flatLinkOrientedAngle]⟩
  · exact ⟨0,Or.inl rfl,by simp [flatLinkOrientedAngle]⟩
  · exact ⟨1,Or.inr rfl,by simp [flatLinkOrientedAngle]⟩

/-- Both local images are proved from the actual isometric halfdisk. No
occupied-side angle, edge-ray placement, or residual chart is a hypothesis. -/
theorem exists_pointFlatHalfDisk_occupied_and_edge_germs
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {L : ℝ} (hL : 0 < L) (f : flatLinkSectorDisk Real.pi L → ℂ)
    (hd : ∀ x z, (pointSmoothConformalEDist a y (f x) (f z)).toReal = dist x z) :
    ∃ C : PointFlatLinkConeDisk a y (f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)),
      ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ L ∧ ρ ≤ C.radius ∧
      let p := f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)
      let cut := Real.pi/(coalescedPointExponent a y p/2+1)
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
        (z ∈ range f ↔ C.chart z ∈ pointClosedRadialInterval ρ 0 cut)) ∧
      (∀ z, (pointSmoothConformalEDist a y z p).toReal ≤ ρ →
        (z ∈ f '' {w | w.1.im = 0} ↔ C.chart z ∈
          pointClosedRadialInterval ρ 0 0 ∪ pointClosedRadialInterval ρ cut cut)) ∧
      (coalescedPointExponent a y p/2+1)*cut = Real.pi := by
  obtain ⟨C,ρ,hρ,hρL,hρC,forward,hpolar,hocc,hwidth⟩ :=
    exists_pointFlatLinkDisk_occupancy ha y Real.pi_pos le_rfl hL f hd
  let p := f (flatLinkSectorDiskApex Real.pi_pos.le hL.le)
  let cut := Real.pi/(coalescedPointExponent a y p/2+1)
  have hconvert (R lo hi : ℝ) :
      flatLinkOccupiedDisk R lo hi = pointClosedRadialInterval R lo hi := by
    simp only [flatLinkOccupiedDisk,pointClosedRadialInterval,sectorPolar_eq_pointRadialSectorPoint]
  refine ⟨C,ρ,hρ,hρL,hρC,?_,?_,hwidth⟩
  · intro z hz
    simpa only [hconvert] using hocc z hz
  · intro z hz
    constructor
    · rintro ⟨x,hxim,rfl⟩
      have hx : ‖x.1‖ ≤ ρ := by
        rwa [pointFlatLinkDiskMap_dist_apex y Real.pi_pos hL f hd] at hz
      obtain ⟨s,t,hst⟩ := flatLinkSectorDisk_representation Real.pi_pos le_rfl hρ hρL x hx
      change x.1.im = 0 at hxim
      have him : (sectorPolar (ρ*s.1) (Real.pi*t.1)).im = 0 := by
        rw [hst] at hxim
        exact hxim
      rcases halfDisk_polar_im_zero_cases (mul_nonneg hρ.le s.2.1) t him with hr0 | ht
      · left
        refine ⟨0,⟨le_rfl,hρ.le⟩,0,⟨le_rfl,le_rfl⟩,?_⟩
        rw [hst,hpolar,hr0,sectorPolar_zero,pointRadialSectorPoint_zero]
      · have he := halfDisk_oriented_zero_or_top forward cut ht
        have hr : ρ*s.1 ∈ Icc (0:ℝ) ρ :=
          ⟨mul_nonneg hρ.le s.2.1,mul_le_of_le_one_right hρ.le s.2.2⟩
        rcases he with hzero | htop
        · left
          refine ⟨ρ*s.1,hr,0,⟨le_rfl,le_rfl⟩,?_⟩
          rw [hst,hpolar]
          change sectorPolar (ρ*s.1) (flatLinkOrientedAngle forward cut t) = _
          rw [hzero,sectorPolar_eq_pointRadialSectorPoint]
        · right
          refine ⟨ρ*s.1,hr,cut,⟨le_rfl,le_rfl⟩,?_⟩
          rw [hst,hpolar]
          change sectorPolar (ρ*s.1) (flatLinkOrientedAngle forward cut t) = _
          rw [htop,sectorPolar_eq_pointRadialSectorPoint]
    · intro hedge
      have hrepr : ∃ r ∈ Icc (0:ℝ) ρ, ∃ θ : ℝ,
          (θ=0 ∨ θ=cut) ∧ C.chart z = pointRadialSectorPoint r θ := by
        rcases hedge with ⟨r,hr,θ,hθ,he⟩ | ⟨r,hr,θ,hθ,he⟩
        · exact ⟨r,hr,θ,Or.inl (le_antisymm hθ.2 hθ.1),he⟩
        · exact ⟨r,hr,θ,Or.inr (le_antisymm hθ.2 hθ.1),he⟩
      obtain ⟨r,hr,θ,hθ,he⟩ := hrepr
      obtain ⟨t,ht,htθ⟩ := halfDisk_oriented_edge_surjective forward cut hθ
      let s : unitInterval := ⟨r/ρ,div_nonneg hr.1 hρ.le,(div_le_one hρ).mpr hr.2⟩
      have hrs : ρ*s.1 = r := mul_div_cancel₀ _ hρ.ne'
      let x := flatLinkSectorDiskPoint Real.pi_pos.le le_rfl (ρ*s.1)
        ⟨mul_nonneg hρ.le s.2.1,(mul_le_of_le_one_right hρ.le s.2.2).trans hρL⟩ t
      have hxim : x.1.im = 0 := by
        change (sectorPolar (ρ*s.1) (Real.pi*t.1)).im = 0
        rcases ht with rfl | rfl <;> simp [sectorPolar_im]
      have hxC : (pointSmoothConformalEDist a y (f x) p).toReal ≤ C.radius := by
        rw [pointFlatLinkDiskMap_dist_apex y Real.pi_pos hL f hd]
        change ‖sectorPolar (ρ*s.1) (Real.pi*t.1)‖ ≤ C.radius
        rw [sectorPolar_norm (mul_nonneg hρ.le s.2.1),hrs]
        exact hr.2.trans hρC
      refine ⟨x,hxim,C.chart.injOn (C.source hxC) (C.source (hz.trans hρC)) ?_⟩
      change C.chart (f (flatLinkSectorDiskPoint Real.pi_pos.le le_rfl (ρ*s.1) _ t)) = C.chart z
      rw [hpolar,hrs]
      change sectorPolar r (flatLinkOrientedAngle forward cut t) = C.chart z
      rw [htθ,sectorPolar_eq_pointRadialSectorPoint]
      exact he.symm

end RepulsiveCoulomb
