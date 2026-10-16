import LeanResearch.RepulsiveCoulomb.PointRetainedUpperBoundaryEdge
import LeanResearch.RepulsiveCoulomb.MetricHalfDiskBoundaryAlignment

/-! SOURCE-ONLY, UNCOMPILED. A true symmetric minimizing interval through a
retained-flat boundary point remains on the old frontier locally. The boundary
assertion is proved from actual raw endpoint coordinates, not assumed from a
metric halfdisk abstraction. This supplies no-mark limiting-top regularization.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem PointRetainedConeNeighborhood.upper_radial_mem_frontier_le_pi
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    (hshort : C.hi-C.lo≤Real.pi)
    {r : ℝ} (hr:0<r) (hrR:r<C.radius)
    (hzR:(pointSmoothConformalEDist a y z p).toReal≤C.radius)
    (hzP:z∈P) (hchart:C.chart z=pointRadialSectorPoint r C.hi) : z∈frontier P := by
  let w:ℝ→ℂ:=fun t↦pointRadialSectorPoint r (C.hi+t)
  let ψ:ℝ→ℂ:=fun t↦C.chart.symm (w t)
  have hnorm(t:ℝ):‖w t‖=r:=pointRadialSectorPoint_norm hr.le (C.hi+t)
  have htarget:w 0∈C.chart.target:=(C.retainedWidth_inverse ((hnorm 0).trans_le hrR.le)).1
  have hwcont:Continuous w:=by unfold w pointRadialSectorPoint;fun_prop
  have hψcont:ContinuousAt ψ 0:=
    (C.chart.continuousAt_symm htarget).comp hwcont.continuousAt
  have hψ0:ψ 0=z:=by
    change C.chart.symm (pointRadialSectorPoint r (C.hi+0))=z
    rw [add_zero,← hchart]
    exact C.chart.left_inv (C.source hzR)
  have hout:ψ '' Ioo (0:ℝ) Real.pi⊆Pᶜ:=by
    rintro x ⟨t,ht,rfl⟩ hxP
    obtain ⟨_,hcoord,hmetric⟩:=C.retainedWidth_inverse ((hnorm t).trans_le hrR.le)
    have hraw:w t∈pointClosedRadialInterval C.radius C.lo C.hi:=by
      have h:ψ t∈P:=hxP
      apply (C.retained (ψ t) (hmetric.trans_le ((hnorm t).trans_le hrR.le))).mp at h
      rwa [hcoord] at h
    have hrot:= (sectorReturn_rotate_closed_interval_iff C.radius C.lo C.hi C.hi (w t)).mpr hraw
    rw [show w t=pointRadialSectorPoint r (C.hi+t) from rfl,
      sectorReturn_rotate_radial_point,show C.hi+t-C.hi=t by ring,sub_self] at hrot
    obtain ⟨s,hs,θ,hθ,he⟩:=hrot
    have hθsin:Real.sin θ≤0:=Real.sin_nonpos_of_nonpos_of_neg_pi_le hθ.2 (by linarith [hθ.1])
    have hnonpos:(pointRadialSectorPoint s θ).im≤0:=by
      rw [← sectorPolar_eq_pointRadialSectorPoint,sectorPolar_im]
      exact mul_nonpos_of_nonneg_of_nonpos hs.1 hθsin
    have hpos:0<(pointRadialSectorPoint r t).im:=by
      rw [← sectorPolar_eq_pointRadialSectorPoint,sectorPolar_im]
      exact mul_pos hr (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)
    have hnonpos' : (pointRadialSectorPoint r t).im≤0 := by
      rw [he]
      exact hnonpos
    exact (not_lt_of_ge hnonpos') hpos
  have h0closure:(0:ℝ)∈closure (Ioo (0:ℝ) Real.pi):=by
    rw [closure_Ioo Real.pi_pos.ne]
    exact ⟨le_rfl,Real.pi_pos.le⟩
  have hzout:z∈closure Pᶜ:=by
    rw [← hψ0]
    exact closure_mono hout (hψcont.continuousWithinAt.mem_closure_image h0closure)
  exact ⟨subset_closure hzP,by simpa only [closure_compl, mem_compl_iff] using hzout⟩

theorem PointRetainedConeNeighborhood.lower_radial_mem_frontier_le_pi
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hshort : C.hi-C.lo≤Real.pi)
    {r : ℝ} (hr : 0<r) (hrR : r<C.radius)
    (hzR : (pointSmoothConformalEDist a y z p).toReal≤C.radius)
    (hzP : z∈P) (hchart : C.chart z=pointRadialSectorPoint r C.lo) : z∈frontier P := by
  obtain ⟨D,hR,_,hcoord,hlo,hhi,_,_⟩ := C.exists_reflect
  apply D.upper_radial_mem_frontier_le_pi
  · rw [hlo,hhi]
    linarith
  · exact hr
  · rwa [hR]
  · rwa [hR]
  · exact hzP
  · rw [hcoord,hchart,pointRadialSectorPoint_conj,hhi]

theorem PointRetainedConeNeighborhood.flatInverse_real_mem_frontier
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p : ℂ}
    (C : PointRetainedConeNeighborhood a y P p) (hp : p∈frontier P)
    (hwidth : C.flatPhysicalWidth=Real.pi) {t : ℝ} (ht : |t|<C.radius) :
    C.flatInverse (t:ℂ)∈frontier P := by
  have hraw : C.hi-C.lo≤Real.pi := by
    have he := coalescedPointExponent_nonneg a y p
    have hw := C.width_pos
    have hm := mul_nonneg he (sub_nonneg.mpr hw.le)
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth at hwidth
    nlinarith
  have hsrc : (t:ℂ)∈retainedFlatSectorDisk C.flatPhysicalWidth C.radius := by
    rw [hwidth,retainedFlatSectorDisk_pi]
    exact ⟨by simp,by simpa only [Complex.norm_real,Real.norm_eq_abs] using ht.le⟩
  obtain ⟨hzP,hzR⟩ := C.flatInverse_mem_and_radius hsrc
  have hmetric : (pointSmoothConformalEDist a y (C.flatInverse (t:ℂ)) p).toReal=|t| := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using C.flatInverse_center_distance hwidth.le hsrc
  rcases lt_trichotomy 0 t with hpos|hzero|hneg
  · have he : C.flatInverse (t:ℂ)=C.chart.symm (pointRadialSectorPoint t C.lo) := by
      have h := C.flatInverse_polar hpos.le (show (0:ℝ)∈Ioc (-Real.pi) Real.pi from
        ⟨neg_neg_of_pos Real.pi_pos,Real.pi_pos.le⟩)
      have hpolar : sectorPolar t 0=(t:ℂ) := by simp [sectorPolar,conePhase]
      simpa only [hpolar,mul_zero,add_zero] using h
    have hc : C.chart (C.flatInverse (t:ℂ))=pointRadialSectorPoint t C.lo := by
      rw [he]
      exact (C.retainedWidth_inverse ((pointRadialSectorPoint_norm hpos.le C.lo).trans_le
        ((abs_of_pos hpos ▸ ht.le)))).2.1
    exact C.lower_radial_mem_frontier_le_pi hraw hpos (abs_of_pos hpos ▸ ht) hzR hzP hc
  · rw [← hzero,Complex.ofReal_zero,C.flatInverse_zero]
    exact hp
  · have hpos : 0 < -t := neg_pos.mpr hneg
    have hphase : sectorPolar (-t) Real.pi=(t:ℂ) := by
      apply Complex.ext <;> simp [sectorPolar_re,sectorPolar_im,Real.cos_pi,Real.sin_pi]
    have hA : coalescedPointExponent a y p/2+1≠0 := by
      have he := coalescedPointExponent_nonneg a y p
      linarith
    have hangle : C.lo+(coalescedPointExponent a y p/2+1)⁻¹*Real.pi=C.hi := by
      rw [← hwidth]
      unfold PointRetainedConeNeighborhood.flatPhysicalWidth
      rw [← mul_assoc,inv_mul_cancel₀ hA,one_mul]
      ring
    have he : C.flatInverse (t:ℂ)=C.chart.symm (pointRadialSectorPoint (-t) C.hi) := by
      rw [← hphase,C.flatInverse_polar hpos.le
        (show Real.pi∈Ioc (-Real.pi) Real.pi from ⟨by linarith [Real.pi_pos],le_rfl⟩),hangle]
    have hnorm : ‖pointRadialSectorPoint (-t) C.hi‖≤C.radius := by
      rw [pointRadialSectorPoint_norm hpos.le]
      simpa only [abs_of_neg hneg] using ht.le
    have hc : C.chart (C.flatInverse (t:ℂ))=pointRadialSectorPoint (-t) C.hi := by
      rw [he]
      exact (C.retainedWidth_inverse hnorm).2.1
    exact C.upper_radial_mem_frontier_le_pi hraw hpos
      (by simpa only [abs_of_neg hneg] using ht) hzR hzP hc

/-- An actual isometric two-sided interval through a retained-flat boundary
point has actual old-frontier image. Its Euclidean diameter coordinate follows
from the midpoint metric identity and the retained upper-side condition. -/
theorem pointRetainedFlat_symmetric_interval_frontier
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} {p : P} (hp : p.1∈frontier P)
    (C : PointRetainedConeNeighborhood a y P p.1) (hwidth : C.flatPhysicalWidth=Real.pi)
    {L : ℝ} (hL : 0<L) (hLC : L<C.radius)
    (ρ : Icc (-L) L→P)
    (hρ : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (hzero : ρ (complexSymmetricIntervalZero hL)=p) :
    ∀ t, (ρ t).1∈frontier P := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let H := C.flatHalfDiskChart ha y p.2 hwidth
  have hball (t : Icc (-L) L) : ρ t∈ball p C.radius := by
    change dist (ρ t) p<C.radius
    calc
      dist (ρ t) p = dist (ρ t) (ρ (complexSymmetricIntervalZero hL)) :=
        congrArg (dist (ρ t)) hzero.symm
      _ = dist t (complexSymmetricIntervalZero hL) := hρ.dist_eq _ _
      _ = |t.1| := by
        change |t.1 - 0| = |t.1|
        rw [sub_zero]
      _ < C.radius := (abs_le.mpr t.2).trans_lt hLC
  let σ : Icc (-L) L→ℂ := fun t ↦ (H.fromEuclidean.symm ⟨ρ t,hball t⟩).1
  have hσ : Isometry σ := by
    apply Isometry.of_dist_eq
    intro t u
    exact (H.fromEuclidean.symm.isometry.dist_eq _ _).trans (hρ.dist_eq t u)
  have hσ0 : σ (complexSymmetricIntervalZero hL)=0 := by
    have he : (⟨ρ (complexSymmetricIntervalZero hL),hball _⟩ : ball p C.radius)=
        H.fromEuclidean (flatUpperDiskZero C.radius_pos) := by
      apply Subtype.ext
      exact hzero.trans H.center.symm
    have he' := (congrArg H.fromEuclidean.symm he).trans
      (H.fromEuclidean.symm_apply_apply (flatUpperDiskZero C.radius_pos))
    exact congrArg (fun z : flatUpperDisk C.radius ↦ z.1) he'
  obtain ⟨ε,hε,hcoord⟩ := complex_upper_interval_isometry_eq_signed_real hL σ hσ hσ0
    (fun t ↦ (H.fromEuclidean.symm ⟨ρ t,hball t⟩).2.2)
  intro t
  have hflat : C.flatInverse (σ t)=(ρ t).1 := by
    have he := congrArg (fun z : ball p C.radius ↦ z.1.1)
      (H.fromEuclidean.apply_symm_apply ⟨ρ t,hball t⟩)
    exact he
  have hnorm : |ε*t.1|<C.radius := by
    rcases hε with rfl|rfl <;>
      simpa only [one_mul,neg_one_mul,abs_neg] using (abs_le.mpr t.2).trans_lt hLC
  rw [← hflat,hcoord t]
  exact C.flatInverse_real_mem_frontier hp hwidth hnorm

end RepulsiveCoulomb
