import LeanResearch.RepulsiveCoulomb.PointRetainedConeReflection
import LeanResearch.RepulsiveCoulomb.PointRetainedFrontierEndpoint
import Mathlib.Topology.Order.DenselyOrdered

/-! SOURCE-ONLY MAXIMAL-CONTINUATION PRODUCER. Construct an actual adjacent
minimizing old-boundary edge directly from the genuine positive corner. The
upper endpoint is proved to be frontier by nearby OUTSIDE radial points in the
actual ambient chart; this converse is not inferred from the one-way frontier
endpoint theorem. The edge is disjoint from the whole escaping ray except at
the corner, by distances and the literal two distinct chart endpoints.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

/-- The upper endpoint of a proper short raw retained interval is genuinely
on the old frontier. Nearby outside angles prove noninteriority. -/
theorem PointRetainedConeNeighborhood.upper_radial_mem_frontier
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {p z : ℂ}
    (C : PointRetainedConeNeighborhood a y P p)
    (hshort : C.hi-C.lo<Real.pi)
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
  exact ⟨subset_closure hzP,by simpa only [closure_compl,mem_compl_iff] using hzout⟩

theorem exists_positive_corner_actual_adjacent_edge
    {m : ℕ} {a : Fin m → ℝ} (ha:∀j,0≤a j) (y:Fin m→ℂ)
    {P:Set ℂ} (hP:IsClosed P)
    (ρ:NNReal→P)
    (hρ:@Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (hfront:∀t,(ρ t).1∈frontier P)
    (C:PointRetainedConeNeighborhood a y P (ρ 0).1) (hadm:C.Admissible)
    (hwidth:C.flatPhysicalWidth<Real.pi) :
    ∃E:PointGeodesicTreeEdge a y,E.start=(ρ 0).1 ∧
      (∀t,E.curve t∈P) ∧ (∀t,E.curve t∈frontier P) ∧
      range E.curve ∩ range (fun t↦(ρ t).1)⊆{(ρ 0).1} := by
  let ray:ℝ→ℂ:=fun t↦(ρ t.toNNReal).1
  have hray0:ray 0=(ρ 0).1:=by simp [ray]
  have hrayd:∀s∈Ici (0:ℝ),∀t∈Ici (0:ℝ),
      (pointSmoothConformalEDist a y (ray s) (ray t)).toReal=dist s t:=by
    intro s hs t ht
    have h := @Isometry.dist_eq NNReal P _
      (pointRegionMetricSpace ha y P).toPseudoMetricSpace ρ hρ s.toNNReal t.toNNReal
    change (pointSmoothConformalEDist a y (ray s) (ray t)).toReal =
      dist s.toNNReal t.toNNReal at h
    rw [NNReal.dist_eq, Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht] at h
    simpa only [Real.dist_eq] using h
  obtain ⟨K,hKadm,hKwidth,T,hT,hTK,hKlower⟩:=
    exists_actual_clean_lower_retained_chart C hadm hP ray hray0 hrayd (fun _ _↦hfront _)
  have hKπ:K.flatPhysicalWidth<Real.pi:=hKwidth.trans_lt hwidth
  have hraw:K.hi-K.lo<Real.pi:=by
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth at hKπ
    have hw:=sub_pos.mpr K.width_pos
    have ha0:=coalescedPointExponent_nonneg a y (ρ 0).1
    nlinarith [mul_nonneg ha0 hw.le]
  let L:=min T K.radius/2
  have hL:0<L:=half_pos (lt_min hT K.radius_pos)
  have hLT:L<T:=(half_lt_self (lt_min hT K.radius_pos)).trans_le (min_le_left _ _)
  have hLK:L<K.radius:=(half_lt_self (lt_min hT K.radius_pos)).trans_le (min_le_right _ _)
  obtain ⟨E,hE0,hEL,hEP,hpolar⟩:=K.exists_raw_radial_seed_edge ha y hL hLK.le
    (show K.hi∈Icc K.lo K.hi from ⟨K.width_pos.le,le_rfl⟩)
  have hdist(t:unitInterval):(pointSmoothConformalEDist a y (E.curve t) (ρ 0).1).toReal=t.1*L:=by
    have h:=E.geodesic t ⟨0, by norm_num⟩
    rw [E.curve_start] at h
    change (pointSmoothConformalEDist a y (E.curve t) E.start).toReal =
      |0 - t.1| * (pointSmoothConformalEDist a y E.start E.finish).toReal at h
    rw [hE0,zero_sub,abs_neg,abs_of_nonneg t.2.1,← hE0,hEL,hE0] at h
    exact h
  have hEf:∀t,E.curve t∈frontier P:=by
    intro t
    by_cases ht:t.1=0
    · have ht0:t=⟨0, by norm_num⟩:=Subtype.ext ht
      rw [ht0,E.curve_start,hE0]
      exact hfront 0
    · have htpos:0<t.1:=lt_of_le_of_ne t.2.1 (Ne.symm ht)
      have hrpos:0<t.1*L:=mul_pos htpos hL
      have hrK:t.1*L<K.radius:=(mul_le_of_le_one_left hL.le t.2.2).trans_lt hLK
      exact K.upper_radial_mem_frontier hraw hrpos hrK
        ((hdist t).trans_le hrK.le) (hEP t) (hpolar t)
  refine ⟨E,hE0,hEP,hEf,?_⟩
  rintro z ⟨⟨t,htz⟩,⟨u,huz⟩⟩
  by_cases ht:t.1=0
  · have ht0:t=⟨0, by norm_num⟩:=Subtype.ext ht
    apply mem_singleton_iff.mpr
    rw [← htz,ht0,E.curve_start,hE0]
  · have htpos:0<t.1:=lt_of_le_of_ne t.2.1 (Ne.symm ht)
    have he:E.curve t=(ρ u).1:=htz.trans huz.symm
    have hru:(pointSmoothConformalEDist a y (ρ u).1 (ρ 0).1).toReal=u.1:=by
      have h := @Isometry.dist_eq NNReal P _
        (pointRegionMetricSpace ha y P).toPseudoMetricSpace ρ hρ u 0
      change (pointSmoothConformalEDist a y (ρ u).1 (ρ 0).1).toReal = dist u 0 at h
      rw [NNReal.dist_eq,NNReal.coe_zero,sub_zero] at h
      exact h.trans (abs_of_nonneg (show (0 : ℝ) ≤ (u : ℝ) from u.2))
    have hu:u.1=t.1*L:=by rw [← hru,← he,hdist]
    have hupos:0<u.1:=hu.symm ▸ mul_pos htpos hL
    have huT:u.1≤T:=hu.symm ▸ (mul_le_of_le_one_left hL.le t.2.2).trans hLT.le
    have hucoord:K.chart (ρ u).1=pointRadialSectorPoint u.1 K.lo:=by
      have huNN : (u.1).toNNReal = u := by
        apply Subtype.ext
        exact Real.coe_toNNReal _ u.2
      have h := hKlower u.1 ⟨u.2,huT⟩
      change K.chart (ρ ((u.1).toNNReal)).1 = pointRadialSectorPoint u.1 K.lo at h
      rwa [huNN] at h
    have hsame:pointRadialSectorPoint u.1 K.hi=pointRadialSectorPoint u.1 K.lo:=by
      rw [hu,← hpolar t,he,← hu]
      exact hucoord
    have hrot:=congrArg (fun w:ℂ↦conePhase (-K.lo)*w) hsame
    rw [sectorReturn_rotate_radial_point,sectorReturn_rotate_radial_point,sub_self] at hrot
    have him:=congrArg Complex.im hrot
    simp only [← sectorPolar_eq_pointRadialSectorPoint,sectorPolar_im,Real.sin_zero,mul_zero] at him
    have hpos:=mul_pos hupos (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr K.width_pos) hraw)
    exact False.elim (hpos.ne' him)

end RepulsiveCoulomb
