module

public import LeanResearch.RepulsiveCoulomb.PointBoundaryEdgeArclength
public import LeanResearch.RepulsiveCoulomb.PointRetainedConeReflection
public import LeanResearch.RepulsiveCoulomb.PointTranslatedOriginalData

@[expose] public section

/-! SOURCE-ONLY AFTER THE UNIFORM-STRIP FREEZE. Derive BOTH local corner
traces from an arbitrary genuine admissible positive corner, the actual
outward minimizing boundary ray, and an actual adjacent minimizing boundary
edge meeting that ray only at the original corner. No endpoint orientation,
raw direction, chart trace, finite rectangle, or strip is an input.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem exists_actual_translated_corner_germs
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hP : IsClosed P)
    (ρ : NNReal → P)
    (hρ : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (hfront : ∀ t,(ρ t).1∈frontier P)
    (C : PointRetainedConeNeighborhood a y P (ρ 0).1) (hadm : C.Admissible)
    (hwidth : C.flatPhysicalWidth<Real.pi)
    (E : PointGeodesicTreeEdge a y) (hE0 : E.start=(ρ 0).1)
    (hEP : ∀ t,E.curve t∈P) (hEfront : ∀ t,E.curve t∈frontier P)
    (hintersection : range E.curve ∩ range (fun t↦(ρ t).1)⊆{(ρ 0).1}) :
    ∃ K : PointRetainedConeNeighborhood a y P (ρ 0).1,
      K.Admissible ∧ K.flatPhysicalWidth=C.flatPhysicalWidth ∧
      ∃ edge : Icc (0:ℝ) (pointActualEdgeLength E)→P,
        (@Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace edge) ∧
        (∀ t,(edge t).1=pointEdgeArclength ha y E t) ∧
        (∀ t,(edge t).1∈frontier P) ∧
        ∃ T : ℝ, 0<T ∧ T≤pointActualEdgeLength E ∧
          (∀ t : NNReal,t.1≤T→K.flatInverse (t:ℂ)=(ρ t).1) ∧
          ∀ t : Icc (0:ℝ) (pointActualEdgeLength E),t.1≤T→
            K.flatInverse (flatShearedPoint (conePhase K.flatPhysicalWidth) 0 t.1)=(edge t).1 := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let ray : ℝ→ℂ := fun t↦(ρ t.toNNReal).1
  have hray0 : ray 0=(ρ 0).1 := by simp [ray]
  have hrayd : ∀ s∈Ici (0:ℝ),∀ t∈Ici (0:ℝ),
      (pointSmoothConformalEDist a y (ray s) (ray t)).toReal=dist s t := by
    intro s hs t ht
    have h:=hρ.dist_eq s.toNNReal t.toNNReal
    exact h.trans (by
      rw [NNReal.dist_eq, Real.toNNReal_of_nonneg hs, Real.toNNReal_of_nonneg ht, Real.dist_eq]
      rfl)
  obtain ⟨K,hKadm,hKwidth,B,hB,hBK,hKlower⟩ :=
    exists_actual_clean_lower_retained_chart C hadm hP ray hray0 hrayd (fun _ _↦hfront _)
  have hKπ : K.flatPhysicalWidth<Real.pi := hKwidth.trans_lt hwidth
  obtain ⟨d,hd,hdK,hdlen,hEgerm⟩ := K.exists_edge_arclength_radial_germ ha y hKadm E hE0 hEP
  let φ := K.actualInitialRawAngle ha y hKadm E hE0 hEP
  have hφends : φ=K.lo ∨ φ=K.hi :=
    K.actualInitialRawAngle_frontier_endpoint ha y hKadm E hE0 hEP (fun t _↦hEfront t)
  have harclen (t : Icc (0:ℝ) (pointActualEdgeLength E)) :
      (pointSmoothConformalEDist a y (pointEdgeArclength ha y E t) (ρ 0).1).toReal=t.1 := by
    have h:=pointEdgeArclength_metric ha y E t ⟨0,le_rfl,(pointActualEdgeLength_pos ha y E).le⟩
    rw [pointEdgeArclength_zero,hE0] at h
    change (pointSmoothConformalEDist a y (pointEdgeArclength ha y E t) (ρ 0).1).toReal=dist t.1 (0:ℝ) at h
    simpa only [Real.dist_eq,sub_zero,abs_of_nonneg t.2.1] using h
  have hraylen (t : NNReal) : (pointSmoothConformalEDist a y (ρ t).1 (ρ 0).1).toReal=t.1 := by
    have h:=hρ.dist_eq t 0
    exact h.trans (by
      simp only [NNReal.dist_eq, NNReal.coe_zero, sub_zero]
      exact abs_of_nonneg t.2)
  have hφhi : φ=K.hi := by
    rcases hφends with hlo | hhi
    · let t:=min d B/2
      have ht:0<t:=half_pos (lt_min hd hB)
      have htd:t<d:=(half_lt_self (lt_min hd hB)).trans_le (min_le_left _ _)
      have htB:t<B:=(half_lt_self (lt_min hd hB)).trans_le (min_le_right _ _)
      let te : Icc (0:ℝ) (pointActualEdgeLength E):=⟨t,ht.le,(htd.trans hdlen).le⟩
      let tr : NNReal:=⟨t,ht.le⟩
      have hecoord : K.chart (pointEdgeArclength ha y E te)=pointRadialSectorPoint t K.lo := by
        have h:=hEgerm te htd.le
        change K.chart (pointEdgeArclength ha y E te)=pointRadialSectorPoint t φ at h
        rwa [hlo] at h
      have hrcoord : K.chart (ρ tr).1=pointRadialSectorPoint t K.lo := by
        have hrt : ray t = (ρ tr).1 :=
          congrArg (fun z : NNReal ↦ (ρ z).1) (Real.toNNReal_of_nonneg ht.le)
        exact (congrArg K.chart hrt).symm.trans (hKlower t ⟨ht.le,htB.le⟩)
      have heq : pointEdgeArclength ha y E te=(ρ tr).1 := K.chart.injOn
        (K.source ((harclen te).trans_le (htd.le.trans hdK.le)))
        (K.source ((hraylen tr).trans_le (htB.le.trans hBK.le)))
        (hecoord.trans hrcoord.symm)
      have hp : pointEdgeArclength ha y E te=(ρ 0).1 := mem_singleton_iff.mp
        (hintersection ⟨pointEdgeArclength_mem ha y E te,⟨tr,heq.symm⟩⟩)
      have hh:=harclen te
      rw [hp,pointSmoothConformalEDist_self,ENNReal.toReal_zero] at hh
      exact False.elim (ht.ne' hh.symm)
    · exact hhi
  let edge : Icc (0:ℝ) (pointActualEdgeLength E)→P := fun t↦
    ⟨pointEdgeArclength ha y E t,hEP _⟩
  have hedge : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace edge := by
    apply @Isometry.of_dist_eq _ P _ (pointRegionMetricSpace ha y P).toPseudoMetricSpace
    exact pointEdgeArclength_metric ha y E
  let T:=min B d
  have hT:0<T:=lt_min hB hd
  have hTB:T≤B:=min_le_left _ _
  have hTd:T≤d:=min_le_right _ _
  have hTlen:T≤pointActualEdgeLength E:=hTd.trans hdlen.le
  have hlower (t : NNReal) (ht:t.1≤T) : K.flatInverse (t:ℂ)=(ρ t).1 := by
    have hpolar:sectorPolar t.1 0=(t:ℂ):=by simp [sectorPolar,conePhase]
    rw [← hpolar,K.flatInverse_polar t.2
      (show (0:ℝ)∈Ioc (-Real.pi) Real.pi from ⟨neg_neg_of_pos Real.pi_pos,Real.pi_pos.le⟩)]
    simp only [mul_zero,add_zero]
    have hcoord:K.chart (ρ t).1=pointRadialSectorPoint t.1 K.lo:=by
      have htNN : (t : ℝ).toNNReal = t := by simp
      have hrt : ray t.1 = (ρ t).1 := congrArg (fun z : NNReal ↦ (ρ z).1) htNN
      exact (congrArg K.chart hrt).symm.trans (hKlower t.1 ⟨t.2,ht.trans hTB⟩)
    rw [← hcoord]
    exact K.chart.left_inv (K.source ((hraylen t).trans_le ((ht.trans hTB).trans hBK.le)))
  have hupper (t : Icc (0:ℝ) (pointActualEdgeLength E)) (ht:t.1≤T) :
      K.flatInverse (flatShearedPoint (conePhase K.flatPhysicalWidth) 0 t.1)=(edge t).1 := by
    have hpolar:flatShearedPoint (conePhase K.flatPhysicalWidth) 0 t.1=
        sectorPolar t.1 K.flatPhysicalWidth:=by simp [flatShearedPoint,sectorPolar]
    have hangle:K.lo+(coalescedPointExponent a y (ρ 0).1/2+1)⁻¹*K.flatPhysicalWidth=K.hi := by
      have hk:coalescedPointExponent a y (ρ 0).1/2+1≠0:=by linarith [coalescedPointExponent_nonneg a y (ρ 0).1]
      unfold PointRetainedConeNeighborhood.flatPhysicalWidth
      rw [← mul_assoc,inv_mul_cancel₀ hk,one_mul]
      ring
    rw [hpolar,K.flatInverse_polar t.2.1
      (show K.flatPhysicalWidth∈Ioc (-Real.pi) Real.pi from
        ⟨(neg_neg_of_pos Real.pi_pos).trans K.flatPhysicalWidth_pos,hKπ.le⟩),hangle]
    have hcoord:K.chart (edge t).1=pointRadialSectorPoint t.1 K.hi:=by
      have h:=hEgerm t (ht.trans hTd)
      change K.chart (edge t).1=pointRadialSectorPoint t.1 φ at h
      rwa [hφhi] at h
    rw [← hcoord]
    exact K.chart.left_inv (K.source ((harclen t).trans_le ((ht.trans hTd).trans hdK.le)))
  exact ⟨K,hKadm,hKwidth,edge,hedge,fun _↦rfl,fun _↦hEfront _,T,hT,hTlen,hlower,hupper⟩

end RepulsiveCoulomb
