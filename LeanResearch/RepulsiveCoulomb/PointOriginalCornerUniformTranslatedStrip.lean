import LeanResearch.RepulsiveCoulomb.PointActualUniformTranslatedStrip
import LeanResearch.RepulsiveCoulomb.PointTranslatedCornerGermAdapter

/-! SOURCE-ONLY ORIGINAL-GEOMETRY ENDPOINT. Actual initial positive uniform
translated strip from a genuine (possibly unoriented) positive retained corner,
its actual clean escaping minimizing boundary ray, and its actual adjacent
minimizing boundary edge. BOTH corner germs are constructed. No chart-trace,
finite seed, strip, stage, direction, continuation, or compatible-family premise
is present. The separate maximal-width/marked-contact theorem is still pending.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem point_exists_original_corner_uniform_translated_strip
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j,0≤a j) (y : Fin m → ℂ)
    {P : Set ℂ} (HP : ℂ ≃ₜ ℂ) (hP : P=HP ⁻¹' planarClosedUpperHalfplane) (hclosed : IsClosed P)
    (pieces : Fin N→PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P=⋃ i,range (pieces i).curve)
    {ν α : ℂ→₀ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hν : ∀ p∈frontier P,∃ K : PointRetainedConeNeighborhood a y P p,
      ν p=Real.pi-(1+coalescedPointExponent a y p/2)*(K.hi-K.lo))
    (hcurv : ∀ p∈interior P,coalescedPointExponent a y p≠0→p∈pointSignedMarked ν α)
    (ρ : NNReal→P)
    (hρ : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (hfront : ∀ t,(ρ t).1∈frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α):Set ℂ)\{(ρ 0).1}) (range (fun t↦(ρ t).1)))
    (C : PointRetainedConeNeighborhood a y P (ρ 0).1) (hadm : C.Admissible)
    (hwidth : C.flatPhysicalWidth<Real.pi)
    (E : PointGeodesicTreeEdge a y) (hE0 : E.start=(ρ 0).1)
    (hEP : ∀ t,E.curve t∈P) (hEfront : ∀ t,E.curve t∈frontier P)
    (hintersection : range E.curve ∩ range (fun t↦(ρ t).1)⊆{(ρ 0).1}) :
    ∃ s : ℝ,∃ hs : 0<s,∃ hsedge : s<pointActualEdgeLength E,
      ∃ F : flatShearedStrip (conePhase C.flatPhysicalWidth) s→P,
        (∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z) ∧
        (∀ r : NNReal,F (translatedStripBottom hs.le r)=ρ r) ∧
        (∀ u : Icc (0:ℝ) s,(F (translatedStripEdge u)).1=
          pointEdgeArclength ha y E ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩) ∧
        (∀ z,(F z).1∉(↑(pointSignedMarked ν α):Set ℂ)\{(ρ 0).1}) ∧
        (∀ r : NNReal,0<r→∀ u : Icc (0:ℝ) s,0<u.1→
          (F ⟨flatShearedPoint (conePhase C.flatPhysicalWidth) r.1 u.1,r.1,r.2,u.1,u.2,rfl⟩).1∈interior P) ∧
        IsClosedEmbedding (fun z↦(F z).1) ∧ IsProperMap (fun z↦(F z).1) ∧
        range (fun z↦(F z).1)∩frontier P=range (fun r↦(ρ r).1) ∪
          range (fun u : Icc (0:ℝ) s↦pointEdgeArclength ha y E ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩) := by
  obtain ⟨K,hKadm,hKwidth,edge,hedge,hedgeval,hedgefront,T,hT,hTE,hlower,hupper⟩ :=
    exists_actual_translated_corner_germs ha y hclosed ρ hρ hfront C hadm hwidth E hE0 hEP hEfront hintersection
  obtain ⟨J,hJν⟩ := hν (ρ 0).1 (hfront 0)
  have hKJ := K.physical_width_eq J
  have hcorner : ν (ρ 0).1=Real.pi-K.flatPhysicalWidth := by
    unfold PointRetainedConeNeighborhood.flatPhysicalWidth
    nlinarith [hJν]
  let D : PointTranslatedOriginalData a y ha P :=
    { halfplane:=HP
      halfplane_eq:=hP
      closed:=hclosed
      pieceCount:=N
      pieces:=pieces
      boundary_cover:=hpieces
      nu:=ν
      alpha:=α
      budget:=hbudget
      boundary_atom:=hν
      interior_support:=hcurv
      ray:=ρ
      ray_metric:=hρ
      ray_frontier:=hfront
      ray_clean:=hclean
      corner:=K
      corner_admissible:=hKadm
      corner_width_lt_pi:=hKwidth.trans_lt hwidth
      corner_atom:=hcorner
      edgeLength:=pointActualEdgeLength E
      edgeLength_pos:=pointActualEdgeLength_pos ha y E
      edge:=edge
      edge_metric:=hedge
      edge_frontier:=hedgefront
      germRadius:=T
      germRadius_pos:=hT
      germRadius_edge:=hTE
      lower_trace:=hlower
      upper_trace:=hupper }
  let Result (θ : ℝ) : Prop :=
    ∃ s : ℝ, ∃ hs : 0 < s, ∃ hsedge : s < (pointActualEdgeLength E),
      ∃ F : flatShearedStrip (conePhase θ) s → P,
        (∀ x z, (pointSmoothConformalEDist a y (F x).1 (F z).1).toReal = dist x z) ∧
        (∀ r : NNReal, F (translatedStripBottom hs.le r)=ρ r) ∧
        (∀ u : Icc (0 : ℝ) s,
          F (translatedStripEdge u)=edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩) ∧
        (∀ z, (F z).1 ∉ (↑(pointSignedMarked ν α) : Set ℂ) \ {(ρ 0).1}) ∧
        (∀ r : NNReal, 0<r → ∀ u : Icc (0 : ℝ) s, 0<u.1 →
          (F ⟨flatShearedPoint (conePhase θ) r.1 u.1,r.1,r.2,u.1,u.2,rfl⟩).1 ∈ interior P) ∧
        IsClosedEmbedding (fun z ↦ (F z).1) ∧ IsProperMap (fun z ↦ (F z).1) ∧
        range (fun z ↦ (F z).1) ∩ frontier P =
          range (fun r ↦ (ρ r).1) ∪
          range (fun u : Icc (0 : ℝ) s ↦ (edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩).1)
  have hresult : Result K.flatPhysicalWidth := D.exists_actual_uniform_translated_strip
  have hresult' : Result C.flatPhysicalWidth := Eq.mp (congrArg Result hKwidth) hresult
  obtain ⟨s,hs,hsedge,F,hd,hb,he,hmarked,hinside,hFc,hFp,hcontact⟩ := hresult'
  have he' (u : Icc (0:ℝ) s) : (F (translatedStripEdge u)).1=
      pointEdgeArclength ha y E ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩ :=
    (congrArg Subtype.val (he u)).trans (hedgeval _)
  have hedgefun : (fun u : Icc (0:ℝ) s↦(edge ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩).1)=
      (fun u : Icc (0:ℝ) s↦pointEdgeArclength ha y E ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩) :=
    funext (fun u↦hedgeval _)
  rw [hedgefun] at hcontact
  exact ⟨s,hs,hsedge,F,hd,hb,he',hmarked,hinside,hFc,hFp,hcontact⟩

end RepulsiveCoulomb
