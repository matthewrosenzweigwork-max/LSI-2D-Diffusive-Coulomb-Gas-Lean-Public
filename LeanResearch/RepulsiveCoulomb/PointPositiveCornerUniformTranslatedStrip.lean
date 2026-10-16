module

public import LeanResearch.RepulsiveCoulomb.PointOriginalCornerUniformTranslatedStrip
public import LeanResearch.RepulsiveCoulomb.PointRetainedUpperBoundaryEdge

@[expose] public section

/-! SOURCE-ONLY STRONGER ORIGINAL-INPUT ENDPOINT. The genuine corner itself
constructs the adjacent minimizing boundary edge, both local trace identities,
and then the positive uniform unbounded translated strip. No adjacent edge,
corner normalization, initial map, development family or continuation premise
is supplied. This is still the INITIAL uniform strip, not maximal contact.
-/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb

theorem point_exists_positive_corner_uniform_translated_strip
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
    (hwidth : C.flatPhysicalWidth<Real.pi) :
    ∃ s : ℝ,∃ hs : 0<s,
      ∃ F : flatShearedStrip (conePhase C.flatPhysicalWidth) s→P,
        (∀ x z,(pointSmoothConformalEDist a y (F x).1 (F z).1).toReal=dist x z) ∧
        (∀ r : NNReal,F (translatedStripBottom hs.le r)=ρ r) ∧
        (∀ z,(F z).1∉(↑(pointSignedMarked ν α):Set ℂ)\{(ρ 0).1}) ∧
        (∀ r : NNReal,0<r→∀ u : Icc (0:ℝ) s,0<u.1→
          (F ⟨flatShearedPoint (conePhase C.flatPhysicalWidth) r.1 u.1,r.1,r.2,u.1,u.2,rfl⟩).1∈interior P) ∧
        IsClosedEmbedding (fun z↦(F z).1) ∧ IsProperMap (fun z↦(F z).1) ∧
        range (fun z↦(F z).1)∩frontier P=
          range (fun r↦(F (translatedStripBottom hs.le r)).1) ∪
          range (fun u : Icc (0:ℝ) s↦(F (translatedStripEdge u)).1) := by
  obtain ⟨E,hE0,hEP,hEfront,hintersection⟩:=
    exists_positive_corner_actual_adjacent_edge ha y hclosed ρ hρ hfront C hadm hwidth
  obtain ⟨s,hs,hsedge,F,hd,hb,he,hmarks,hint,hFc,hFp,hcontact⟩:=
    point_exists_original_corner_uniform_translated_strip ha y HP hP hclosed pieces hpieces
      hbudget hν hcurv ρ hρ hfront hclean C hadm hwidth E hE0 hEP hEfront hintersection
  have hbfun:(fun r:NNReal↦(F (translatedStripBottom hs.le r)).1)=(fun r↦(ρ r).1):=
    funext (fun r↦congrArg Subtype.val (hb r))
  have hefun:(fun u:Icc (0:ℝ) s↦(F (translatedStripEdge u)).1)=
      (fun u:Icc (0:ℝ) s↦pointEdgeArclength ha y E ⟨u.1,u.2.1,u.2.2.trans hsedge.le⟩):=funext he
  rw [← hbfun,← hefun] at hcontact
  exact ⟨s,hs,F,hd,hb,hmarks,hint,hFc,hFp,hcontact⟩

end RepulsiveCoulomb
