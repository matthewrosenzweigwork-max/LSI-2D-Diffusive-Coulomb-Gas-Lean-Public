module

public import LeanResearch.RepulsiveCoulomb.PointTranslatedTopRowInterior
public import LeanResearch.RepulsiveCoulomb.PointInteriorZeroExponentFlatChart

@[expose] public section

/-! SOURCE-ONLY ASSEMBLY. Derive every positive-height/positive-length chart
of an actual finite translated stage from the original signed geometry.
Interior membership uses the newly assembled retained parallel-return proof;
zero ambient exponent then follows from the ONE whole-ray clearance. -/
noncomputable section
open Set Metric
namespace RepulsiveCoulomb

theorem point_translated_stage_positive_flatChart
    {m N : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (HP : ℂ ≃ₜ ℂ) (hP : P = HP ⁻¹' planarClosedUpperHalfplane)
    (pieces : Fin N → PointClosedBoundaryGeodesicPiece a y)
    (hpieces : frontier P = ⋃ i, range (pieces i).curve)
    {ν α : ℂ →₀ ℝ} (hbudget : PointSignedBudgetInvariant ν α)
    (hν : ∀ p ∈ frontier P, ∃ C : PointRetainedConeNeighborhood a y P p,
      ν p = Real.pi - (1 + coalescedPointExponent a y p / 2) * (C.hi - C.lo))
    (hcurv : ∀ p ∈ interior P, coalescedPointExponent a y p ≠ 0 → p ∈ pointSignedMarked ν α)
    {stripAngle R s ell delta : ℝ} (stripAngle_pos : 0 < stripAngle) (stripAngle_lt_pi : stripAngle < Real.pi)
    (hR : 0 < R) (hs : 0 < s) (hsell : s < ell) (hsdelta : s ≤ delta)
    (ρ : NNReal → P)
    (hρ : @Isometry NNReal P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace ρ)
    (hρfront : ∀ t, (ρ t).1 ∈ frontier P)
    (hcorner : ν (ρ 0).1 = Real.pi - stripAngle)
    (hclear : ∀ z ∈ (↑(pointSignedMarked ν α) : Set ℂ) \ {(ρ 0).1}, ∀ r : NNReal,
      delta < (pointSmoothConformalEDist a y z (ρ r).1).toReal)
    (edge : Icc (0 : ℝ) ell → P)
    (hedge : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace edge)
    (hedgefront : ∀ u, (edge u).1 ∈ frontier P)
    (f : flatShearedRectangle (conePhase stripAngle) R s → P)
    (hf : @Isometry _ P inferInstance (pointRegionMetricSpace ha y P).toPseudoEMetricSpace f)
    (hbottom : ∀ r : Icc (0 : ℝ) R, f (shearedBottomPoint hs.le r) = ρ ⟨r.1, r.2.1⟩)
    (hold : ∀ u : Icc (0 : ℝ) s,
      f (shearedCompactEdgePoint hR.le u) = edge ⟨u.1, u.2.1, u.2.2.trans hsell.le⟩)
    (r : Icc (0 : ℝ) R) (hr : 0 < r.1) (u : Icc (0 : ℝ) s) (hu : 0 < u.1) :
    let q : flatShearedRectangle (conePhase stripAngle) R s :=
      ⟨flatShearedPoint (conePhase stripAngle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩
    (f q).1 ∈ interior P ∧ (f q).1 ∉ pointSignedMarked ν α ∧
      Nonempty (@MetricFlatDiskChart P (pointRegionMetricSpace ha y P) (f q)) := by
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let q : flatShearedRectangle (conePhase stripAngle) R s :=
    ⟨flatShearedPoint (conePhase stripAngle) r.1 u.1, r.1, r.2, u.1, u.2, rfl⟩
  let incl : flatShearedRectangle (conePhase stripAngle) R u.1 → flatShearedRectangle (conePhase stripAngle) R s :=
    Set.inclusion (flatShearedRectangle_mono le_rfl u.2.2)
  have hincl : Isometry incl := fun _ _ ↦ rfl
  let g := f ∘ incl
  have hg : Isometry g := hf.comp hincl
  have hubottom (t : Icc (0 : ℝ) R) : g (shearedBottomPoint hu.le t) = ρ ⟨t.1, t.2.1⟩ := hbottom t
  have huell : u.1 < ell := u.2.2.trans_lt hsell
  have huold (t : Icc (0 : ℝ) u.1) :
      g (shearedCompactEdgePoint hR.le t) = edge ⟨t.1, t.2.1, t.2.2.trans huell.le⟩ :=
    hold ⟨t.1, t.2.1, t.2.2.trans u.2.2⟩
  have hpint : (f q).1 ∈ interior P := point_translated_top_row_mem_interior
    ha y HP hP pieces hpieces hbudget hν stripAngle_pos stripAngle_lt_pi hR hu huell (u.2.2.trans hsdelta)
    ρ hρ hρfront hcorner hclear edge hedge hedgefront g hg hubottom huold r hr
  have hlocal : PointLocallyDistancePreserving a y (fun z ↦ (f z).1) := by
    intro z
    exact ⟨univ, isOpen_univ, mem_univ _, fun x _ w _ ↦ hf.dist_eq x w⟩
  have havoid : (f q).1 ∉ (↑(pointSignedMarked ν α) : Set ℂ) \ {(ρ 0).1} := by
    apply pointShearedRectangle_unmarked ha y (conePhase_norm stripAngle) hs.le hsdelta
      (fun t ↦ (ρ t).1) hclear (fun z ↦ (f z).1) hlocal
    intro t ht
    exact congrArg Subtype.val (hbottom ⟨t, ht⟩)
  have hneq : (f q).1 ≠ (ρ 0).1 := by
    intro he
    have hno := metric_translated_stage_avoids_bottom stripAngle_pos stripAngle_lt_pi hR hs.le ρ hρ f hf hbottom r u hu
    exact hno ⟨0, Subtype.ext he.symm⟩
  have hoff : (f q).1 ∉ pointSignedMarked ν α := fun hm ↦ havoid ⟨hm, hneq⟩
  have hzero : coalescedPointExponent a y (f q).1 = 0 := by
    by_contra hn
    exact hoff (hcurv _ hpint hn)
  exact ⟨hpint, hoff, exists_pointInterior_zeroExponent_flatDiskChart ha y hpint hzero⟩

end RepulsiveCoulomb
