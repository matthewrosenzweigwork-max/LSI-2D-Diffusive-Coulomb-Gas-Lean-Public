module

public import LeanResearch.RepulsiveCoulomb.PointFiniteSurgeryIncidentData
public import LeanResearch.RepulsiveCoulomb.PointOccupiedBranchProvenance
public import LeanResearch.RepulsiveCoulomb.PointRefinedComplementBranch

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. Actual finite incident chart construction:
choose paired source models, derive cyclic order and physical angle balance,
construct every occupied and complement branch, then paste both directions.
Neither the local homeomorphism nor its inverse laws are input assumptions. -/
noncomputable section
open Set Metric
open scoped BigOperators
namespace RepulsiveCoulomb

variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {p : ℂ} {c : ℝ}

/-- Exact pairwise estimates retained before closed-cover globalization. -/
def PointSurgeryBranchBounds
    {ι : Type*} {N : ℕ} {u : Fin (N + 1) → ℝ} {owner : ι ↪ Fin N} {k : ℝ}
    {C : PointFlatLinkConeDisk a y p} {R ε : ℝ}
    {Q : FiniteLinkComplementRefinement u owner k} {width : Fin N → ℝ}
    {x : Σ j : Fin N, Fin (Q.count j)}
    (c : ℝ) (B : PointRefinedAngularBranch C R ε Q width x) : Prop :=
  (∀ z ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x,
    ∀ w ∈ pointConeOpenBall C R ∩ pointRefinedSourceSet C R Q x,
      c * (pointSmoothConformalEDist a y z w).toReal ≤ dist (B.forward z) (B.forward w) ∧
        dist (B.forward z) (B.forward w) ≤ (pointSmoothConformalEDist a y z w).toReal) ∧
  (∀ z ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width x,
    ∀ w ∈ ball 0 ε ∩ pointRefinedTargetSet ε Q width x,
      c * (pointSmoothConformalEDist a y (B.inverse z) (B.inverse w)).toReal ≤ dist z w ∧
        dist z w ≤ (pointSmoothConformalEDist a y (B.inverse z) (B.inverse w)).toReal)

/-- A constructed incident chart, with its actual pieces and provenance.
All fields below are conclusions of the builder. In particular the exact
occupied formula is preserved for the later rigid-overlap theorem. -/
structure PointConstructedIncidentSurgeryChart
    (ha : ∀ j, 0 ≤ a j) (L : List (PointActualAllocatedSector a y)) (p : ℂ) (c : ℝ)
    (hc : 0 < c) (hc1 : c ≤ 1) where
  data : PointFiniteSurgeryIncidentData L p c
  initial : PointIncidentIndex L p
  ε : ℝ
  ε_pos : 0 < ε
  ε_le : ε ≤ c * data.radius
  N : ℕ
  N_pos : 0 < N
  u : Fin (N + 1) → ℝ
  u_mono : StrictMono u
  u_first : u 0 = 0
  u_last : u (Fin.last N) = 2 * Real.pi
  owner : PointIncidentIndex L p ↪ Fin N
  owner_ends : ∀ i, u (owner i).castSucc = normalizedIncidentLower (data.lo initial) (data.lo i) ∧
    u (owner i).succ = normalizedIncidentLower (data.lo initial) (data.lo i) +
      (data.paired i).old.angle / (coalescedPointExponent a y p / 2 + 1)
  width : Fin N → ℝ
  width_pos : ∀ j, 0 < width j
  width_total : (∑ j, width j) = 2 * Real.pi
  width_owned : ∀ i, width (owner i) = (data.paired i).new.angle
  width_complement : ∀ j, j ∉ range owner → width j =
    (coalescedPointExponent a y p / 2 + 1) * (u j.succ - u j.castSucc)
  refinement : FiniteLinkComplementRefinement u owner (coalescedPointExponent a y p / 2 + 1)
  branch : ∀ x : (Σ j : Fin N, Fin (refinement.count j)),
    PointRefinedAngularBranch (data.cone.rotate (-data.lo initial)) data.radius ε refinement width x
  bounds : ∀ x, PointSurgeryBranchBounds c (branch x)
  provenance : ∀ x,
    (∃ i : PointIncidentIndex L p, x.1 = owner i ∧
      (branch x).forward = (data.paired i).occupiedForward ha hc hc1
        (linkCumulativeWidth (finiteLinkWidthSequence width) (owner i).1) (data.forward i)) ∨
    (x.1 ∉ range owner ∧
      ∀ z ∈ pointConeOpenBall (data.cone.rotate (-data.lo initial)) data.radius ∩
          pointRefinedSourceSet (data.cone.rotate (-data.lo initial)) data.radius refinement x,
        ∀ w ∈ pointConeOpenBall (data.cone.rotate (-data.lo initial)) data.radius ∩
          pointRefinedSourceSet (data.cone.rotate (-data.lo initial)) data.radius refinement x,
          dist ((branch x).forward z) ((branch x).forward w) =
            (pointSmoothConformalEDist a y z w).toReal)
  chart : OpenPartialHomeomorph ℂ ℂ
  center_mem : p ∈ chart.source
  center : chart p = 0
  source_subset : chart.source ⊆ pointConeOpenBall (data.cone.rotate (-data.lo initial)) data.radius
  target : chart.target = ball 0 ε
  forward_formula : ∀ x z, z ∈ chart.source →
    z ∈ pointRefinedSourceSet (data.cone.rotate (-data.lo initial)) data.radius refinement x →
      chart z = (branch x).forward z
  inverse_formula : ∀ x z, z ∈ ball 0 ε → z ∈ pointRefinedTargetSet ε refinement width x →
    chart.symm z = (branch x).inverse z

/-- Actual incident-boundary chart with all local branch fields discharged.
The only premises are geometry of the finite allocation, its exact budget,
and the fact that this point is on selected boundaries rather than interiors. -/
theorem exists_pointConstructedIncidentSurgeryChart
    (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    (L : List (PointActualAllocatedSector a y)) (p : ℂ)
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hdis : L.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage))
    (hregular : ∀ S ∈ L, ∀ z : closedEuclideanSector S.beta,
      z.1 ∈ interior (closedEuclideanSector S.beta) → coalescedPointExponent a y (S.map z) = 0)
    (hbalance : (1-c) * pointActualAllocatedBudget L p = Real.pi * coalescedPointExponent a y p)
    (hseam : ∀ i : Fin L.length, p ∉ (L.get i).openImage)
    (i₀ : PointIncidentIndex L p) :
    Nonempty (PointConstructedIncidentSurgeryChart ha L p c hc hc1) := by
  classical
  obtain ⟨D⟩ := exists_pointFiniteSurgeryIncidentData ha y L p hc hc1 hseam
  let P := fun i : PointIncidentIndex L p ↦ (D.paired i).sourcePatch
  have hsep := pointAllocatedList_incident_closed_disjoint ha y L hdis hregular p
  obtain ⟨N, hN, u, hu, hu0, huT, owner, hends, width, hw, htotal, howned, hcomp,
      Q, hshort, hsum, hcover, htargetcover⟩ :=
    exists_point_constructed_refined_angles ha y L p hc hc1 hbalance P D.cone hsep
      D.radius_pos D.radius_old D.radius_cone D.lo D.forward D.polar i₀
  have hwidth (i : PointIncidentIndex L p) : width (owner i) = (D.paired i).new.angle :=
    (howned i).trans (D.paired i).new_angle.symm
  let ε := c * D.radius / 2
  have hε : 0 < ε := half_pos (mul_pos hc D.radius_pos)
  have hεcR : ε ≤ c * D.radius := (half_lt_self (mul_pos hc D.radius_pos)).le
  have hεR : ε ≤ D.radius := hεcR.trans (mul_le_of_le_one_left D.radius_pos.le hc1)
  let C := D.cone.rotate (-D.lo i₀)
  let σ := Σ j : Fin N, Fin (Q.count j)
  have hbranch : ∀ x : σ, ∃ B : PointRefinedAngularBranch C D.radius ε Q width x,
      PointSurgeryBranchBounds c B ∧
      ((∃ i : PointIncidentIndex L p, x.1 = owner i ∧
        B.forward = (D.paired i).occupiedForward ha hc hc1
          (linkCumulativeWidth (finiteLinkWidthSequence width) (owner i).1) (D.forward i)) ∨
       (x.1 ∉ range owner ∧
        ∀ z ∈ pointConeOpenBall C D.radius ∩ pointRefinedSourceSet C D.radius Q x,
          ∀ w ∈ pointConeOpenBall C D.radius ∩ pointRefinedSourceSet C D.radius Q x,
            dist (B.forward z) (B.forward w) = (pointSmoothConformalEDist a y z w).toReal)) := by
    rintro ⟨j, v⟩
    by_cases hj : j ∈ range owner
    · obtain ⟨i, rfl⟩ := hj
      obtain ⟨B, hformula, hf, hg⟩ :=
        (D.paired i).exists_ownedRefinedAngularBranch_with_formula ha hc hc1 D.cone
          D.radius_pos (D.radius_old i) (D.radius_new i) D.radius_cone hε hεcR
          (D.polar i) (D.lo i₀) Q width i v (hends i).1 (hends i).2 (hwidth i)
      exact ⟨B, ⟨hf, hg⟩, Or.inl ⟨i, rfl, hformula⟩⟩
    · obtain ⟨B, hf, hg⟩ := exists_pointRefinedComplementBranch ha y C D.radius_pos
        D.radius_cone hε hεR Q width ⟨j, v⟩ hj
      refine ⟨B, ⟨?_, ?_⟩, Or.inr ⟨hj, hf⟩⟩
      · intro z hz w hw
        rw [hf z hz w hw]
        exact ⟨mul_le_of_le_one_left ENNReal.toReal_nonneg hc1, le_rfl⟩
      · intro z hz w hw
        rw [hg z hz w hw]
        exact ⟨mul_le_of_le_one_left dist_nonneg hc1, le_rfl⟩
  choose B hbounds hprovenance using hbranch
  have hk : 0 < coalescedPointExponent a y p / 2 + 1 := by
    linarith [coalescedPointExponent_nonneg a y p]
  obtain ⟨e, hep, he0, hes, het, hef, heg⟩ :=
    exists_openChart_of_refined_angular_branches C D.radius_pos hε hN hu hu0 huT
      Q hk width hw hcomp htotal B
  exact ⟨{
    data := D, initial := i₀, ε := ε, ε_pos := hε, ε_le := hεcR,
    N := N, N_pos := hN, u := u, u_mono := hu, u_first := hu0, u_last := huT,
    owner := owner, owner_ends := hends, width := width, width_pos := hw,
    width_total := htotal, width_owned := hwidth, width_complement := hcomp,
    refinement := Q, branch := B, bounds := hbounds, provenance := hprovenance,
    chart := e, center_mem := hep, center := he0, source_subset := hes,
    target := het, forward_formula := hef, inverse_formula := heg
  }⟩

end RepulsiveCoulomb
