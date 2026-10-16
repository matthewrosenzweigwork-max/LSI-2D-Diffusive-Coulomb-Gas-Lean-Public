import LeanResearch.RepulsiveCoulomb.PointActualMarkedDirection
import Mathlib.Data.Finset.Max

/-! ISOLATED SOURCE-ONLY first marked direction and attained finite minimum.
All edge and direction choices are constructed from the actual geometry.
No Lean invocation, staging, or acceptance claim. -/
noncomputable section
open Set
namespace RepulsiveCoulomb

/-- The literal nonempty finite set {h} union all constructed marked directions. -/
def finiteCappedDirectionSet {ι : Type*} [Fintype ι] (χ : ι → ℝ) (h : ℝ) : Finset ℝ := by
  classical
  exact insert h (Finset.univ.image χ)

theorem finiteCappedDirectionSet_nonempty {ι : Type*} [Fintype ι] (χ : ι → ℝ) (h : ℝ) :
    (finiteCappedDirectionSet χ h).Nonempty := by
  classical
  exact Finset.insert_nonempty _ _

/-- This is an actual attained finite minimum, not an infimum over sectors. -/
def finiteCappedDirectionMinimum {ι : Type*} [Fintype ι] (χ : ι → ℝ) (h : ℝ) : ℝ :=
  (finiteCappedDirectionSet χ h).min' (finiteCappedDirectionSet_nonempty χ h)

theorem finiteCappedDirectionMinimum_spec
    {ι : Type*} [Fintype ι] (χ : ι → ℝ) (h : ℝ)
    (hh : 0 < h) (hχ : ∀ i, 0 < χ i) :
    0 < finiteCappedDirectionMinimum χ h ∧
      finiteCappedDirectionMinimum χ h ≤ h ∧
      (∀ i, finiteCappedDirectionMinimum χ h ≤ χ i) ∧
      (finiteCappedDirectionMinimum χ h = h ∨
        ∃ i, χ i = finiteCappedDirectionMinimum χ h) := by
  classical
  let B := finiteCappedDirectionSet χ h
  have hm : finiteCappedDirectionMinimum χ h ∈ B :=
    Finset.min'_mem B (finiteCappedDirectionSet_nonempty χ h)
  have hatt : finiteCappedDirectionMinimum χ h = h ∨
      ∃ i, χ i = finiteCappedDirectionMinimum χ h := by
    rcases Finset.mem_insert.mp hm with he | hi
    · exact Or.inl he
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hi
      exact Or.inr ⟨i, hi⟩
  have hpos : 0 < finiteCappedDirectionMinimum χ h := by
    rcases hatt with he | ⟨i, hi⟩
    · rwa [he]
    · rw [← hi]
      exact hχ i
  refine ⟨hpos, ?_, ?_, hatt⟩
  · exact Finset.min'_le B h (Finset.mem_insert_self _ _)
  · intro i
    apply Finset.min'_le B (χ i)
    exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)

/-- Below the imposed cap, an actual marked index attains the direction.
Among all such indices, an actual distance minimizer exists by finiteness. -/
theorem finiteCappedDirectionMinimum_closest
    {ι : Type*} [Fintype ι] (χ d : ι → ℝ) (h : ℝ)
    (hh : 0 < h) (hχ : ∀ i, 0 < χ i)
    (hlt : finiteCappedDirectionMinimum χ h < h) :
    ∃ i, χ i = finiteCappedDirectionMinimum χ h ∧
      ∀ j, χ j = finiteCappedDirectionMinimum χ h → d i ≤ d j := by
  classical
  have hatt := (finiteCappedDirectionMinimum_spec χ h hh hχ).2.2.2
  obtain ⟨i, hi⟩ := hatt.resolve_left (ne_of_lt hlt)
  let T := Finset.univ.filter (fun j ↦ χ j = finiteCappedDirectionMinimum χ h)
  have hT : T.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩
  obtain ⟨j, hj, hjmin⟩ := T.exists_min_image d hT
  refine ⟨j, (Finset.mem_filter.mp hj).2, ?_⟩
  intro k hk
  exact hjmin k (Finset.mem_filter.mpr ⟨Finset.mem_univ k, hk⟩)

/-- The requested positive finite first direction, constructed from actual
point-region data. S is the actual common finite support of nu and alpha.

The only residual boundary interface is the genuine atom identity at positive
points of the supplied clean boundary ray. It constructs width-pi charts via
cleanliness; it is not a continuation or direction certificate. The generic cap
h is positive and bounded by pi and the actual retained width. -/
theorem exists_point_actual_first_marked_direction
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P : Set ℂ} (hclosed : IsClosed P) (hconn : IsPreconnected P)
    (hcharts : ∀ p ∈ P, ∃ C : PointRetainedConeNeighborhood a y P p,
      C.Full ∨ C.Admissible)
    {ν α : ℂ →₀ ℝ} (hmarks : (↑(pointSignedMarked ν α) : Set ℂ) ⊆ P)
    (ρ : NNReal → ℂ)
    (hρ : ∀ s t, (pointSmoothConformalEDist a y (ρ s) (ρ t)).toReal = dist s t)
    (hρP : ∀ t, ρ t ∈ P) (hfront : ∀ t, ρ t ∈ frontier P)
    (hclean : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ))
    (hboundary : ∀ t : NNReal, 0 < t →
      ∃ D : PointRetainedConeNeighborhood a y P (ρ t),
        ν (ρ t) = Real.pi - D.flatPhysicalWidth)
    (C : PointRetainedConeNeighborhood a y P (ρ 0)) (hadm : C.Admissible)
    {h : ℝ} (hh : 0 < h) (hhpi : h ≤ Real.pi) (hhwidth : h ≤ C.flatPhysicalWidth) :
    let ι := {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)}
    ∃ E : ι → PointGeodesicTreeEdge a y,
      ∃ hE0 : ∀ i, (E i).start = ρ 0,
      ∃ hEP : ∀ i t, (E i).curve t ∈ P,
      (∀ i, (E i).finish = i.1) ∧
      ∃ χ : ι → ℝ,
        (∀ i, χ i = C.actualPhysicalDirection ha y hadm (E i)
          (pointRayComparisonEdge ha y ρ hρ (E i)) (hE0 i) rfl (hEP i) (fun t ↦ hρP _)) ∧
        (∀ i, 0 < χ i ∧ χ i ≤ C.flatPhysicalWidth) ∧
        (∀ i, C.actualInitialRawAngle ha y hadm
          (pointRayComparisonEdge ha y ρ hρ (E i)) rfl (fun t ↦ hρP _) = C.lo ∨
          C.actualInitialRawAngle ha y hadm
            (pointRayComparisonEdge ha y ρ hρ (E i)) rfl (fun t ↦ hρP _) = C.hi) ∧
        ∃ β : ℝ,
          (∃ hι : Fintype ι, β = @finiteCappedDirectionMinimum ι hι χ h) ∧
          0 < β ∧ β ≤ h ∧ β ≤ Real.pi ∧ β ≤ C.flatPhysicalWidth ∧
          (∀ i, β ≤ χ i) ∧
          (β = h ∨ ∃ i, χ i = β) ∧
          (β < h → ∃ i, χ i = β ∧
            ∀ j, χ j = β → pointActualEdgeLength (E i) ≤ pointActualEdgeLength (E j)) := by
  classical
  dsimp only
  let ι := {x : ℂ // x ∈ (pointSignedMarked ν α).erase (ρ 0)}
  letI : Fintype ι := Fintype.ofFinite ι
  have hedge (i : ι) : ∃ E : PointGeodesicTreeEdge a y,
      E.start = ρ 0 ∧ E.finish = i.1 ∧ (∀ t, E.curve t ∈ P) ∧
      ∀ F : PointGeodesicTreeEdge a y,
        F.start = ρ 0 → F.finish = i.1 → E.curve = F.curve := by
    have hi := Finset.mem_erase.mp i.2
    exact exists_retained_actual_edge ha y hclosed hconn hcharts
      (hρP 0) (hmarks hi.2) hi.1.symm
  choose E hE0 hE1 hEP hUnique using hedge
  let χ (i : ι) := C.actualPhysicalDirection ha y hadm (E i)
    (pointRayComparisonEdge ha y ρ hρ (E i)) (hE0 i) rfl (hEP i) (fun t ↦ hρP _)
  have hχpos (i : ι) : 0 < χ i := by
    apply C.actual_marked_direction_pos ha y ρ hρ hρP hadm hclean hboundary
      (E i) (hE0 i) (hEP i)
    rw [hE1 i]
    exact (Finset.mem_erase.mp i.2).2
  have hχwidth (i : ι) : χ i ≤ C.flatPhysicalWidth :=
    (C.actualPhysicalDirection_mem ha y hadm (E i)
      (pointRayComparisonEdge ha y ρ hρ (E i)) (hE0 i) rfl (hEP i) (fun t ↦ hρP _)).2
  refine ⟨E, hE0, hEP, hE1, χ, fun i ↦ rfl,
    fun i ↦ ⟨hχpos i, hχwidth i⟩, ?_, ?_⟩
  · intro i
    exact C.actualInitialRawAngle_frontier_endpoint ha y hadm
      (pointRayComparisonEdge ha y ρ hρ (E i)) rfl (fun t ↦ hρP _)
      (fun t ht ↦ hfront _)
  · let β := finiteCappedDirectionMinimum χ h
    obtain ⟨hβpos, hβh, hβχ, hatt⟩ := finiteCappedDirectionMinimum_spec χ h hh hχpos
    refine ⟨β, ⟨inferInstance, rfl⟩, hβpos, hβh, hβh.trans hhpi,
      hβh.trans hhwidth, hβχ, hatt, ?_⟩
    intro hlt
    exact finiteCappedDirectionMinimum_closest χ (fun i ↦ pointActualEdgeLength (E i))
      h hh hχpos hlt

end RepulsiveCoulomb
