import LeanResearch.RepulsiveCoulomb.PointTranslatedFiniteWidthLimit
import LeanResearch.RepulsiveCoulomb.PointTranslatedStripWidthBound

/-! SOURCE-ONLY, UNCOMPILED. Original genuine corner data produce a finite,
positive supremal width and its actual closed isometric limiting strip. The
boundedness premise is discharged geometrically: an unbounded compatible union
is closed and relatively open, so exhausts P, contradicting a positive-budget
point avoided by every actual regular stage. No family, width bound, excluded
point or completion map is supplied by the caller. Attained NEW marked contact
and strict residual-angle positivity remain the next geometric obligations. -/
noncomputable section
open Set Metric Topology
namespace RepulsiveCoulomb.PointTranslatedRegularData
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {ha : ∀ j, 0 ≤ a j}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} (D : PointTranslatedRegularData a y ha P ν α)

/-- The excluded point is constructed from the positive total allocation. -/
theorem exists_excluded_budget_point : ∃ q : P, α q.1 ≠ 0 ∧
    ∀ {s : ℝ} (T : D.Stage s), q.1 ∉ range (fun z ↦ (T.map z).1) := by
  classical
  have hα : ∃ x : ℂ, α x ≠ 0 := by
    by_contra hn
    push_neg at hn
    have he : α = 0 := Finsupp.ext hn
    have hz : pointSignedBudgetMass ν α = 0 := by simp [pointSignedBudgetMass, he]
    have hp := D.budget.budget_pos
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  obtain ⟨x, hx⟩ := hα
  refine ⟨⟨x, D.allocation_support x hx⟩, hx, ?_⟩
  intro s T
  rintro ⟨z, hz⟩
  have hxp : x ≠ (D.ray 0).1 := fun he ↦ hx (he.symm ▸ D.apex_budget_zero)
  have hmarked : x ∈ pointSignedMarked ν α := (mem_pointSignedMarked ν α x).mpr (Or.inr hx)
  change (T.map z).1 = x at hz
  apply T.unmarked z
  rw [hz]
  exact ⟨hmarked, hxp⟩

/-- The width set defined by original geometry is actually bounded. -/
theorem regularWidths_bddAbove : BddAbove D.regularWidths := by
  classical
  let M := pointRegionMetricSpace ha y P
  letI : MetricSpace P := M
  letI : PseudoMetricSpace P := M.toPseudoMetricSpace
  letI : PseudoEMetricSpace P := M.toPseudoEMetricSpace
  let T : ∀ s : D.regularWidths, D.Stage s.1 := fun s ↦ Classical.choice s.2
  let f := fun s : D.regularWidths ↦ (T s).map
  have hcompat : ∀ s t : D.regularWidths,
      ∀ z (hs : z ∈ flatShearedStrip (conePhase D.angle) s.1)
        (ht : z ∈ flatShearedStrip (conePhase D.angle) t.1), f s ⟨z, hs⟩ = f t ⟨z, ht⟩ := by
    intro s t z hs ht
    rcases le_total s.1 t.1 with hst | hts
    · exact D.stages_agree (T s) (T t) hst ⟨z, hs⟩
    · exact (D.stages_agree (T t) (T s) hts ⟨z, ht⟩).symm
  obtain ⟨q, hqα, hq⟩ := D.exists_excluded_budget_point
  apply pointTranslatedRegularWidths_bddAbove ha y D.connected.isPreconnected
    D.angle_pos D.angle_lt_pi D.regularWidths_positive f
    (fun s x z ↦ (T s).metric.dist_eq x z) hcompat
    (fun s ↦ (T s).exact_contact) ?_ ?_ q (fun s ↦ hq (T s))
  · intro p hp
    obtain ⟨C, hC, _⟩ := D.boundary_coeff p hp
    exact ⟨C, hC⟩
  · intro s p hp hmem
    obtain ⟨z, hz⟩ := hmem.1
    have hpne : p ≠ (D.ray 0).1 := fun he ↦ (D.ray_frontier 0).2 (he ▸ hp)
    have hm : p ∉ pointSignedMarked ν α := by
      intro hm
      change ((T s).map z).1 = p at hz
      apply (T s).unmarked z
      rw [hz]
      exact ⟨hm, hpne⟩
    by_contra hn
    exact hm (D.interior_marked p hp hn)

/-- Actual source-only finite maximal WIDTH construction from original data.
The word maximal refers to the supremum of regular widths, and does not silently
assert that the limiting top already has a marked point or admissible residual. -/
theorem construct_finite_maximal_width : Nonempty D.FiniteWidthLimit :=
  D.exists_finite_width_limit D.regularWidths_bddAbove

end RepulsiveCoulomb.PointTranslatedRegularData
