import LeanResearch.RepulsiveCoulomb.PointFiniteActualCutPrefix

/-! SOURCE-ONLY, UNCOMPILED. Geometry and quantitative bounds of the actual
finite prefix, plus exact allocation if its produced endpoint is terminal.
No terminality or disjoint family is assumed by the finite-prefix constructor.
-/
noncomputable section
open Set
namespace RepulsiveCoulomb

def PointActualAllocatedSector.openImage {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
    (S : PointActualAllocatedSector a y) : Set ℂ :=
  S.map '' {x : closedEuclideanSector S.beta | x.1 ∈ interior (closedEuclideanSector S.beta)}

theorem PointActualAllocatedSector.openImage_subset_range
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} (S : PointActualAllocatedSector a y) :
    S.openImage ⊆ range S.map := by
  rintro x ⟨z, _, rfl⟩
  exact mem_range_self z

theorem PointConstructedCutSector.openImage_subset_interior
    {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ} {P : Set ℂ} {ν α : ℂ →₀ ℝ}
    (S : PointConstructedCutSector a y P ν α) : S.allocated.openImage ⊆ interior P := by
  rintro x ⟨z, hz, rfl⟩
  have harg := closedEuclideanSector_interior_strict_arg S.positive S.le_pi hz
  have hz0 : 0 < ‖z.1‖ := norm_pos_iff.mpr (fun he ↦ by
    have hh := harg.1
    rw [he, Complex.arg_zero] at hh
    exact lt_irrefl _ hh)
  exact (S.clean_open z hz0 harg.1 harg.2).1

namespace PointFiniteActualCutPrefix
variable {m : ℕ} {a : Fin m → ℝ} {y : Fin m → ℂ}
  {P : Set ℂ} {ν α : ℂ →₀ ℝ} {K : PointGeometricCutState a y P ν α}

theorem selected_range_subset (T : PointFiniteActualCutPrefix a y K) :
    ∀ S ∈ T.sectors, range S.map ⊆ P := by
  induction T with
  | blocked K hm hc => simp [sectors]
  | terminal K B S hspent =>
      intro E hE
      have he : E = S.allocated := by simpa only [sectors, List.mem_singleton] using hE
      subst E
      rintro x ⟨z, rfl⟩
      exact B.subset_old (S.mem_region z)
  | next K B S O tail ih =>
      intro E hE
      rcases List.mem_cons.mp hE with he | he
      · subst E
        rintro x ⟨z, rfl⟩
        exact B.subset_old (S.mem_region z)
      · exact (ih E he).trans (O.subset_old.trans B.subset_old)

theorem selected_openImage_subset (T : PointFiniteActualCutPrefix a y K) :
    ∀ S ∈ T.sectors, S.openImage ⊆ interior P := by
  induction T with
  | blocked K hm hc => simp [sectors]
  | terminal K B S hspent =>
      intro E hE
      have he : E = S.allocated := by simpa only [sectors, List.mem_singleton] using hE
      subst E
      exact S.openImage_subset_interior.trans (interior_mono B.subset_old)
  | next K B S O tail ih =>
      intro E hE
      rcases List.mem_cons.mp hE with he | he
      · subst E
        exact S.openImage_subset_interior.trans (interior_mono B.subset_old)
      · exact (ih E he).trans (interior_mono (O.subset_old.trans B.subset_old))

/-- Later interiors lie in the actual closed residual's interior and hence
avoid the entire earlier closed sector, not merely its apex or a boundary ray. -/
theorem pairwise_disjoint_openImages (T : PointFiniteActualCutPrefix a y K) :
    T.sectors.Pairwise (fun S E ↦ Disjoint S.openImage E.openImage) := by
  induction T with
  | blocked K hm hc => simp [sectors]
  | terminal K B S hspent => simp [sectors]
  | next K B S O tail ih =>
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih⟩
      intro E hE
      exact O.disjoint_old_sector_new_interior.mono
        S.allocated.openImage_subset_range (tail.selected_openImage_subset E hE)

theorem selected_apex_supported (T : PointFiniteActualCutPrefix a y K) :
    ∀ S ∈ T.sectors, S.apex ∈ α.support := by
  induction T with
  | blocked K hm hc => simp [sectors]
  | terminal K B S hspent =>
      intro E hE
      have he : E = S.allocated := by simpa only [sectors, List.mem_singleton] using hE
      subst E
      exact S.apex_supported
  | next K B S O tail ih =>
      intro E hE
      rcases List.mem_cons.mp hE with he | he
      · subst E
        exact S.apex_supported
      · exact pointCut_spent_budget_support_subset S.positive S.le_budget (ih E he)

/-- Every successful nonterminal step strictly decreases the outer rank.
A final terminal sector costs one additional step; a blocked prefix costs none. -/
theorem length_le_rank_add_one (T : PointFiniteActualCutPrefix a y K) :
    T.sectors.length ≤ pointCutOuterRank P ν α + 1 := by
  induction T with
  | blocked K hm hc => simp [sectors]
  | terminal K B S hspent => simp [sectors]
  | next K B S O tail ih =>
      have hd := O.rank_lt.trans_le B.rank_le
      change tail.sectors.length + 1 ≤ _
      omega

end PointFiniteActualCutPrefix
end RepulsiveCoulomb
