module

public import LeanResearch.RepulsiveCoulomb.PointFullLinePreparationAlgebra
public import LeanResearch.RepulsiveCoulomb.PointMarkedRayClearance
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Set.Finite.Basic

@[expose] public section

/-! SOURCE-ONLY, UNCOMPILED. The finite maximum is taken on the entire new
complete metric top line. The resulting ray is an actual shifted restriction
of that line, with the ambient metric law and genuine new-frontier membership.
The budget apex is positive by old-interior curvature interpretation and
negative-part domination, including budget-only marks. -/
noncomputable section
open Set Topology
open scoped Classical
namespace RepulsiveCoulomb

/-- No clean ray or farthest-clock certificate is an input. -/
theorem pointFullLine_exists_clean_budget_ray
    {m : ℕ} {a : Fin m → ℝ} (ha : ∀ j, 0 ≤ a j) (y : Fin m → ℂ)
    {P Q : Set ℂ} {turn : ℂ → ℝ} {ν α : ℂ →₀ ℝ}
    (hν : PointFullStripCurvatureRepresentation a y P turn ν)
    (hdom : ∀ p, signedBudgetNeg (ν p) ≤ α p)
    (top : ℝ → ℂ)
    (htop : ∀ s t, (pointSmoothConformalEDist a y (top s) (top t)).toReal = dist s t)
    (hfront : range top ⊆ frontier Q) (hinterior : range top ⊆ interior P)
    (hcontact : ∃ t, top t ∈ pointSignedMarked ν α) :
    ∃ s : ℝ, top s ∈ pointSignedMarked ν α ∧ 0 < α (top s) ∧
      (∀ t, top t ∈ pointSignedMarked ν α → t ≤ s) ∧
      let ρ : NNReal → ℂ := fun t ↦ top (s + (t : ℝ))
      ρ 0 = top s ∧
      (∀ u v, (pointSmoothConformalEDist a y (ρ u) (ρ v)).toReal = dist u v) ∧
      IsClosedEmbedding ρ ∧ IsProperMap ρ ∧
      range ρ ⊆ frontier Q ∧ range ρ ⊆ interior P ∧
      (∀ t : NNReal, 0 < t → ρ t ∉ pointSignedMarked ν α) ∧
      (∀ t : NNReal, 0 < t → ν (ρ t) = 0 ∧ α (ρ t) = 0) ∧
      Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ) ∧
      (∀ L ε : ℝ, 0 < L → 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ < L ∧ δ < ε ∧
        ∀ p ∈ (↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}, ∀ t : NNReal,
          δ < (pointSmoothConformalEDist a y p (ρ t)).toReal) := by
  classical
  have hinj : Function.Injective top := by
    intro s t he
    have hd := htop s t
    rw [he, pointSmoothConformalEDist_self, ENNReal.toReal_zero] at hd
    exact dist_eq_zero.mp hd.symm
  let K : Set ℝ := top ⁻¹' (↑(pointSignedMarked ν α) : Set ℂ)
  have hK : K.Finite := (pointSignedMarked ν α).finite_toSet.preimage
    (fun s _ t _ he ↦ hinj he)
  have hKne : K.Nonempty := hcontact
  obtain ⟨s, hs, hmax⟩ := Finset.exists_max_image hK.toFinset id
    (hK.toFinset_nonempty.mpr hKne)
  have hsmark : top s ∈ pointSignedMarked ν α := hK.mem_toFinset.mp hs
  have hsmax : ∀ t, top t ∈ pointSignedMarked ν α → t ≤ s := by
    intro t ht
    exact hmax t (hK.mem_toFinset.mpr ht)
  let ρ : NNReal → ℂ := fun t ↦ top (s + (t : ℝ))
  have hρ0 : ρ 0 = top s := by simp only [ρ, NNReal.coe_zero, add_zero]
  have hρmetric : ∀ u v, (pointSmoothConformalEDist a y (ρ u) (ρ v)).toReal = dist u v := by
    intro u v
    rw [htop]
    change dist (s + (u : ℝ)) (s + (v : ℝ)) = dist (u : ℝ) (v : ℝ)
    exact dist_add_left _ _ _
  have hclosed := pointMetricRay_isClosedEmbedding ha y ρ hρmetric
  have hclean : ∀ t : NNReal, 0 < t → ρ t ∉ pointSignedMarked ν α := by
    intro t ht hm
    have hle := hsmax (s + (t : ℝ)) hm
    have ht' : (0 : ℝ) < t := ht
    linarith
  have hdis : Disjoint ((↑(pointSignedMarked ν α) : Set ℂ) \ {ρ 0}) (range ρ) := by
    apply disjoint_left.mpr
    rintro p ⟨hp, hp0⟩ ⟨t, rfl⟩
    by_cases ht : t = 0
    · exact hp0 (by simp only [ht, mem_singleton_iff])
    · exact hclean t (lt_of_le_of_ne (show (0 : NNReal) ≤ t from zero_le) (Ne.symm ht)) hp
  refine ⟨s, hsmark,
    hν.marked_interior_budget_pos hdom (hinterior (mem_range_self s)) hsmark,
    hsmax, hρ0, hρmetric, hclosed, hclosed.isProperMap, ?_, ?_, hclean, ?_, hdis, ?_⟩
  · rintro p ⟨t, rfl⟩
    exact hfront (mem_range_self (s + (t : ℝ)))
  · rintro p ⟨t, rfl⟩
    exact hinterior (mem_range_self (s + (t : ℝ)))
  · intro t ht
    exact pointSigned_eq_zero_off_marked (hclean t ht)
  · intro L ε hL hε
    exact pointMetricRay_exists_uniform_marked_clearance ha y ρ hρmetric
      (pointSignedMarked ν α).finite_toSet hdis hL hε

end RepulsiveCoulomb
