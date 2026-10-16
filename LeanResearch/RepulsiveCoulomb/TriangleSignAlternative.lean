module

public import LeanResearch.RepulsiveCoulomb.TriangleLevelSigns

@[expose] public section

/-! Explicit isolated-sign selection for every nonvertex triangular level. -/
noncomputable section
namespace RepulsiveCoulomb

theorem triangle_regular_sign_alternative (u : Fin 3 → ℝ) (t : ℝ)
    (ht : ∀ i, u i ≠ t) :
    (∀ i, u i < t) ∨ (∀ i, t < u i) ∨
      ∃ i : Fin 3,
        ((u i < t ∧ t < u (i + 1)) ∨ (u (i + 1) < t ∧ t < u i)) ∧
        ((u i < t ∧ t < u (i + 2)) ∨ (u (i + 2) < t ∧ t < u i)) := by
  have hgt (i : Fin 3) (h : ¬u i < t) : t < u i :=
    lt_of_le_of_ne (le_of_not_gt h) (Ne.symm (ht i))
  by_cases h0 : u 0 < t <;> by_cases h1 : u 1 < t <;> by_cases h2 : u 2 < t
  · exact Or.inl (fun i => by fin_cases i <;> assumption)
  · refine Or.inr (Or.inr ⟨2, ?_, ?_⟩) <;> norm_num
    · exact Or.inr ⟨h0, hgt 2 h2⟩
    · exact Or.inr ⟨h1, hgt 2 h2⟩
  · refine Or.inr (Or.inr ⟨1, ?_, ?_⟩) <;> norm_num
    · exact Or.inr ⟨h2, hgt 1 h1⟩
    · exact Or.inr ⟨h0, hgt 1 h1⟩
  · refine Or.inr (Or.inr ⟨0, ?_, ?_⟩) <;> norm_num
    · exact Or.inl ⟨h0, hgt 1 h1⟩
    · exact Or.inl ⟨h0, hgt 2 h2⟩
  · refine Or.inr (Or.inr ⟨0, ?_, ?_⟩) <;> norm_num
    · exact Or.inr ⟨h1, hgt 0 h0⟩
    · exact Or.inr ⟨h2, hgt 0 h0⟩
  · refine Or.inr (Or.inr ⟨1, ?_, ?_⟩) <;> norm_num
    · exact Or.inl ⟨h1, hgt 2 h2⟩
    · exact Or.inl ⟨h1, hgt 0 h0⟩
  · refine Or.inr (Or.inr ⟨2, ?_, ?_⟩) <;> norm_num
    · exact Or.inl ⟨h2, hgt 0 h0⟩
    · exact Or.inl ⟨h2, hgt 1 h1⟩
  · exact Or.inr (Or.inl (fun i => by fin_cases i <;> exact hgt _ (by assumption)))

end RepulsiveCoulomb
