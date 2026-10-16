import LeanResearch.RepulsiveCoulomb.PoleBranchOptimalSymmetricConstant

/-! RECORDS-ONLY UNCOMPILED. The exact compact-temperature C_sym bound, with
actual interval suprema of optimal Poincare coefficients inside the finite
maximum. Positive admissible witnesses are used only to prove boundedness of
those supremum sets. No symmetric PI or dbar distance estimate is asserted. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory
namespace RepulsiveCoulomb

def poleBranchOptimalPoincareIntervalValues (N : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) : Set ℝ :=
  range (fun β : Set.Icc a b => coulombOptimalPoincare N (ha.trans_le β.property.1))

def poleBranchOptimalPoincareIntervalSup (N : ℕ) {a : ℝ} (ha : 0 < a) (b : ℝ) : ℝ :=
  sSup (poleBranchOptimalPoincareIntervalValues N ha b)

theorem poleBranchOptimalPoincareIntervalValues_nonempty (N : ℕ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : (poleBranchOptimalPoincareIntervalValues N ha b).Nonempty :=
  ⟨_, ⟨⟨a, le_rfl, hab⟩, rfl⟩⟩

theorem poleBranchOptimalPoincareIntervalValues_bddAbove (N : ℕ) (hN : 2 ≤ N) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) : BddAbove (poleBranchOptimalPoincareIntervalValues N ha b) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  obtain ⟨C, hC, hbound⟩ := coulombOptimalPoincare_compact_temperature_bound n ha hab
  refine ⟨C, ?_⟩
  rintro q ⟨β, rfl⟩
  exact hbound β β.property

theorem poleBranchOptimalPoincareIntervalSup_le {N : ℕ} {a b C : ℝ}
    (ha : 0 < a) (hab : a ≤ b)
    (hbound : ∀ β (hβ : β ∈ Set.Icc a b), coulombOptimalPoincare N (ha.trans_le hβ.1) ≤ C) :
    poleBranchOptimalPoincareIntervalSup N ha b ≤ C := by
  apply csSup_le (poleBranchOptimalPoincareIntervalValues_nonempty N ha hab)
  rintro q ⟨β, rfl⟩
  exact hbound β β.property

theorem poleBranchOptimalPoincare_le_intervalSup {N : ℕ} (hN : 2 ≤ N) {a b β : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hβ : β ∈ Set.Icc a b) :
    coulombOptimalPoincare N (ha.trans_le hβ.1) ≤ poleBranchOptimalPoincareIntervalSup N ha b :=
  le_csSup (poleBranchOptimalPoincareIntervalValues_bddAbove N hN ha hab) ⟨⟨β, hβ⟩, rfl⟩

theorem poleBranchOptimalPoincareIntervalSup_bounded (N : ℕ) (hN : 2 ≤ N) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ poleBranchOptimalPoincareIntervalSup N ha b ≤ C := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, N = n + 2 := ⟨N - 2, by omega⟩
  obtain ⟨C, hC, hbound⟩ := coulombOptimalPoincare_compact_temperature_bound n ha hab
  exact ⟨C, hC, poleBranchOptimalPoincareIntervalSup_le ha hab hbound⟩

def poleBranchSymmetricIntervalBound {a : ℝ} (ha : 0 < a) (b : ℝ) : ℝ :=
  if hs : (poleBranchExceptionalParticleCounts b).Nonempty then
    max (1 / a) ((poleBranchExceptionalParticleCounts b).sup' hs
      (fun N => poleBranchOptimalPoincareIntervalSup N ha b))
  else 1 / a

theorem poleBranchSymmetricIntervalBound_one_div_le {a b : ℝ} (ha : 0 < a) :
    1 / a ≤ poleBranchSymmetricIntervalBound ha b := by
  unfold poleBranchSymmetricIntervalBound
  split
  · exact le_max_left _ _
  · exact le_rfl

theorem poleBranchSymmetricIntervalBound_pos {a b : ℝ} (ha : 0 < a) :
    0 < poleBranchSymmetricIntervalBound ha b :=
  (one_div_pos.mpr ha).trans_le (poleBranchSymmetricIntervalBound_one_div_le ha)

theorem poleBranchSymmetricIntervalBound_optimalSup_le {a b : ℝ} (ha : 0 < a)
    (N : ℕ) (hN : N ∈ poleBranchExceptionalParticleCounts b) :
    poleBranchOptimalPoincareIntervalSup N ha b ≤ poleBranchSymmetricIntervalBound ha b := by
  have hs : (poleBranchExceptionalParticleCounts b).Nonempty := ⟨N, hN⟩
  rw [poleBranchSymmetricIntervalBound, dif_pos hs]
  exact (Finset.le_sup' (fun M => poleBranchOptimalPoincareIntervalSup M ha b) hN).trans
    (le_max_right _ _)

/-- The manuscript's exact pointwise interval maximum bound. -/
theorem poleBranchSymmetricPoincareConstant_le_intervalBound {a b β : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hβ : β ∈ Set.Icc a b) :
    poleBranchSymmetricPoincareConstant (ha.trans_le hβ.1) ≤ poleBranchSymmetricIntervalBound ha b := by
  apply poleBranchSymmetricPoincareConstant_le
  · exact (one_div_le_one_div_of_le ha hβ.1).trans (poleBranchSymmetricIntervalBound_one_div_le ha)
  · intro N hN
    have hN2 : 2 ≤ N :=
      ((poleBranchExceptionalParticleCounts_mem (ha.trans_le hβ.1).le N).mp hN).1
    have hNb := poleBranchExceptionalParticleCounts_mono hβ.2 hN
    exact (poleBranchOptimalPoincare_le_intervalSup hN2 ha hab hβ).trans
      (poleBranchSymmetricIntervalBound_optimalSup_le ha N hNb)

def poleBranchSymmetricIntervalValues {a : ℝ} (ha : 0 < a) (b : ℝ) : Set ℝ :=
  range (fun β : Set.Icc a b => poleBranchSymmetricPoincareConstant (ha.trans_le β.property.1))

def poleBranchSymmetricIntervalSup {a : ℝ} (ha : 0 < a) (b : ℝ) : ℝ :=
  sSup (poleBranchSymmetricIntervalValues ha b)

theorem poleBranchSymmetricIntervalValues_nonempty {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (poleBranchSymmetricIntervalValues ha b).Nonempty := ⟨_, ⟨⟨a, le_rfl, hab⟩, rfl⟩⟩

theorem poleBranchSymmetricIntervalValues_bddAbove {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    BddAbove (poleBranchSymmetricIntervalValues ha b) := by
  refine ⟨poleBranchSymmetricIntervalBound ha b, ?_⟩
  rintro C ⟨β, rfl⟩
  exact poleBranchSymmetricPoincareConstant_le_intervalBound ha hab β.property

/-- Literal inequality for the actual interval supremum; every sSup used above
has an explicit nonempty and bounded-above set in the applicable particle range. -/
theorem poleBranchSymmetricIntervalSup_le_exact_max {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    poleBranchSymmetricIntervalSup ha b ≤ poleBranchSymmetricIntervalBound ha b := by
  apply csSup_le (poleBranchSymmetricIntervalValues_nonempty ha hab)
  rintro C ⟨β, rfl⟩
  exact poleBranchSymmetricPoincareConstant_le_intervalBound ha hab β.property

theorem poleBranchSymmetricIntervalSup_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    0 < poleBranchSymmetricIntervalSup ha b := by
  have hmem : poleBranchSymmetricPoincareConstant ha ∈ poleBranchSymmetricIntervalValues ha b :=
    ⟨⟨a, le_rfl, hab⟩, rfl⟩
  exact (poleBranchSymmetricPoincareConstant_pos ha).trans_le
    (le_csSup (poleBranchSymmetricIntervalValues_bddAbove ha hab) hmem)

theorem poleBranchSymmetricPoincareConstant_compact_bounded {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    ∃ C : ℝ, 0 < C ∧ ∀ β (hβ : β ∈ Set.Icc a b),
      poleBranchSymmetricPoincareConstant (ha.trans_le hβ.1) ≤ C :=
  ⟨poleBranchSymmetricIntervalBound ha b, poleBranchSymmetricIntervalBound_pos ha,
    fun β hβ => poleBranchSymmetricPoincareConstant_le_intervalBound ha hab hβ⟩


theorem poleBranchSymmetricIntervalSup_le_max {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hs : (poleBranchExceptionalParticleCounts b).Nonempty) :
    poleBranchSymmetricIntervalSup ha b ≤
      max (1 / a) ((poleBranchExceptionalParticleCounts b).sup' hs
        (fun N => poleBranchOptimalPoincareIntervalSup N ha b)) := by
  have h := poleBranchSymmetricIntervalSup_le_exact_max ha hab
  simpa only [poleBranchSymmetricIntervalBound, dif_pos hs] using h

theorem poleBranchSymmetricIntervalSup_le_inverse_of_empty {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hs : ¬(poleBranchExceptionalParticleCounts b).Nonempty) :
    poleBranchSymmetricIntervalSup ha b ≤ 1 / a := by
  have h := poleBranchSymmetricIntervalSup_le_exact_max ha hab
  simpa only [poleBranchSymmetricIntervalBound, dif_neg hs] using h

end RepulsiveCoulomb
