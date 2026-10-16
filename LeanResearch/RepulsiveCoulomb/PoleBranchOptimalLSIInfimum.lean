import LeanResearch.RepulsiveCoulomb.PoleBranchOptimalLSIRate

/-! RECORDS-ONLY UNCOMPILED. Exact nested infima of the actual optimal LSI
rates. Empty temperature sets have extended-real infimum +infinity. On
nonempty sets the extended infimum equals the coercion of the genuine real
nested infimum. The positive lower bound explicitly consumes a common actual
full-domain LSI rate; no analytic LSI is proved here. -/
noncomputable section
open Set MeasureTheory
open PeriodicAttractiveLogGas
namespace RepulsiveCoulomb

/-- Finite real infima and their extended-real versions agree for a nonempty
family bounded below. This proof remains uncompiled. -/
theorem poleBranch_ereal_iInf_coe_eq_sInf {ι : Type*} [Nonempty ι]
    (f : ι → ℝ) (hb : BddBelow (range f)) :
    (⨅ i, (f i : EReal)) = ((sInf (range f) : ℝ) : EReal) := by
  classical
  let L : EReal := ⨅ i, (f i : EReal)
  obtain ⟨b, hb⟩ := hb
  have hbelow : (b : EReal) ≤ L := by
    apply le_iInf
    intro i
    exact_mod_cast hb (mem_range_self i)
  have hbot : L ≠ ⊥ := ne_of_gt ((show (⊥ : EReal) < (b : EReal) by simp).trans_le hbelow)
  have htop : L ≠ ⊤ := ne_of_lt
    ((iInf_le (fun i => (f i : EReal)) (Classical.arbitrary ι)).trans_lt (by simp))
  have hreal : (L.toReal : EReal) = L := EReal.coe_toReal htop hbot
  apply le_antisymm
  · have hle : L.toReal ≤ sInf (range f) := by
      apply le_csInf (range_nonempty f)
      rintro r ⟨i, rfl⟩
      have hi : L ≤ (f i : EReal) := iInf_le _ i
      rw [← hreal] at hi
      exact_mod_cast hi
    change L ≤ _
    rw [← hreal]
    exact_mod_cast hle
  · apply le_iInf
    intro i
    exact_mod_cast (csInf_le (show BddBelow (range f) from ⟨b, hb⟩) (mem_range_self i))

def poleBranchOptimalLSIParticleValues {β : ℝ} (hβ : 0 < β) : Set ℝ :=
  range (fun N : {N : ℕ // 2 ≤ N} => poleBranchOptimalLSIRate N.val hβ)

def poleBranchOptimalLSIParticleRealInf {β : ℝ} (hβ : 0 < β) : ℝ :=
  sInf (poleBranchOptimalLSIParticleValues hβ)

def poleBranchOptimalLSIParticleInf {β : ℝ} (hβ : 0 < β) : EReal :=
  ⨅ N : {N : ℕ // 2 ≤ N}, (poleBranchOptimalLSIRate N.val hβ : EReal)

theorem poleBranchOptimalLSIParticleValues_nonempty {β : ℝ} (hβ : 0 < β) :
    (poleBranchOptimalLSIParticleValues hβ).Nonempty :=
  ⟨_, ⟨⟨2, le_rfl⟩, rfl⟩⟩

theorem poleBranchOptimalLSIParticleValues_bddBelow {β : ℝ} (hβ : 0 < β) :
    BddBelow (poleBranchOptimalLSIParticleValues hβ) := by
  refine ⟨0, ?_⟩
  rintro r ⟨N, rfl⟩
  exact poleBranchOptimalLSIRate_nonneg N.val N.property hβ

theorem poleBranchOptimalLSIParticleRealInf_nonneg {β : ℝ} (hβ : 0 < β) :
    0 ≤ poleBranchOptimalLSIParticleRealInf hβ := by
  apply le_csInf (poleBranchOptimalLSIParticleValues_nonempty hβ)
  rintro r ⟨N, rfl⟩
  exact poleBranchOptimalLSIRate_nonneg N.val N.property hβ

theorem poleBranchOptimalLSIParticleInf_eq_real {β : ℝ} (hβ : 0 < β) :
    poleBranchOptimalLSIParticleInf hβ = (poleBranchOptimalLSIParticleRealInf hβ : EReal) := by
  letI : Nonempty {N : ℕ // 2 ≤ N} := ⟨⟨2, le_rfl⟩⟩
  exact poleBranch_ereal_iInf_coe_eq_sInf _ (poleBranchOptimalLSIParticleValues_bddBelow hβ)

def poleBranchOptimalLSIInfOn (I : Set ℝ) (hI : I ⊆ Set.Ioi (0 : ℝ)) : EReal :=
  ⨅ β : I, poleBranchOptimalLSIParticleInf (hI β.property)

def poleBranchOptimalLSIRealInfOn (I : Set ℝ) (hI : I ⊆ Set.Ioi (0 : ℝ)) : ℝ :=
  sInf (range (fun β : I => poleBranchOptimalLSIParticleRealInf (hI β.property)))

theorem poleBranchOptimalLSIInfOn_empty (hI : (∅ : Set ℝ) ⊆ Set.Ioi (0 : ℝ)) :
    poleBranchOptimalLSIInfOn ∅ hI = ⊤ := by
  simp [poleBranchOptimalLSIInfOn]

theorem poleBranchOptimalLSIInfOn_eq_real (I : Set ℝ) (hI : I ⊆ Set.Ioi (0 : ℝ))
    (hne : I.Nonempty) :
    poleBranchOptimalLSIInfOn I hI = (poleBranchOptimalLSIRealInfOn I hI : EReal) := by
  letI : Nonempty I := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  have hpos (β : I) : 0 < (β : ℝ) := hI β.property
  change (⨅ β : I, poleBranchOptimalLSIParticleInf (hpos β)) =
    ((sInf (range (fun β : I => poleBranchOptimalLSIParticleRealInf (hpos β))) : ℝ) : EReal)
  calc
    _ = ⨅ β : I, (poleBranchOptimalLSIParticleRealInf (hpos β) : EReal) :=
      iInf_congr (fun β => poleBranchOptimalLSIParticleInf_eq_real (hpos β))
    _ = _ := by
      apply poleBranch_ereal_iInf_coe_eq_sInf
      refine ⟨0, ?_⟩
      rintro r ⟨β, rfl⟩
      exact poleBranchOptimalLSIParticleRealInf_nonneg (hpos β)

/-- A common actual full-domain LSI rate bounds the literal nested optimum
infimum, including the empty-temperature-set convention. -/
theorem poleBranchOptimalLSIInfOn_ge_common_rate (I : Set ℝ) (hI : I ⊆ Set.Ioi (0 : ℝ))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hLSI : ∀ (β : ℝ) (hβ : β ∈ I) (N : ℕ) (hN : 2 ≤ N)
      (u : CoulombFormDomain N (hI hβ)),
      entropy (coulombMeasure N β) (fun z => (coulombFormValueL N (hI hβ) u z) ^ 2) ≤
        (((2 / ρ) * coulombFormEnergy N (hI hβ) u : ℝ) : EReal)) :
    (ρ : EReal) ≤ poleBranchOptimalLSIInfOn I hI := by
  apply le_iInf
  intro β
  apply le_iInf
  intro N
  exact_mod_cast (poleBranch_admissible_le_optimalLSIRate N.property (hI β.property)
    ⟨hρ, hLSI β β.property N.val N.property⟩)

theorem poleBranchOptimalLSIInfOn_pos_of_common_rate (I : Set ℝ)
    (hI : I ⊆ Set.Ioi (0 : ℝ)) {ρ : ℝ} (hρ : 0 < ρ)
    (hLSI : ∀ (β : ℝ) (hβ : β ∈ I) (N : ℕ) (hN : 2 ≤ N)
      (u : CoulombFormDomain N (hI hβ)),
      entropy (coulombMeasure N β) (fun z => (coulombFormValueL N (hI hβ) u z) ^ 2) ≤
        (((2 / ρ) * coulombFormEnergy N (hI hβ) u : ℝ) : EReal)) :
    0 < poleBranchOptimalLSIInfOn I hI :=
  (by exact_mod_cast hρ : (0 : EReal) < (ρ : EReal)).trans_le
    (poleBranchOptimalLSIInfOn_ge_common_rate I hI hρ hLSI)

theorem poleBranchOptimalLSIRealInfOn_pos_of_common_rate (I : Set ℝ)
    (hI : I ⊆ Set.Ioi (0 : ℝ)) (hne : I.Nonempty) {ρ : ℝ} (hρ : 0 < ρ)
    (hLSI : ∀ (β : ℝ) (hβ : β ∈ I) (N : ℕ) (hN : 2 ≤ N)
      (u : CoulombFormDomain N (hI hβ)),
      entropy (coulombMeasure N β) (fun z => (coulombFormValueL N (hI hβ) u z) ^ 2) ≤
        (((2 / ρ) * coulombFormEnergy N (hI hβ) u : ℝ) : EReal)) :
    0 < poleBranchOptimalLSIRealInfOn I hI := by
  have h := poleBranchOptimalLSIInfOn_pos_of_common_rate I hI hρ hLSI
  rw [poleBranchOptimalLSIInfOn_eq_real I hI hne] at h
  exact_mod_cast h

end RepulsiveCoulomb
